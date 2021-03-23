using JuMP


function model2latex(model::Model, var_names::Vector{String}=Vector{String}([]))
    nb_variables = num_variables(model)
    if isempty(var_names)
        for i in 1:nb_variables
            push!(var_names, "x_{$i}")
        end
    end

    tex_str = ""
    all_variables_vec = all_variables(model)
    tex_str *= "\\begin{equation*}\n\\begin{array}{rc"
    for _ in 1:nb_variables
        tex_str *= "c" #1 for each variable
    end
    tex_str *= "cc}\n" #1 for cst_sense + 1 for rhs

    if objective_sense(model) == MOI.MIN_SENSE
        tex_str *= "\\min"
    elseif objective_sense(model) == MOI.MAX_SENSE
        tex_str *= "\\max"
    else
        error(objective_sense(model))
    end
    tex_str *= "\\ z & = & "
    firstobjcoeff = true
    for i in 1:nb_variables
        variable = all_variables_vec[i]
        coeff = get(objective_function(model).terms, variable, 0.0)
        if coeff != 0
            if firstobjcoeff
                firstobjcoeff = false
            elseif coeff > 0
                tex_str *= "+ "
            end
            tex_str *= "$(abs(coeff) == 1 ? (coeff == -1 ? "- " : "") : (coeff == round(coeff)) ? "$(round(Int, coeff)) " : "$coeff ")$(var_names[i]) & "
        else
            tex_str *= "& "
        end
    end
    tex_str *= "& \\\\\n"

    all_constraints_vec = Vector{Tuple{Any, Any, Int}}()
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        for con in all_constraints(model, F, S)
            push!(all_constraints_vec, (con, S, con.index.value))
        end
    end
    sort!(all_constraints_vec, by=x->x[3])

    firstcst = true
    for (con, S, _) in all_constraints_vec
        tex_str *= "& "
        if firstcst
            firstcst = false
            tex_str *= "\\text{s.c.} "
        end
        tex_str *= "& "
        firstobjcoeff = true
        for i in 1:nb_variables
            variable = all_variables_vec[i]
            coeff = normalized_coefficient(con, variable)
            if coeff != 0
                if firstobjcoeff
                    firstobjcoeff = false
                elseif coeff > 0
                    tex_str *= "+ "
                end
                tex_str *= "$(abs(coeff) == 1 ? (coeff == -1 ? "- " : "") : (coeff == round(coeff)) ? "$(round(Int, coeff)) " : "$coeff ")$(var_names[i]) & "
            else
                tex_str *= "& "
            end
        end
        if S == MOI.LessThan{Float64}
            tex_str *= "\\leq "
        elseif S == MOI.GreaterThan{Float64}
            tex_str *= "\\geq "
        elseif S == MOI.EqualTo{Float64}
            tex_str *= "= "
        else
            error()
        end
        tex_str *= "& "
        tex_str *= "$(normalized_rhs(con) == round(normalized_rhs(con)) ? "$(round(Int, normalized_rhs(con)))" : "$(normalized_rhs(con))") "
        tex_str *= "\\\\\n"
    end

    tex_str *= "& & "
    for i in 1:(nb_variables-1)
        tex_str *= "$(var_names[i]), & "
    end
    tex_str *= "$(var_names[end]) & \\geq & 0"
    tex_str *= "\n\\end{array}\n\\end{equation*}"

    return tex_str
end


function min2max!(model::Model)
    @assert objective_sense(model) == MOI.MIN_SENSE

    set_objective_sense(model, MOI.MAX_SENSE)
    for variable in all_variables(model)
        set_objective_coefficient(model, variable, -get(objective_function(model).terms, variable, 0.0))
    end

    return model
end


function rhs2pos!(model::Model)
    all_constraints_rhs_vec = Vector{Bool}()
    all_variables_vec = all_variables(model)
    all_constraints_vec = Vector{Tuple{Any, Any, Int}}()
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        for con in all_constraints(model, F, S)
            push!(all_constraints_vec, (con, S, con.index.value))
        end
    end
    sort!(all_constraints_vec, by=x->x[3])

    for (con, S, _) in all_constraints_vec
        push!(all_constraints_rhs_vec, false)
        if normalized_rhs(con) < 0
            set_normalized_rhs(con, -normalized_rhs(con))
            all_constraints_rhs_vec[end] = true
            for variable in all_variables(model)
                set_normalized_coefficient(con, variable, -normalized_coefficient(con, variable))
            end
        end
    end

    if true in all_constraints_rhs_vec
        for i in 1:length(all_constraints_vec)
            con = all_constraints_vec[i][1]
            S = all_constraints_vec[i][2]
            c = [normalized_coefficient(con, variable) for variable in all_variables_vec]
            rhs = normalized_rhs(con)
            delete(model, con)
            if S == MOI.LessThan{Float64}
                if all_constraints_rhs_vec[i]
                    @constraint(model, c' * all_variables_vec >= rhs)
                else
                    @constraint(model, c' * all_variables_vec <= rhs)
                end
            elseif S == MOI.GreaterThan{Float64}
                if all_constraints_rhs_vec[i]
                    @constraint(model, c' * all_variables_vec <= rhs)
                else
                    @constraint(model, c' * all_variables_vec >= rhs)
                end
            elseif S == MOI.EqualTo{Float64}
                @constraint(model, c' * all_variables_vec == rhs)
            else
                error()
            end
        end
    end

    return model
end


function add_slack_variables!(model::Model)
    all_constraints_vec = Vector{Tuple{Any, Any, Int}}()
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        for con in all_constraints(model, F, S)
            push!(all_constraints_vec, (con, S, con.index.value))
        end
    end
    sort!(all_constraints_vec, by=x->x[3])

    for (con, S, _) in all_constraints_vec
        if S == MOI.LessThan{Float64}
            x = @variable(model, lower_bound=0.0)
            set_normalized_coefficient(con, x, 1.0)
        elseif S == MOI.GreaterThan{Float64}
            x = @variable(model, lower_bound=0.0)
            set_normalized_coefficient(con, x, -1.0)
        elseif S == MOI.EqualTo{Float64}
            @variable(model, lower_bound=0.0)
        else
            error()
        end
    end

    all_variables_vec = all_variables(model)
    for i in 1:length(all_constraints_vec)
        con = all_constraints_vec[i][1]
        c = [normalized_coefficient(con, variable) for variable in all_variables_vec]
        rhs = normalized_rhs(con)
        delete(model, con)
        @constraint(model, c' * all_variables_vec == rhs)
    end

    return model
end



function add_artificial_variables!(model::Model)
    all_variables_vec = all_variables(model)
    all_constraints_vec = Vector{Tuple{Any, Any, Int}}()
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        for con in all_constraints(model, F, S)
            push!(all_constraints_vec, (con, S, con.index.value))
        end
    end
    sort!(all_constraints_vec, by=x->x[3])

    nb_constraints = length(all_constraints_vec)
    for i in 1:nb_constraints
        con = all_constraints_vec[i][1]
        x = @variable(model, lower_bound=0.0)
        if normalized_coefficient(con, all_variables_vec[end-nb_constraints+i]) != 1.0
            set_normalized_coefficient(con, x, 1.0)
        end
    end

    return model
end



mutable struct RationalSimplex
    simplex_array::Matrix{Rational{Int}}
    artificial_objective::Vector{Rational{Int}}
    artificial_objective_value::Rational{Int}
    reduce_costs::Vector{Rational{Int}}
    dual_costs::Vector{Rational{Int}}
    objective_value::Rational{Int}
    basis_variables::Vector{Int}
    artificial_variables::Vector{Int}
    variable_names::Vector{String}
end

function get_nb_constraints(simplex::RationalSimplex)
    return size(simplex.simplex_array)[1]
end

function get_nb_variables(simplex::RationalSimplex)
    return size(simplex.simplex_array)[2]
end

function get_array(simplex::RationalSimplex)
    return simplex.simplex_array
end

function get_objective_value(simplex::RationalSimplex)
    return simplex.objective_value
end

function set_objective_value!(simplex::RationalSimplex, value::Rational{Int})
    simplex.objective_value = value
    return simplex
end

function get_var_names(simplex::RationalSimplex)
    return simplex.variable_names
end

function get_objective_coefficients(simplex::RationalSimplex)
    return simplex.reduce_costs
end

function set_objective_coefficient_value!(simplex::RationalSimplex, i::Int, value::Rational{Int})
    simplex.reduce_costs[i] = value
    return simplex
end

function get_artificial_objective(simplex::RationalSimplex)
    return simplex.artificial_objective
end

function get_rhs(simplex::RationalSimplex)
    return simplex.dual_costs
end

function set_rhs_value!(simplex::RationalSimplex, i::Int, value::Rational{Int})
    simplex.dual_costs[i] = value
    return simplex
end

function get_artificial_variables(simplex::RationalSimplex)
    return simplex.artificial_variables
end

function get_basis_variables(simplex::RationalSimplex)
    return simplex.basis_variables
end

function set_basis_variables!(simplex::RationalSimplex, i::Int, variable::Int)
    simplex.basis_variables[i] = variable
    return simplex
end

function set_coefficient_array!(simplex::RationalSimplex, i::Int, j::Int, value::Rational{Int})
    simplex.simplex_array[i,j] = value
    return simplex
end

function set_artificial_objective_coefficient!(simplex::RationalSimplex, i::Int, value::Rational{Int})
    simplex.artificial_objective[i] = value
    return simplex
end

function get_artificial_objective_coefficient(simplex::RationalSimplex, i::Int)
    return simplex.artificial_objective[i]
end


function get_artificial_objective_value(simplex::RationalSimplex)
    return simplex.artificial_objective_value
end

function set_artificial_objective_value!(simplex::RationalSimplex, value::Rational{Int})
    simplex.artificial_objective_value = value
    return simplex
end


function rational2tex(x::Rational{Int}; in_math=false)
    return "$(!in_math ? "\$" : "")$(denominator(x) != 1 ? "$(sign(numerator(x)) == -1 ? "-" : "")\\frac{$(abs(numerator(x)))}{$(denominator(x))}" : numerator(x))$(!in_math ? "\$" : "")"
end


function simplex2latex(simplex::RationalSimplex)
    tex_str = ""
    (nb_constraints, nb_variables) = size(get_array(simplex))
    tex_str *= "\\begin{center}\n\\begin{tabular}{c|$("c"^nb_variables)|c}\n"

    tex_str *= "& "
    for var_name in get_var_names(simplex)
        tex_str *= "\$$(var_name)\$ & "
    end
    tex_str *= "\\\\\n\\cmidrule(lr){2-$(nb_variables+1)}\n"

    if !isempty(get_artificial_variables(simplex))
        tex_str *= "\$c_a\$ & "
        for coeff in get_artificial_objective(simplex)
            tex_str *= "$(rational2tex(coeff)) & "
        end
        tex_str *= "$(rational2tex(get_artificial_objective_value(simplex))) \\\\\n\\hline\n"
    end

    tex_str *= "\$c\$ & "
    for coeff in get_objective_coefficients(simplex)
        tex_str *= "$(rational2tex(coeff)) & "
    end
    tex_str *= "$(rational2tex(get_objective_value(simplex))) \\\\\n\\hline\n"

    array_simplex = get_array(simplex)
    for i in 1:nb_constraints
        tex_str *= "\$$(get_var_names(simplex)[get_basis_variables(simplex)[i]])\$ & "
        for j in 1:nb_variables
            tex_str *= "$(rational2tex(get_array(simplex)[i,j])) & "
        end
        tex_str *= "$(rational2tex(get_rhs(simplex)[i])) \\\\\n"
    end

    tex_str *= "\\end{tabular}\n\\end{center}"

    return tex_str
end





function model2simplex(model::Model, init_var_names::Vector{String})
    init_all_variables_vec = all_variables(model)
    all_constraints_vec = Vector{Tuple{Any, Any, Int}}()
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        for con in all_constraints(model, F, S)
            push!(all_constraints_vec, (con, S, con.index.value))
        end
    end
    sort!(all_constraints_vec, by=x->x[3])

    nb_constraints = length(all_constraints_vec)
    all_variables_vec = Vector{VariableRef}()
    var_names = Vector{String}()
    for i in 1:length(init_all_variables_vec)
        variable = init_all_variables_vec[i]
        useless_variable = true
        for (con, S, _) in all_constraints_vec
            if normalized_coefficient(con, variable) != 0
                useless_variable = false
                break
            end
        end
        if get(objective_function(model).terms, variable, 0.0) != 0
            useless_variable = false
        end
        if !useless_variable
            push!(all_variables_vec, variable)
            push!(var_names, init_var_names[i])
        end
    end
    nb_variables = length(all_variables_vec)

    basis_variables = Vector{Int}()
    artificial_variables = Vector{Int}()

    for i in 1:nb_constraints
        con = all_constraints_vec[i][1]
        last_variable = 0
        for j in 1:nb_variables
            if normalized_coefficient(con, all_variables_vec[j]) == 1.0
                last_variable = j
            end
        end
        push!(basis_variables, last_variable)
        if last_variable >= length(init_all_variables_vec)-nb_constraints
            push!(artificial_variables, last_variable)
        end
    end

    simplex = RationalSimplex(
        zeros(Rational{Int}, nb_constraints, nb_variables),
        zeros(Rational{Int}, nb_variables),
        zero(Rational{Int}),
        Vector{Rational{Int}}([rationalize(get(objective_function(model).terms, variable, 0.0)) for variable in all_variables_vec]),
        Vector{Rational{Int}}([normalized_rhs(con) for (con, S, _) in all_constraints_vec]),
        rationalize(-objective_function(model).constant),
        basis_variables,
        artificial_variables,
        var_names
    )

    for i in 1:nb_constraints
        con = all_constraints_vec[i][1]
        last_variable = 0
        for j in 1:nb_variables
            set_coefficient_array!(simplex, i, j, rationalize(normalized_coefficient(con, all_variables_vec[j])))
        end
    end
    for variable in artificial_variables
        set_artificial_objective_coefficient!(simplex, variable, 1//1)
    end

    return simplex
end


function repair_simplex!(simplex::RationalSimplex)
    nb_variables = get_nb_variables(simplex)
    nb_constraints = get_nb_constraints(simplex)
    for i in 1:nb_constraints
        if get_basis_variables(simplex)[i] in get_artificial_variables(simplex)
            for j in 1:nb_variables
                set_artificial_objective_coefficient!(simplex, j, get_artificial_objective_coefficient(simplex, j) - get_array(simplex)[i,j])
            end
            set_artificial_objective_value!(simplex, get_artificial_objective_value(simplex) - get_rhs(simplex)[i])
        end
    end

    return simplex
end




function find_entering_variable(simplex::RationalSimplex)
    nb_variables = get_nb_variables(simplex)
    vect_objective = get_artificial_objective(simplex)
    minus = -1
    if !(false in (vect_objective .== 0))
        vect_objective = get_objective_coefficients(simplex)
        minus = 1
    end
    for j in 1:nb_variables
        if minus*vect_objective[j] > 0
            return j
        end
    end

    return 0
end



function find_leaving_variable_candidates(simplex::RationalSimplex, variable_entering::Int)
    possible_leaving_variables = Vector{Int}()
    minimum_value = Inf
    nb_constraints = get_nb_constraints(simplex)
    for i in 1:nb_constraints
        if get_array(simplex)[i, variable_entering] <= 0
            continue
        end
        if get_rhs(simplex)[i]//get_array(simplex)[i, variable_entering] <= minimum_value
            if get_rhs(simplex)[i]//get_array(simplex)[i, variable_entering] != minimum_value
                possible_leaving_variables = Vector{Int}()
            end
            push!(possible_leaving_variables, get_basis_variables(simplex)[i])
            minimum_value = get_rhs(simplex)[i]//get_array(simplex)[i, variable_entering]
        end
    end

    return possible_leaving_variables
end


function get_constraint_for_leaving_variable(simplex::RationalSimplex, variable_leaving::Int)
    nb_constraints = get_nb_constraints(simplex)
    for i in 1:nb_constraints
        if variable_leaving == get_basis_variables(simplex)[i]
            return i
        end
    end
    error("Leaving variable is not in basis.")
end


function normalize_simplex!(simplex::RationalSimplex, variable_entering::Int, variable_leaving::Int)
    i = get_constraint_for_leaving_variable(simplex, variable_leaving)
    nb_variables = get_nb_variables(simplex)
    coeff = get_array(simplex)[i, variable_entering]
    for j in 1:nb_variables
        set_coefficient_array!(simplex, i, j, get_array(simplex)[i, j]//coeff)
    end
    set_rhs_value!(simplex, i, get_rhs(simplex)[i]//coeff)

    return simplex
end



function artificial_pivot!(simplex::RationalSimplex, variable_entering::Int, variable_leaving::Int)
    constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
    nb_variables = get_nb_variables(simplex)
    coeff = get_artificial_objective_coefficient(simplex, variable_entering)
    for j in 1:nb_variables
        set_artificial_objective_coefficient!(simplex, j, get_artificial_objective_coefficient(simplex, j) - coeff*get_array(simplex)[constraint_i,j])
    end
    set_artificial_objective_value!(simplex, get_artificial_objective_value(simplex) - coeff*get_rhs(simplex)[constraint_i])

    simplex_pivot!(simplex, variable_entering, variable_leaving)

    return simplex
end


function simplex_pivot!(simplex::RationalSimplex, variable_entering::Int, variable_leaving::Int)
    constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
    nb_variables = get_nb_variables(simplex)
    coeff = get_objective_coefficients(simplex)[variable_entering]
    for j in 1:nb_variables
        set_objective_coefficient_value!(simplex, j, get_objective_coefficients(simplex)[j] - coeff*get_array(simplex)[constraint_i,j])
    end
    set_objective_value!(simplex, get_objective_value(simplex) - coeff*get_rhs(simplex)[constraint_i])

    nb_constraints = get_nb_constraints(simplex)
    for i in 1:nb_constraints
        if i != constraint_i
            coeff = get_array(simplex)[i,variable_entering]
            for j in 1:nb_variables
                set_coefficient_array!(simplex, i, j, get_array(simplex)[i,j] - coeff*get_array(simplex)[constraint_i,j])
            end
            set_rhs_value!(simplex, i, get_rhs(simplex)[i] - coeff*get_rhs(simplex)[constraint_i])
        end
    end

    set_basis_variables!(simplex, constraint_i, variable_entering)

    return simplex
end


function remove_artificials!(simplex::RationalSimplex)
    artificial_variables = get_artificial_variables(simplex)
    basis_variables = get_basis_variables(simplex)
    for variable in artificial_variables
        if variable in basis_variables
            error("Something went wrong.")
        end
    end

    simplex.reduce_costs = simplex.reduce_costs[1:(end-length(artificial_variables))]
    simplex.variable_names = simplex.variable_names[1:(end-length(artificial_variables))]
    simplex.simplex_array = simplex.simplex_array[1:end, 1:(end-length(artificial_variables))]
    simplex.artificial_variables = Vector{Int}()
    simplex.artificial_objective = zeros(length(simplex.variable_names))
    simplex.artificial_objective_value = zero(Rational{Int})

    return simplex
end



function solve_with_simplex(init_model::Model)
    model = copy(init_model)
    var_names = Vector{String}()
    nb_variables = length(all_variables(model))
    for i in 1:nb_variables
        push!(var_names, "x_{$i}")
    end
    nb_constraints = 0
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        nb_constraints += length(all_constraints(model, F, S))
    end

    tex_str = ""

    tex_str *= model2latex(model, var_names)

    if objective_sense(model) == MOI.MIN_SENSE
        min2max!(model)
        tex_str *= "\n\nObjective function from \$\\min\$ to \$\\max\$\n\n"
        tex_str *= model2latex(model, var_names)
    end

    rhsneg = false
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        for con in all_constraints(model, F, S)
            if normalized_rhs(con) < 0
                rhsneg = true
            end
        end
    end

    if rhsneg
        rhs2pos!(model)
        tex_str *= "\n\nPositive right hand sides\n\n"
        tex_str *= model2latex(model, var_names)
    end

    tex_str *= "\n\nAdd slack variables\n\n"
    add_slack_variables!(model)
    for i in 1:nb_constraints
        push!(var_names, "\\textcolor{blue}{e_{$i}}")
    end
    tex_str *= model2latex(model, var_names)

    tex_str *= "\n\nAdd artificial variables\n\n"
    add_artificial_variables!(model)
    for i in 1:nb_constraints
        push!(var_names, "\\textcolor{red}{v_{$i}}")
    end
    tex_str *= model2latex(model, var_names)

    tex_str *= "\n\nModel to simplex table\n\n"
    simplex = model2simplex(model, var_names)
    tex_str *= simplex2latex(simplex)

    if !isempty(get_artificial_variables(simplex))
        tex_str *= "\n\nRepair simplex table\n\n"
        repair_simplex!(simplex)
        tex_str *= simplex2latex(simplex)

        while true in (get_artificial_objective(simplex) .< 0)
            variable_leaving = 0
            variable_entering = find_entering_variable(simplex)
            tex_str *= "\n\nEntering variable: \$$(get_var_names(simplex)[variable_entering])\$"
            possible_leaving_variables = find_leaving_variable_candidates(simplex, variable_entering)
            if isempty(possible_leaving_variables)
                tex_str *= "\n\nNo leaving variable."
                return tex_str
            elseif length(possible_leaving_variables) >= 2
                tex_str *= "\n\nMultiple possible leaving variables. Not handled yet."
                return tex_str
            end
            variable_leaving = possible_leaving_variables[1]
            constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
            tex_str *= " \\quad -- \\quad Leaving variable: \$$(get_var_names(simplex)[variable_leaving])\$\n\n"
            if get_array(simplex)[constraint_i, variable_entering] != 1
                tex_str *= "\\begin{align*}\n"
                tex_str *= "& L_{$(constraint_i)} \\leftarrow $(rational2tex(1//(get_array(simplex)[constraint_i, variable_entering]), in_math=true))L_{$(constraint_i)} \\\\\n"
                tex_str *= "\\end{align*}\n\n"
                normalize_simplex!(simplex, variable_entering, variable_leaving)
                tex_str *= simplex2latex(simplex)
            end

            tex_str *= "\\begin{align*}\n"
            nb_constraints = get_nb_constraints(simplex)
            coeff = get_artificial_objective(simplex)[variable_entering]
            tex_str *= "& L_{c_{a}} \\leftarrow L_{c_{a}}"
            if coeff != 0
                tex_str *= " $(coeff < 0 ? "+ " : "- ")$(abs(coeff) != 1 ? "$(rational2tex(abs(coeff), in_math=true))" : "")L_{$(constraint_i)}"
            end
            tex_str *= "\\\\\n"
            coeff = get_objective_coefficients(simplex)[variable_entering]
            tex_str *= "& L_{c} \\leftarrow L_{c}"
            if coeff != 0
                tex_str *= " $(coeff < 0 ? "+ " : "- ")$(abs(coeff) != 1 ? "$(rational2tex(abs(coeff), in_math=true))" : "")L_{$(constraint_i)}"
            end
            for i in 1:nb_constraints
                if i != constraint_i
                    coeff = get_array(simplex)[i,variable_entering]
                    tex_str *= " \\\\\n& L_{$i} \\leftarrow L_{$i}"
                    if coeff != 0
                        tex_str *= " $(coeff < 0 ? "+ " : "- ")$(abs(coeff) != 1 ? "$(rational2tex(abs(coeff), in_math=true))" : "")L_{$(constraint_i)}"
                    end
                end
            end
            tex_str *= "\n\\end{align*}\n\n"
            artificial_pivot!(simplex, variable_entering, variable_leaving)
            tex_str *= simplex2latex(simplex)
        end
        tex_str *= "\n\nRemove artificial variables\n\n"
        remove_artificials!(simplex)
        tex_str *= simplex2latex(simplex)
    end

    while true in (get_objective_coefficients(simplex) .> 0)
        variable_leaving = 0
        variable_entering = find_entering_variable(simplex)
        tex_str *= "\n\nEntering variable: \$$(get_var_names(simplex)[variable_entering])\$"
        possible_leaving_variables = find_leaving_variable_candidates(simplex, variable_entering)
        if isempty(possible_leaving_variables)
            tex_str *= "\n\nNo leaving variable."
            return tex_str
        elseif length(possible_leaving_variables) >= 2
            tex_str *= "\n\nMultiple possible leaving variables -- Uses Bland's rule.\n\n"
            tex_str *= "Entering variable: \$$(get_var_names(simplex)[variable_entering])\$"
            sort!(possible_leaving_variables)
        end
        variable_leaving = possible_leaving_variables[1]
        constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
        tex_str *= " \\quad -- \\quad Leaving variable: \$$(get_var_names(simplex)[variable_leaving])\$\n\n"
        if get_array(simplex)[constraint_i, variable_entering] != 1
            tex_str *= "\\begin{align*}\n"
            tex_str *= "& L_{$(constraint_i)} \\leftarrow $(rational2tex(1//(get_array(simplex)[constraint_i, variable_entering]), in_math=true))L_{$(constraint_i)} \\\\\n"
            tex_str *= "\\end{align*}\n\n"
            normalize_simplex!(simplex, variable_entering, variable_leaving)
            tex_str *= simplex2latex(simplex)
        end

        tex_str *= "\\begin{align*}\n"
        nb_constraints = get_nb_constraints(simplex)
        coeff = get_objective_coefficients(simplex)[variable_entering]
        tex_str *= "& L_{c} \\leftarrow L_{c}"
        if coeff != 0
            tex_str *= " $(coeff < 0 ? "+ " : "- ")$(abs(coeff) != 1 ? "$(rational2tex(abs(coeff), in_math=true))" : "")L_{$(constraint_i)}"
        end
        for i in 1:nb_constraints
            if i != constraint_i
                coeff = get_array(simplex)[i,variable_entering]
                tex_str *= " \\\\\n& L_{$i} \\leftarrow L_{$i}"
                if coeff != 0
                    tex_str *= " $(coeff < 0 ? "+ " : "- ")$(abs(coeff) != 1 ? "$(rational2tex(abs(coeff), in_math=true))" : "")L_{$(constraint_i)}"
                end
            end
        end
        tex_str *= "\n\\end{align*}\n\n"
        simplex_pivot!(simplex, variable_entering, variable_leaving)
        tex_str *= simplex2latex(simplex)
    end

    return tex_str
end





function main()
    model = Model()
    @variable(model, x_1 >= 0)
    @variable(model, x_2 >= 0)
    @objective(model, Min, -2x_1 - x_2)
    @constraint(model, x_1 - x_2 >= -2)
    @constraint(model, -x_1 - x_2 >= -6)
    @constraint(model, 2x_1 >= 4)

    println(solve_with_simplex(model))
    return nothing
end