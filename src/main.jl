using JuMP


function model2latex(model::Model)
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

    init_all_variables_vec = all_variables(model)
    all_variables_vec = Vector{VariableRef}()

    for variable in init_all_variables_vec
        if get(objective_function(model).terms, variable, 0.0) != 0.0
            push!(all_variables_vec, variable)
            continue
        end
        for (con, S, _) in all_constraints_vec
            if normalized_coefficient(con, variable) != 0.0
                push!(all_variables_vec, variable)
                break
            end
        end
    end
    nb_variables = length(all_variables_vec)

    tex_str = ""
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
    for variable in all_variables_vec
        coeff = get(objective_function(model).terms, variable, 0.0)
        if coeff != 0
            if firstobjcoeff
                firstobjcoeff = false
            elseif coeff > 0
                tex_str *= "+ "
            end
            tex_str *= "$(abs(coeff) == 1 ? (coeff == -1 ? "- " : "") : (coeff == round(coeff)) ? "$(round(Int, coeff)) " : "$coeff ")$(model[:var_names][variable]) & "
        else
            tex_str *= "& "
        end
    end
    tex_str *= "& \\\\\n"

    firstcst = true
    for (con, S, _) in all_constraints_vec
        tex_str *= "& "
        if firstcst
            firstcst = false
            tex_str *= "\\text{s.c.} "
        end
        tex_str *= "& "
        firstobjcoeff = true
        for variable in all_variables_vec
            coeff = normalized_coefficient(con, variable)
            if coeff != 0
                if firstobjcoeff
                    firstobjcoeff = false
                elseif coeff > 0
                    tex_str *= "+ "
                end
                tex_str *= "$(abs(coeff) == 1 ? (coeff == -1 ? "- " : "") : (coeff == round(coeff)) ? "$(round(Int, coeff)) " : "$coeff ")$(model[:var_names][variable]) & "
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
        tex_str *= "$(model[:var_names][all_variables_vec[i]]), & "
    end
    tex_str *= "$(model[:var_names][all_variables_vec[end]]) & \\geq & 0"
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

    i = 1
    for (con, S, _) in all_constraints_vec
        if S == MOI.LessThan{Float64}
            x = @variable(model, lower_bound=0.0)
            model[:var_names][x] = "\\textcolor{blue}{e_{$i}}"
            set_normalized_coefficient(con, x, 1.0)
        elseif S == MOI.GreaterThan{Float64}
            x = @variable(model, lower_bound=0.0)
            model[:var_names][x] = "\\textcolor{blue}{e_{$i}}"
            set_normalized_coefficient(con, x, -1.0)
        elseif S == MOI.EqualTo{Float64}
            x = @variable(model, lower_bound=0.0)
            model[:var_names][x] = "\\textcolor{blue}{e_{$i}}"
        else
            error()
        end
        i += 1
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
        model[:var_names][x] = "\\textcolor{red}{v_{$i}}"
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
    reduced_costs::Vector{Rational{Int}}
    dual_costs::Vector{Rational{Int}}
    objective_value::Rational{Int}
    basis_variables::Vector{Int}
    init_variables::Vector{Int}
    slack_variables::Vector{Int}
    artificial_variables::Vector{Int}
    variable_names::Vector{String}
    is_solved::Bool
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
    return simplex.reduced_costs
end

function set_objective_coefficient_value!(simplex::RationalSimplex, i::Int, value::Rational{Int})
    simplex.reduced_costs[i] = value
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

function get_init_variables(simplex::RationalSimplex)
    return simplex.init_variables
end

function is_solved(simplex::RationalSimplex)
    return simplex.is_solved
end

function solved!(simplex::RationalSimplex)
    simplex.is_solved = true
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





function model2simplex(model::Model)
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
            push!(var_names, model[:var_names][variable])
            push!(all_variables_vec, variable)
        end
    end
    nb_variables = length(all_variables_vec)

    basis_variables = Vector{Int}()
    init_variables = Vector{Int}(1:(nb_variables-2*nb_constraints))
    slack_variables = Vector{Int}((nb_variables-2*nb_constraints+1):(nb_variables-nb_constraints))
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
        init_variables,
        slack_variables,
        artificial_variables,
        var_names,
        false
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

    simplex.reduced_costs = simplex.reduced_costs[1:(end-length(artificial_variables))]
    simplex.variable_names = simplex.variable_names[1:(end-length(artificial_variables))]
    simplex.simplex_array = simplex.simplex_array[1:end, 1:(end-length(artificial_variables))]
    simplex.artificial_variables = Vector{Int}()
    simplex.artificial_objective = zeros(length(simplex.variable_names))
    simplex.artificial_objective_value = zero(Rational{Int})

    return simplex
end



function solve_with_simplex(init_model::Model, filename::String)
    model = copy(init_model)
    model[:var_names] = Dict{VariableRef, String}()
    nb_variables = length(all_variables(model))
    for i in 1:nb_variables
        variable = all_variables(model)[i]
        model[:var_names][variable] = "x_{$i}"
    end
    nb_constraints = 0
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        nb_constraints += length(all_constraints(model, F, S))
    end

    tex_str = ""
    tex_str *= "\n\\section*{Solving model with simplex}\n"
    tex_str *= "\n\\subsection*{Rewriting model}\n"

    tex_str *= model2latex(model)

    if objective_sense(model) == MOI.MIN_SENSE
        min2max!(model)
        tex_str *= "\n\nObjective function from \$\\min\$ to \$\\max\$\n\n"
        tex_str *= model2latex(model)
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
        tex_str *= model2latex(model)
    end

    tex_str *= "\n\nAdd slack variables\n\n"
    add_slack_variables!(model)
    tex_str *= model2latex(model)

    tex_str *= "\n\nAdd artificial variables\n\n"
    add_artificial_variables!(model)
    tex_str *= model2latex(model)

    tex_str *= "\n\nModel to simplex table\n\n"
    simplex = model2simplex(model)
    tex_str *= simplex2latex(simplex)

    tex_str *= "\n\n\\subsection*{Solving}\n"

    if !isempty(get_artificial_variables(simplex))
        tex_str *= "\nRepair simplex table\n\n"
        repair_simplex!(simplex)
        tex_str *= simplex2latex(simplex)

        while true in (get_artificial_objective(simplex) .< 0)
            variable_leaving = 0
            variable_entering = find_entering_variable(simplex)
            tex_str *= "\n\nEntering variable: \$$(get_var_names(simplex)[variable_entering])\$"
            possible_leaving_variables = find_leaving_variable_candidates(simplex, variable_entering)
            if isempty(possible_leaving_variables)
                tex_str *= "\n\nNo leaving variable."
                open(filename, "a") do f
                    write(f, tex_str)
                end
                return simplex
            elseif length(possible_leaving_variables) >= 2
                tex_str *= "\n\nMultiple possible leaving variables. Not handled yet."
                open(filename, "a") do f
                    write(f, tex_str)
                end
                return simplex
            end
            variable_leaving = possible_leaving_variables[1]
            constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
            tex_str *= " \\quad -- \\quad Leaving variable: \$$(get_var_names(simplex)[variable_leaving])\$"
            if get_array(simplex)[constraint_i, variable_entering] != 1
                tex_str *= "\n\n\\begin{align*}\n"
                tex_str *= "& L_{$(constraint_i)} \\leftarrow $(rational2tex(1//(get_array(simplex)[constraint_i, variable_entering]), in_math=true))L_{$(constraint_i)} \\\\\n"
                tex_str *= "\\end{align*}\n\n"
                normalize_simplex!(simplex, variable_entering, variable_leaving)
                tex_str *= simplex2latex(simplex)
            end

            tex_str *= "\n\n\\begin{align*}\n"
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
            open(filename, "a") do f
                write(f, tex_str)
            end
            return simplex
        elseif length(possible_leaving_variables) >= 2
            tex_str *= "\n\nMultiple possible leaving variables -- Uses Bland's rule.\n\n"
            tex_str *= "Entering variable: \$$(get_var_names(simplex)[variable_entering])\$"
            sort!(possible_leaving_variables)
        end
        variable_leaving = possible_leaving_variables[1]
        constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
        tex_str *= " \\quad -- \\quad Leaving variable: \$$(get_var_names(simplex)[variable_leaving])\$"
        if get_array(simplex)[constraint_i, variable_entering] != 1
            tex_str *= "\n\n\\begin{align*}\n"
            tex_str *= "& L_{$(constraint_i)} \\leftarrow $(rational2tex(1//(get_array(simplex)[constraint_i, variable_entering]), in_math=true))L_{$(constraint_i)} \\\\\n"
            tex_str *= "\\end{align*}\n\n"
            normalize_simplex!(simplex, variable_entering, variable_leaving)
            tex_str *= simplex2latex(simplex)
        end

        tex_str *= "\n\n\\begin{align*}\n"
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

    open(filename, "a") do f
        write(f, tex_str)
    end

    solved!(simplex)

    return simplex
end


mutable struct SensitivityIntervalVariables
    variable_names::Vector{String}
    reduced_costs::Vector{Rational{Int}}
    intervals::Vector{Tuple{Union{Nothing, Rational{Int}, Float64}, Union{Nothing, Rational{Int}, Float64}}}
end

function get_var_names(sensitivity_variables::SensitivityIntervalVariables)
    return sensitivity_variables.variable_names
end

function get_reduced_costs(sensitivity_variables::SensitivityIntervalVariables)
    return sensitivity_variables.reduced_costs
end

function get_var_name(sensitivity_variables::SensitivityIntervalVariables, var_indice::Int)
    return sensitivity_variables.variable_names[var_indice]
end

function get_reduced_cost(sensitivity_variables::SensitivityIntervalVariables, var_indice::Int)
    return sensitivity_variables.reduced_costs[var_indice]
end

function get_intervals(sensitivity_variables::SensitivityIntervalVariables)
    return sensitivity_variables.intervals
end

function get_interval(sensitivity_variables::SensitivityIntervalVariables, var_indice::Int)
    return sensitivity_variables.intervals[var_indice]
end

function get_nb_variables(sensitivity_variables::SensitivityIntervalVariables)
    return length(sensitivity_variables.reduced_costs)
end

function rational2tex(x::Float64; in_math=false)
    @assert abs(x) == Inf
    return "$(!in_math ? "\$" : "")$(x == Inf ? "" : "-")\\infty$(!in_math ? "\$" : "")"
end

function rational2tex(x::Nothing; in_math=false)
    return "$(!in_math ? "\$" : "")-$(!in_math ? "\$" : "")"
end

function sensitivity2latex(sensitivity_variables::SensitivityIntervalVariables)
    tex_str = ""
    nb_variables = get_nb_variables(sensitivity_variables)
    tex_str *= "\\begin{center}\n\\begin{tabular}{|c|cccc|}\\hline\n"
    tex_str *= "Variable & Reduced cost & Min & Current value & Max \\\\\n\\hline\n"
    for i in 1:nb_variables
        tex_str *= "$(get_var_name(sensitivity_variables, i)) & $(rational2tex(get_interval(sensitivity_variables, i)[1])) & $(rational2tex(get_reduced_cost(sensitivity_variables, i))) & $(rational2tex(get_interval(sensitivity_variables, i)[2])) \\\\\n"
    end
    tex_str *= "\\hline\n\\end{tabular}\n\\end{center}"
    return tex_str
end

function sensitivity_analysis(simplex::RationalSimplex, filename::String)
    tex_str = ""
    tex_str *= "\n\\section*{Sensitivity analysis}"
    tex_str *= "\n\\subsection*{Computing sensitivity of c_i}\n"

    tex_str *= "Sensitivity intervals for the variables:"

    init_variables = get_init_variables(simplex)
    nb_variables = length(init_variables)

    reduced_costs = get_objective_coefficients(simplex)[1:nb_variables]
    variable_names = get_var_names(simplex)[1:nb_variables]
    sen_intervals = Vector{Tuple{Union{Nothing, Int, Float64}, Union{Nothing, Int, Float64}}}(undef, nb_variables)
    for i in 1:nb_variables
        intervals[i] = (nothing, nothing)
    end
    sensitivity_variables = SensitivityIntervalVariables(
        reduced_costs,
        variable_names,
        sen_intervals
    )



end




function main()
    model = Model()
    @variable(model, x_1 >= 0)
    @variable(model, x_2 >= 0)
    @objective(model, Min, -2x_1 - x_2)
    @constraint(model, x_1 - x_2 >= -2)
    @constraint(model, -x_1 - x_2 >= -6)
    @constraint(model, 2x_1 >= 4)

    open(filename, "w") do f
        write(f, header)
    end

    simplex = solve_with_simplex(model, filename)
    if is_solved(simplex)
        sensitivity_analysis(simplex, filename)
    end

    open(filename, "a") do f
        write(f, footer)
    end

    return nothing
end
