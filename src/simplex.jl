using JuMP


mutable struct RationalSimplex
    simplex_array::Matrix{Rational{BigInt}}
    artificial_objective::Vector{Rational{BigInt}}
    artificial_objective_value::Rational{BigInt}
    initial_objective_coefficients::Vector{Rational{BigInt}}
    reduced_and_dual_costs::Vector{Rational{BigInt}}
    initial_rhs::Vector{Rational{BigInt}}
    rhs::Vector{Rational{BigInt}}
    objective_value::Rational{BigInt}
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

function set_objective_value!(simplex::RationalSimplex, value::Rational{BigInt})
    simplex.objective_value = value
    return simplex
end

function get_var_names(simplex::RationalSimplex)
    return simplex.variable_names
end

function get_objective_coefficients(simplex::RationalSimplex)
    return simplex.reduced_and_dual_costs
end

function get_objective_coefficient(simplex::RationalSimplex, i::Int)
    return simplex.reduced_and_dual_costs[i]
end

function get_initial_objective_coefficients(simplex::RationalSimplex)
    return simplex.initial_objective_coefficients
end

function get_initial_objective_coefficient(simplex::RationalSimplex, i::Int)
    return simplex.initial_objective_coefficients[i]
end

function get_initial_rhs_coefficients(simplex::RationalSimplex)
    return simplex.initial_rhs
end

function get_initial_rhs_coefficient(simplex::RationalSimplex, i::Int)
    return simplex.initial_rhs[i]
end

function set_objective_coefficient_value!(simplex::RationalSimplex, i::Int, value::Rational{BigInt})
    simplex.reduced_and_dual_costs[i] = value
    return simplex
end

function get_artificial_objective(simplex::RationalSimplex)
    return simplex.artificial_objective
end

function get_rhs_coefficients(simplex::RationalSimplex)
    return simplex.rhs
end

function get_rhs_coefficient(simplex::RationalSimplex, i::Int)
    return simplex.rhs[i]
end

function set_rhs_value!(simplex::RationalSimplex, i::Int, value::Rational{BigInt})
    simplex.rhs[i] = value
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

function set_coefficient_array!(simplex::RationalSimplex, i::Int, j::Int, value::Rational{BigInt})
    simplex.simplex_array[i,j] = value
    return simplex
end

function set_artificial_objective_coefficient!(simplex::RationalSimplex, i::Int, value::Rational{BigInt})
    simplex.artificial_objective[i] = value
    return simplex
end

function get_artificial_objective_coefficient(simplex::RationalSimplex, i::Int)
    return simplex.artificial_objective[i]
end


function get_artificial_objective_value(simplex::RationalSimplex)
    return simplex.artificial_objective_value
end

function set_artificial_objective_value!(simplex::RationalSimplex, value::Rational{BigInt})
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


function model2simplex(model::Model)
    init_all_variables_vec = all_variables(model)
    all_constraints_vec = list_constraints(model)

    nb_constraints = length(all_constraints_vec)
    all_variables_vec = Vector{VariableRef}()
    var_names = Vector{String}()
    init_variables = Vector{Int}()
    slack_variables = Vector{Int}()
    artificial_variables = Vector{Int}()
    nb_useless_variable = 0
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
            if i <= length(init_all_variables_vec)-2*nb_constraints
                push!(init_variables, i-nb_useless_variable)
            elseif i <= length(init_all_variables_vec)-nb_constraints
                push!(slack_variables, i-nb_useless_variable)
            else
                push!(artificial_variables, i-nb_useless_variable)
            end
        else
            nb_useless_variable += 1
        end
    end
    nb_variables = length(all_variables_vec)

    basis_variables = Vector{Int}()

    for i in 1:nb_constraints
        con = all_constraints_vec[i][1]
        last_variable = 0
        for j in 1:nb_variables
            if normalized_coefficient(con, all_variables_vec[j]) == 1.0
                last_variable = j
            end
        end
        push!(basis_variables, last_variable)
    end

    simplex = RationalSimplex(
        zeros(Rational{BigInt}, nb_constraints, nb_variables),
        zeros(Rational{BigInt}, nb_variables),
        zero(Rational{BigInt}),
        Vector{Rational{BigInt}}([rationalize(BigInt, get(objective_function(model).terms, variable, 0.0)) for variable in all_variables_vec]),
        Vector{Rational{BigInt}}([rationalize(BigInt, get(objective_function(model).terms, variable, 0.0)) for variable in all_variables_vec]),
        Vector{Rational{BigInt}}([rationalize(BigInt, normalized_rhs(con)) for (con, S, _) in all_constraints_vec]),
        Vector{Rational{BigInt}}([rationalize(BigInt, normalized_rhs(con)) for (con, S, _) in all_constraints_vec]),
        rationalize(BigInt, -objective_function(model).constant),
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
            set_coefficient_array!(simplex, i, j, rationalize(BigInt, normalized_coefficient(con, all_variables_vec[j])))
        end
    end
    for variable in artificial_variables
        set_artificial_objective_coefficient!(simplex, variable, big(1)//1)
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
            set_artificial_objective_value!(simplex, get_artificial_objective_value(simplex) - get_rhs_coefficient(simplex, i))
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
        if get_rhs_coefficient(simplex, i)//get_array(simplex)[i, variable_entering] <= minimum_value
            if get_rhs_coefficient(simplex, i)//get_array(simplex)[i, variable_entering] != minimum_value
                possible_leaving_variables = Vector{Int}()
            end
            push!(possible_leaving_variables, get_basis_variables(simplex)[i])
            minimum_value = get_rhs_coefficient(simplex, i)//get_array(simplex)[i, variable_entering]
        end
    end

    return possible_leaving_variables
end


function get_constraint_for_variable(simplex::RationalSimplex, variable_ind::Int)
    nb_constraints = get_nb_constraints(simplex)
    for i in 1:nb_constraints
        if variable_ind == get_basis_variables(simplex)[i]
            return i
        end
    end
    return 0
end

function get_constraint_for_leaving_variable(simplex::RationalSimplex, variable_leaving::Int)
    constraint_ind = get_constraint_for_variable(simplex, variable_leaving)
    if constraint_ind == 0
        error("Leaving variable is not in basis.")
    end
    return constraint_ind
end


function normalize_simplex!(simplex::RationalSimplex, variable_entering::Int, variable_leaving::Int)
    i = get_constraint_for_leaving_variable(simplex, variable_leaving)
    nb_variables = get_nb_variables(simplex)
    coeff = get_array(simplex)[i, variable_entering]
    for j in 1:nb_variables
        set_coefficient_array!(simplex, i, j, get_array(simplex)[i, j]//coeff)
    end
    set_rhs_value!(simplex, i, get_rhs_coefficient(simplex, i)//coeff)

    return simplex
end



function artificial_pivot!(simplex::RationalSimplex, variable_entering::Int, variable_leaving::Int)
    constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
    nb_variables = get_nb_variables(simplex)
    coeff = get_artificial_objective_coefficient(simplex, variable_entering)
    for j in 1:nb_variables
        set_artificial_objective_coefficient!(simplex, j, get_artificial_objective_coefficient(simplex, j) - coeff*get_array(simplex)[constraint_i,j])
    end
    set_artificial_objective_value!(simplex, get_artificial_objective_value(simplex) - coeff*get_rhs_coefficient(simplex, constraint_i))

    simplex_pivot!(simplex, variable_entering, variable_leaving)

    return simplex
end


function simplex_pivot!(simplex::RationalSimplex, variable_entering::Int, variable_leaving::Int)
    constraint_i = get_constraint_for_leaving_variable(simplex, variable_leaving)
    nb_variables = get_nb_variables(simplex)
    coeff = get_objective_coefficient(simplex, variable_entering)
    for j in 1:nb_variables
        set_objective_coefficient_value!(simplex, j, get_objective_coefficient(simplex, j) - coeff*get_array(simplex)[constraint_i,j])
    end
    set_objective_value!(simplex, get_objective_value(simplex) - coeff*get_rhs_coefficient(simplex, constraint_i))

    nb_constraints = get_nb_constraints(simplex)
    for i in 1:nb_constraints
        if i != constraint_i
            coeff = get_array(simplex)[i,variable_entering]
            for j in 1:nb_variables
                set_coefficient_array!(simplex, i, j, get_array(simplex)[i,j] - coeff*get_array(simplex)[constraint_i,j])
            end
            set_rhs_value!(simplex, i, get_rhs_coefficient(simplex, i) - coeff*get_rhs_coefficient(simplex, constraint_i))
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

    simplex.reduced_and_dual_costs = simplex.reduced_and_dual_costs[1:(end-length(artificial_variables))]
    simplex.variable_names = simplex.variable_names[1:(end-length(artificial_variables))]
    simplex.simplex_array = simplex.simplex_array[1:end, 1:(end-length(artificial_variables))]
    simplex.artificial_variables = Vector{Int}()
    simplex.artificial_objective = zeros(length(simplex.variable_names))
    simplex.artificial_objective_value = zero(Rational{BigInt})

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
    nb_constraints = length(list_constraints(model))

    tex_str = ""
    tex_str *= "\n\n\\section*{Solving model with simplex}\n"
    tex_str *= "\n\\subsection*{Rewriting model}\n"

    tex_str *= model2latex(model)

    if objective_sense(model) == MOI.MIN_SENSE
        min2max!(model)
        tex_str *= "\n\nObjective function from \$\\min\$ to \$\\max\$\n\n"
        tex_str *= model2latex(model)
    end

    rhsneg = false
    for (con, S, _) in list_constraints(model)
        if normalized_rhs(con) < 0
            rhsneg = true
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
                tex_str *= "\n\n\\begin{equation*}\n"
                tex_str *= "L_{$(constraint_i)} \\leftarrow $(rational2tex(1//(get_array(simplex)[constraint_i, variable_entering]), in_math=true))L_{$(constraint_i)} \n"
                tex_str *= "\\end{equation*}\n\n"
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
            coeff = get_objective_coefficient(simplex, variable_entering)
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
            tex_str *= "\n\n\\begin{equation*}\n"
            tex_str *= "L_{$(constraint_i)} \\leftarrow $(rational2tex(1//(get_array(simplex)[constraint_i, variable_entering]), in_math=true))L_{$(constraint_i)} \n"
            tex_str *= "\\end{equation*}\n\n"
            normalize_simplex!(simplex, variable_entering, variable_leaving)
            tex_str *= simplex2latex(simplex)
        end

        tex_str *= "\n\n\\begin{align*}\n"
        nb_constraints = get_nb_constraints(simplex)
        coeff = get_objective_coefficient(simplex, variable_entering)
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
