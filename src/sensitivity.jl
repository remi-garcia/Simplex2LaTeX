mutable struct SensitivityIntervalVariables
    variable_names::Vector{String}
    reduced_costs::Vector{Rational{BigInt}}
    initial_objective_coefficients::Vector{Rational{BigInt}}
    intervals::Vector{Tuple{Union{Nothing, Rational{BigInt}, Float64}, Union{Nothing, Rational{BigInt}, Float64}}}
end

function get_initial_objective_coefficients(sensitivity_variables::SensitivityIntervalVariables)
    return sensitivity_variables.initial_objective_coefficients
end

function get_initial_objective_coefficient(sensitivity_variables::SensitivityIntervalVariables, i::Int)
    return sensitivity_variables.initial_objective_coefficients[i]
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

function set_interval!(sensitivity_variables::SensitivityIntervalVariables, var_indice::Int, interval::Tuple{Union{Rational{BigInt}, Float64}, Union{Rational{BigInt}, Float64}})
    sensitivity_variables.intervals[var_indice] = interval
    return sensitivity_variables
end

function get_nb_variables(sensitivity_variables::SensitivityIntervalVariables)
    return length(sensitivity_variables.initial_objective_coefficients)
end


mutable struct SensitivityIntervalConstraints
    dual_costs::Vector{Rational{BigInt}}
    initial_rhs_coefficients::Vector{Rational{BigInt}}
    intervals::Vector{Tuple{Union{Nothing, Rational{BigInt}, Float64}, Union{Nothing, Rational{BigInt}, Float64}}}
end

function get_initial_rhs_coefficients(sensitivity_constraints::SensitivityIntervalConstraints)
    return sensitivity_constraints.initial_rhs_coefficients
end

function get_initial_rhs_coefficient(sensitivity_constraints::SensitivityIntervalConstraints, i::Int)
    return sensitivity_constraints.initial_rhs_coefficients[i]
end

function get_dual_costs(sensitivity_constraints::SensitivityIntervalConstraints)
    return sensitivity_constraints.dual_costs
end

function get_dual_cost(sensitivity_constraints::SensitivityIntervalConstraints, const_indice::Int)
    return sensitivity_constraints.dual_costs[const_indice]
end

function get_intervals(sensitivity_constraints::SensitivityIntervalConstraints)
    return sensitivity_constraints.intervals
end

function get_interval(sensitivity_constraints::SensitivityIntervalConstraints, const_indice::Int)
    return sensitivity_constraints.intervals[const_indice]
end

function set_interval!(sensitivity_constraints::SensitivityIntervalConstraints, const_indice::Int, interval::Tuple{Union{Rational{BigInt}, Float64}, Union{Rational{BigInt}, Float64}})
    sensitivity_constraints.intervals[const_indice] = interval
    return sensitivity_constraints
end

function get_nb_constraints(sensitivity_constraints::SensitivityIntervalConstraints)
    return length(sensitivity_constraints.dual_costs)
end


function sensitivity_analysis(simplex::RationalSimplex, filename::String)
    tex_str = ""
    tex_str *= "\n\n\n\\section*{Sensitivity analysis}"
    tex_str *= "\n\\subsection*{Computing sensitivity of \$c_i\$}\n"

    tex_str *= "Sensitivity intervals for the variables:\n"
    init_variables = get_init_variables(simplex)
    nb_variables = length(init_variables)

    reduced_costs = get_objective_coefficients(simplex)[1:nb_variables]
    variable_names = get_var_names(simplex)[1:nb_variables]
    sen_intervals = Vector{Tuple{Union{Nothing, Int, Float64}, Union{Nothing, Int, Float64}}}(undef, nb_variables)
    for i in 1:nb_variables
        sen_intervals[i] = (nothing, nothing)
    end
    sensitivity_variables = SensitivityIntervalVariables(
        variable_names,
        reduced_costs,
        get_initial_objective_coefficients(simplex)[1:nb_variables],
        sen_intervals
    )
    tex_str *= sensitivity2latex(sensitivity_variables)

    total_nb_variables = length(get_objective_coefficients(simplex))

    for i in 1:nb_variables
        var_name = get_var_name(sensitivity_variables, i)
        tex_str *= "Compute sensitivity interval for variable \$$(var_name)\$\n"
        constraint_ind = get_constraint_for_variable(simplex, i)
        delta_has_lower_bound = false
        delta_has_upper_bound = false
        delta_lower_bound = big(0)//1
        delta_upper_bound = big(0)//1
        if constraint_ind != 0
            first_eq_done = false
            tex_str *= "\\begin{align*}\n"
            for j in 1:total_nb_variables
                if j != i
                    var_a = get_array(simplex)[constraint_ind, j]
                    if var_a != 0
                        if first_eq_done
                            tex_str *= " \\\\\n"
                        else
                            first_eq_done = true
                        end
                        var_b = get_objective_coefficient(simplex, j)
                        tex_str *= "& $(rational2tex(var_b, in_math=true)) $(var_a < 0 ? "+" : "-") $(abs(var_a) != 1 ? rational2tex(abs(var_a), in_math=true) : "") \\Delta_{$(var_name)} \\leq 0"
                        if var_a < 0
                            if delta_has_upper_bound
                                delta_upper_bound = min(delta_upper_bound, -var_b//abs(var_a))
                            else
                                delta_upper_bound = -var_b//abs(var_a)
                                delta_has_upper_bound = true
                            end
                        else
                            if delta_has_lower_bound
                                delta_lower_bound = max(delta_lower_bound, var_b//abs(var_a))
                            else
                                delta_lower_bound = var_b//abs(var_a)
                                delta_has_lower_bound = true
                            end
                        end
                    end
                end
            end
            tex_str *= "\n\\end{align*}\n"
        else
            delta_has_upper_bound = true
            delta_upper_bound = -get_reduced_cost(sensitivity_variables, i)
            tex_str *= "\n\\begin{equation*}\n"
            tex_str *= "$(rational2tex(get_reduced_cost(sensitivity_variables, i), in_math=true)) + \\Delta_{$(var_name)} \\leq 0"
            tex_str *= "\n\\end{equation*}\n"
        end
        tex_str *= "Thus \$\\Delta_{$(var_name)} \\in \\left[$(rational2tex(delta_has_lower_bound ? delta_lower_bound : -Inf, in_math=true)), $(rational2tex(delta_has_upper_bound ? delta_upper_bound : Inf, in_math=true))\\right]\$\n\n"
        set_interval!(sensitivity_variables, i, (delta_has_lower_bound ? delta_lower_bound+get_initial_objective_coefficient(sensitivity_variables, i) : -Inf, delta_has_upper_bound ? delta_upper_bound+get_initial_objective_coefficient(sensitivity_variables, i) : Inf))
        tex_str *= sensitivity2latex(sensitivity_variables)
    end

    tex_str *= "\n\\subsection*{Computing sensitivity of \$b_j\$}\n"

    tex_str *= "Sensitivity intervals for the constraints:\n"
    initial_rhs = get_initial_rhs_coefficients(simplex)
    nb_constraints = length(initial_rhs)
    dual_costs = -get_objective_coefficients(simplex)[(nb_variables+1):(nb_variables+nb_constraints)]
    sen_intervals = Vector{Tuple{Union{Nothing, Int, Float64}, Union{Nothing, Int, Float64}}}(undef, nb_constraints)
    for j in 1:nb_constraints
        sen_intervals[j] = (nothing, nothing)
    end
    sensitivity_constraints = SensitivityIntervalConstraints(
        dual_costs,
        initial_rhs,
        sen_intervals
    )
    tex_str *= sensitivity2latex(sensitivity_constraints)

    for j in 1:nb_constraints
        tex_str *= "Compute sensitivity interval for constraint \$\\left($j\\right)\$\n"
        delta_has_lower_bound = false
        delta_has_upper_bound = false
        delta_lower_bound = big(0)//1
        delta_upper_bound = big(0)//1
        first_eq_done = false
        tex_str *= "\\begin{align*}\n"
        for k in 1:nb_constraints
            var_a = get_array(simplex)[k, nb_variables+j]
            if var_a != 0
                if first_eq_done
                    tex_str *= " \\\\\n"
                else
                    first_eq_done = true
                end
                var_b = get_rhs_coefficient(simplex, k)
                tex_str *= "& $(rational2tex(var_b, in_math=true)) $(var_a < 0 ? "+" : "-") $(abs(var_a) != 1 ? rational2tex(abs(var_a), in_math=true) : "") \\Delta_{\\left($(j)\\right)} \\geq 0"
                if var_a < 0
                    if delta_has_lower_bound
                        delta_lower_bound = max(delta_lower_bound, -var_b//abs(var_a))
                    else
                        delta_lower_bound = -var_b//abs(var_a)
                        delta_has_lower_bound = true
                    end
                else
                    if delta_has_upper_bound
                        delta_upper_bound = min(delta_upper_bound, var_b//abs(var_a))
                    else
                        delta_upper_bound = var_b//abs(var_a)
                        delta_has_upper_bound = true
                    end
                end
            end
        end
        tex_str *= "\n\\end{align*}\n"
        tex_str *= "Thus \$\\Delta_{\\left($(j)\\right)} \\in \\left[$(rational2tex(delta_has_lower_bound ? delta_lower_bound : -Inf, in_math=true)), $(rational2tex(delta_has_upper_bound ? delta_upper_bound : Inf, in_math=true))\\right]\$\n\n"
        set_interval!(sensitivity_constraints, j, (delta_has_lower_bound ? delta_lower_bound+get_initial_rhs_coefficient(sensitivity_constraints, j) : -Inf, delta_has_upper_bound ? delta_upper_bound+get_initial_rhs_coefficient(sensitivity_constraints, j) : Inf))
        tex_str *= sensitivity2latex(sensitivity_constraints)
    end


    open(filename, "a") do f
        write(f, tex_str)
    end
    return sensitivity_variables, sensitivity_constraints
end
