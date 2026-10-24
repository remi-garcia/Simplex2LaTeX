using JuMP


function model2latex(model::Model)
    all_constraints_vec = list_constraints(model)

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


function rational2tex(x::Rational{BigInt}; in_math=false)
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
        tex_str *= "$(rational2tex(get_rhs_coefficient(simplex, i))) \\\\\n"
    end

    tex_str *= "\\end{tabular}\n\\end{center}"

    return tex_str
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
    tex_str *= "Variable & Reduced cost & Min & Current objective value & Max \\\\\n\\hline\n"
    for i in 1:nb_variables
        tex_str *= "\$$(get_var_name(sensitivity_variables, i))\$ & $(rational2tex(get_reduced_cost(sensitivity_variables, i))) & $(rational2tex(get_interval(sensitivity_variables, i)[1])) & $(rational2tex(get_initial_objective_coefficient(sensitivity_variables, i))) & $(rational2tex(get_interval(sensitivity_variables, i)[2])) \\\\\n"
    end
    tex_str *= "\\hline\n\\end{tabular}\n\\end{center}\n\n"
    return tex_str
end


function sensitivity2latex(sensitivity_constraints::SensitivityIntervalConstraints)
    tex_str = ""
    nb_constraints = get_nb_constraints(sensitivity_constraints)
    tex_str *= "\\begin{center}\n\\begin{tabular}{|c|cccc|}\\hline\n"
    tex_str *= "Constraint & Dual cost & Min & Current rhs value & Max \\\\\n\\hline\n"
    for j in 1:nb_constraints
        tex_str *= "\$\\left($(j)\\right)\$ & $(rational2tex(get_dual_cost(sensitivity_constraints, j))) & $(rational2tex(get_interval(sensitivity_constraints, j)[1])) & $(rational2tex(get_initial_rhs_coefficient(sensitivity_constraints, j))) & $(rational2tex(get_interval(sensitivity_constraints, j)[2])) \\\\\n"
    end
    tex_str *= "\\hline\n\\end{tabular}\n\\end{center}\n\n"
    return tex_str
end
