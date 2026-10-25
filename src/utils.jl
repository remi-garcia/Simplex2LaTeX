using JuMP


function list_constraints(model::Model)
    all_constraints_vec = Vector{Tuple{Any, Any}}()
    for (F, S) in list_of_constraint_types(model)
        if F == VariableRef
            continue
        end
        cons = all_constraints(model, F, S)
        sort!(cons, by=con->con.index.value)
        for con in cons
            push!(all_constraints_vec, (con, S))
        end
    end

    return all_constraints_vec
end


function min2max!(model::Model)
    @assert objective_sense(model) == MOI.MIN_SENSE

    set_objective_sense(model, MOI.MAX_SENSE)
    for variable in all_variables(model)
        set_objective_coefficient(model, variable, -get(objective_function(model).terms, variable, 0.0))
    end

    return model
end


function rhs2pos!(model::Model, all_constraints_vec)
    all_constraints_rhs_vec = Vector{Bool}()
    all_variables_vec = all_variables(model)

    for (con, S) in all_constraints_vec
        push!(all_constraints_rhs_vec, false)
        if normalized_rhs(con) < 0
            set_normalized_rhs(con, -normalized_rhs(con))
            all_constraints_rhs_vec[end] = true
            for variable in all_variables(model)
                set_normalized_coefficient(con, variable, -normalized_coefficient(con, variable))
            end
        end
    end

    if !(true in all_constraints_rhs_vec)
        return all_constraints_vec
    end

    new_constraints_vec = Vector{Tuple{Any, Any}}()
    for i in 1:length(all_constraints_vec)
        con = all_constraints_vec[i][1]
        S = all_constraints_vec[i][2]
        c = [normalized_coefficient(con, variable) for variable in all_variables_vec]
        rhs = normalized_rhs(con)
        delete(model, con)
        if S == MOI.LessThan{Float64}
            if all_constraints_rhs_vec[i]
                con = @constraint(model, c' * all_variables_vec >= rhs)
            else
                con = @constraint(model, c' * all_variables_vec <= rhs)
            end
        elseif S == MOI.GreaterThan{Float64}
            if all_constraints_rhs_vec[i]
                con = @constraint(model, c' * all_variables_vec <= rhs)
            else
                con = @constraint(model, c' * all_variables_vec >= rhs)
            end
        elseif S == MOI.EqualTo{Float64}
            con = @constraint(model, c' * all_variables_vec == rhs)
        else
            error()
        end
        push!(new_constraints_vec, (con, typeof(constraint_object(con).set)))
    end

    return new_constraints_vec
end


function add_slack_variables!(model::Model, all_constraints_vec)
    i = 1
    for (con, S) in all_constraints_vec
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
    new_constraints_vec = Vector{Tuple{Any, Any}}()
    for i in 1:length(all_constraints_vec)
        con = all_constraints_vec[i][1]
        c = [normalized_coefficient(con, variable) for variable in all_variables_vec]
        rhs = normalized_rhs(con)
        delete(model, con)
        con = @constraint(model, c' * all_variables_vec == rhs)
        push!(new_constraints_vec, (con, MOI.EqualTo{Float64}))
    end

    return new_constraints_vec
end



function add_artificial_variables!(model::Model, all_constraints_vec)
    all_variables_vec = all_variables(model)

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
