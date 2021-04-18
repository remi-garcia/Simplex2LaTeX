include("../src/main.jl")

function model1()
    model = Model()
    @variable(model, x_1 >= 0)
    @variable(model, x_2 >= 0)
    @objective(model, Min, -2x_1 - x_2)
    @constraint(model, x_1 - x_2 >= -2)
    @constraint(model, -x_1 - x_2 >= -6)
    @constraint(model, 2x_1 >= 4)

    filename = (@__DIR__)*"/../outputs/model1.tex"
    main(model, filename)

    return nothing
end
