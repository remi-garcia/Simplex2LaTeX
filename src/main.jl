using JuMP

include("utils.jl")
include("simplex.jl")
include("sensitivity.jl")
include("latex.jl")


function main(model::Model, filename::String)
    open(filename, "w") do f
        write(f, """
        \\documentclass[11pt]{article}
        \\usepackage[utf8]{inputenc}
        \\usepackage{amssymb}
        \\usepackage{amsmath}
        \\usepackage[usenames, dvipsnames]{xcolor}
        \\usepackage{xspace}
        \\usepackage{booktabs}
        \\usepackage{array}
        \\setlength\\parindent{0pt}

        \\begin{document}
        """)
    end

    simplex = solve_with_simplex(model, filename)
    if is_solved(simplex)
        sensitivity_analysis(simplex, filename)
    end

    open(filename, "a") do f
        write(f, "\n\n\\end{document}")
    end

    return nothing
end
