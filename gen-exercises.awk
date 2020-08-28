BEGIN {
    in_solution = 0;
}
{ # on every line of the input
    if (match($0, /^( *)\(\* *BEGIN SOLUTION *\*\)$/, groups)) {
        in_solution = 1
    } else if (match($0, /^( *)\(\* *END SOLUTION *\*\)$/, groups)) {
        print groups[1] "  (* exercise *)"
        print groups[1] "Admitted."
        in_solution = 0
    } else if (match($0, /^( *)\(\* *END SOLUTION BEGIN TEMPLATE *$/, groups)) {
        in_solution = 0
    } else if (match($0, /^( *)END TEMPLATE *\*\)$/, groups)) {
        # Nothing to do, just do not print this line.
    } else if (in_solution == 0) {
        gsub("From solutions Require", "From exercises Require")
        print
    }
}
