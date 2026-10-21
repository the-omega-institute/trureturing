# Multipartite CHS recurrence

For a finite part-size function `a`, `esymmParts a j` is the elementary symmetric sum of degree `j` in the part sizes. The sequence `recH a` starts at `1` and is defined by strong induction. For positive `d`, its defining equation is

`recH a d = ∑ j ∈ Finset.Icc 2 d, ((j : ℝ) - 1) * (esymmParts a j : ℝ) * recH a (d - j)`.

The module proves nonnegativity of every coefficient and strict positivity of the even coefficients when there are at least two positive parts. The extremal comparison theorem remains a separate open proof obligation for the transfer argument.
