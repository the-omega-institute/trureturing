---
bibkey: changshrock2001nnnstrips
authors: Shu-Chiuan Chang, Robert Shrock
year: 2001
title: "Exact Partition Function for the Potts Model with Next-Nearest Neighbor Couplings on Strips of the Square Lattice"
doi: 10.1142/S0217979201004630
url: https://arxiv.org/abs/cond-mat/0007505
claim: "We present exact calculations of partition function $Z$ of the $q$-state Potts model with next-nearest-neighbor spin-spin couplings, both for the ferromagnetic and antiferromagnetic case, for arbitrary temperature, on $n$-vertex strip graphs of width $L_y=2$ of the square lattice with free, cyclic, and Möbius longitudinal boundary conditions."
strata_touched:
  - D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229571.result
  - D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229573.result
  - D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229574.result
  - D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229575.result
  - D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229576.result
  - D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229577.result
  - D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578.result
license: citation-only
triage: anchor
---

# Full-temperature Potts counts on width-two king strips

## Verified locator

Source: [arXiv:cond-mat/0007505v2](https://arxiv.org/abs/cond-mat/0007505v2),
abstract; Section 1, the spin Hamiltonian, the relation between the temperature
variable and the edge variable, and the definition of the open strip;
Section 2, “Case of Free Longitudinal Boundary Conditions”, the generating
function and its displayed numerator coefficients and denominator.
The title and author names above follow the arXiv metadata and manuscript.

DOI: [10.1142/S0217979201004630](https://doi.org/10.1142/S0217979201004630).
The [Crossref record](https://api.crossref.org/works/10.1142/S0217979201004630)
confirms *International Journal of Modern Physics B* **15** (2001), 443–478,
and records the journal title as “EXACT PARTITION FUNCTION FOR THE POTTS
MODEL WITH NEXT-NEAREST NEIGHBOR COUPLINGS ON ARBITRARY-LENGTH LADDERS”.
The arXiv record associates that DOI with the manuscript cited here.

The abstract's first sentence is quoted in `claim`. The manuscript takes
equal nearest- and next-nearest-neighbour couplings, includes both diagonals
of each square, and restricts the transverse width to two. Its open strip
$S_m$ has $2(m+2)$ vertices, so it is the free $(m+2)\times2$ king strip.

## The one-unsatisfied-bond coefficient

The spin-sum definition gives
$Z(G;4,z-1)=\sum_f z^{b(f)}$, where $b(f)$ is the number of monochromatic
bonds. Thus $[z^1]Z(G;4,z-1)$ counts labelled states with exactly one
unsatisfied bond. Write the paper's length-generating variable as $x$,
reserving $z$ for the bond weight. Its Section 2 formulas give

$$
\begin{aligned}
\sum_{m\ge0}Z(S_m;4,z-1)x^m
&=\frac{24+z(144+72x)+O(z^2)}
        {1-2x-z(11x+6x^2)+O(z^2)},\\
[z^1]\sum_{m\ge0}Z(S_m;4,z-1)x^m
&=\frac{48(3+x)}{(1-2x)^2}.
\end{aligned}
$$

For $n\ge2$, a one-defect $n\times2$ colouring uses at least three colours,
so each colour orbit has $24$ labelled members; canonical first-appearance
order picks one. Dividing the coefficient by $24$ therefore gives

$$
\sum_{m\ge0}T(m+2,2)x^m=\frac{2(3+x)}{(1-2x)^2},\qquad
T(n,2)=(7n-8)2^{n-2}\quad(n\ge2).
$$

Consequently $T(n,2)=4T(n-1,2)-4T(n-2,2)$ for $n>3$.
The coefficient extraction and canonical normalization are deductions from
the published partition function; they are not quoted as an OEIS statement
made by the authors. This supplies the $k=2$ conjunct of A229578, while the
other six column lines and the diagonal recurrence concern counts beyond
the width-two result in this paper.
