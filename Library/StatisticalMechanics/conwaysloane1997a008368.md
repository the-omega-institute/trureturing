---
bibkey: conwaysloane1997a008368
authors: J. H. Conway, N. J. A. Sloane
year: 1997
title: "Low-Dimensional Lattices VII: Coordination Sequences"
doi: 10.1098/rspa.1997.0126
url: https://doi.org/10.1098/rspa.1997.0126
claim: "OEIS A008368 counts point-group orbits on contact-graph shells of the face centered cubic lattice; the entry attributes the rational generating function to a conjecture of Simon Plouffe."
strata_touched:
  - D5/S3/StatisticalMechanics/FccPointGroupShells
license: citation-only
triage: anchor
---

# Point-group orbits on face centered cubic shells

Conway and Sloane, *Proceedings of the Royal Society of London A* **453**, 2369–2389,
DOI [10.1098/rspa.1997.0126](https://doi.org/10.1098/rspa.1997.0126), is the lattice
reference linked by [OEIS A008368](https://oeis.org/A008368).
The [immutable OEIS entry](https://raw.githubusercontent.com/oeis/oeisdata/77073cc8105b8042be07ec0d885da5ea5960ff3c/seq/A008/A008368.seq)
states:

> Number of orbits on points that are at n steps from the origin in the f.c.c. lattice.

> G.f. is conjectured to be (1-x^5)/((1-x)*(1-x^2)^2*(1-x^3))
> (a conjecture of Simon Plouffe, see A023054).

The specified lattice is
$L=\{x\in\mathbb Z^3:x_0+x_1+x_2\equiv0\pmod2\}$.
A contact step is one of the twelve vectors $\pm e_i\pm e_j$ with $i<j$.
Distance means minimum walk length in this graph. The group consists of all signed
coordinate permutations, with reflections included. With this group, each orbit has
exactly one representative $(a,b,c)$ with $a\ge b\ge c\ge0$ and even coordinate sum.
This fixes the group interpretation of the OEIS word “orbits”; the rotation subgroup
is a different action.

## Generating function

The repository theorem concerns the literal shell-orbit count, including radius zero.
Its proof derives the distance formula

$$d(a,b,c)=\max\left(a,\frac{a+b+c}{2}\right).$$

Each edge changes a coordinate by at most one and changes the sum of absolute
coordinates by at most two, giving the lower bound. A step toward zero in the two
largest nonzero coordinates decreases the proposed distance by one. When only the
largest coordinate is nonzero, it is positive and even; decrease it by one and
increase a zero coordinate to one. Signed permutations transport this descent to
all vertices. Strong induction constructs a walk attaining the bound.

Split the representatives into two disjoint regions. If $a\ge b+c$, there is a unique
triple $(c,u,t)\in\mathbb N^3$ with

$$b=c+u,\qquad a=2c+u+2t,\qquad d=2c+u+2t.$$

If $a<b+c$, write

$$p=1+i,\quad q=p+j,\quad r=q+k,\qquad
(a,b,c)=(q+r,p+r,p+q).$$

Here $(i,j,k)\in\mathbb N^3$ is unique and $d=3+3i+2j+k$.
Thus the two contributions are

$$\frac1{(1-X)(1-X^2)^2}
  +\frac{X^3}{(1-X)(1-X^2)(1-X^3)}.$$

Multiplying by $(1-X)(1-X^2)^2(1-X^3)$ gives
$(1-X^3)+X^3(1-X^2)=1-X^5$.
This derivation and its formal proof are repository results. The OEIS entry supplies
the sequence and conjectural formula; no claim about priority or the absence of
other proofs is made here. The identity is formal over the integers and makes no
analytic convergence assertion.
