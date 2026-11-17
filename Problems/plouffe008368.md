---
slug: plouffe008368
bibkey: conwaysloane1997a008368
doi: 10.1098/rspa.1997.0126
url: https://oeis.org/A008368
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/FccPointGroupShells.result
---

# Plouffe's generating function for point-group orbits on f.c.c. shells

## Problem

[OEIS A008368](https://oeis.org/A008368), revision 18, by Conway and Sloane, has NAME

> Number of orbits on points that are at n steps from the origin in the f.c.c. lattice.

and FORMULA

> G.f. is conjectured to be (1-x^5)/((1-x)*(1-x^2)^2*(1-x^3)) (a conjecture of Simon Plouffe, see A023054).

The lattice is $L=\{x\in\mathbb Z^3 : x_1+x_2+x_3 \text{ even}\}$. Its contact graph
joins $x$ and $y$ when $y-x$ is one of the twelve vectors $\pm e_i\pm e_j$ with $i<j$.
Here $n$ steps means graph distance from the origin. Orbits are taken under the full
point group of $L$, namely all $48$ signed coordinate permutations, reflections
included. The series starts at $n=0$, where $A(0)=1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| f.c.c. lattice | `FccPointGroupShells.L`, the even-sum subtype of `Fin 3 → ℤ` | Literal |
| one step | `contactGraph`: two coordinates change by a unit and the third is fixed | The twelve contact vectors |
| at $n$ steps from the origin | `d x = contactGraph.dist origin x` and `Shell n = {x // d x = n}` | Genuine shortest-walk distance |
| orbits | `A n`, the cardinality of the orbit quotient of `Shell n` under `W`, which acts by `latticeAction` | Literal quotient |
| full point group | `W`, the subgroup of all signed coordinate permutations | All $48$ elements |
| conjectured g.f. | `result`: $(1-X)(1-X^2)^2(1-X^3)\cdot\sum_n A(n)X^n=1-X^5$ in `PowerSeries ℤ` | Equivalent to the quotient, since the denominator has constant term $1$ |

The entry does not name the group. With rotations only, chiral classes split
into two orbits each, so the counts would be larger. The full group is the reading
that reproduces the sequence's terms.

## Motivation

The settling declaration is
`D5.S3.StatisticalMechanics.FccPointGroupShells.result`. The external assertion
and its conventions are preregistered in
[issue #26900](https://github.com/the-omega-institute/trureturing/issues/26900).
The source note is
`Library/StatisticalMechanics/conwaysloane1997a008368.md`. The f.c.c. lattice is
the cubic close-packed crystal structure. $A(n)$ counts the
symmetry-inequivalent sites in the $n$-th contact-graph coordination shell.

## Gap

The entry still records the generating function as a conjecture. The
preregistration's bounded screen found no proof of this orbit generating
function. It covered Conway–Sloane 1997, Baake–Grimm cond-mat/9706122,
Goodman-Strauss–Sloane arXiv:1803.08530, formal-conjectures and
Eppie/oeis-proofs. Literature completeness and priority are listed under
`ASSUMED-UNVERIFIED`.

## Route

The proof has three steps.

1. **Graph distance.** Define $\varphi(x)=\max(\max_i|x_i|,\ \tfrac12\sum_i|x_i|)$. Each contact step changes $\varphi$ by at most one. Applying the general potential lower bound `VertexPositionRatioRefutation.potential_dist`, from the frozen module `VertexPositionRatioRefutation`, gives $d\ge\varphi$. Conversely, every nonzero lattice point has a neighbour with potential exactly one less. Strong induction on that descent constructs a walk of length $\varphi(x)$. Therefore $d=\varphi$.
2. **Orbit representatives.** Each orbit has exactly one representative $a\ge b\ge c\ge0$ with $a+b+c$ even. The canonical sorted absolute value gives a bijection between the orbit quotient of a shell and these representatives at potential $n$.
3. **Generating function.** Split the representatives at $a=b+c$.
   - **Exterior cone** $a\ge b+c$: the parameters $(c,u,t)$ with $b=c+u$ and $a=2c+u+2t$ have weight $2c+u+2t$.
   - **Interior cone** $a<b+c$: write $p=1+i$, $q=p+j$, $r=q+k$ and $(a,b,c)=(q+r,p+r,p+q)$. The weight is $3+3i+2j+k$.

   Each cone's counting series is a product of geometric series. The sum is $1/((1-x)(1-x^2)^2)+x^3/((1-x)(1-x^2)(1-x^3))$, which equals $(1-x^5)/((1-x)(1-x^2)^2(1-x^3))$.

## Falsifier

A shell whose orbit count disagrees with a coefficient of the stated series would
contradict `result`.

## Evidence

The kernel declaration is
`D5.S3.StatisticalMechanics.FccPointGroupShells.result`. Its axiom closure is
contained in `{propext, Classical.choice, Quot.sound}`. The only direct frozen
dependency is
`D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.potential_dist`.

## Triage

1. **Proved (kernel-checked):** Plouffe's generating function for the
   full-point-group orbit counts on every contact-graph shell of the f.c.c.
   lattice, including $n=0$, by `FccPointGroupShells.result`.
2. **Proved (kernel-checked), internal:** the contact-graph distance equals
   $\max(\max_i|x_i|,\tfrac12\sum_i|x_i|)$ at every lattice point. This is a
   private step of `result`.
3. **Open:** the rotation-only (chiral) orbit counts and their generating
   function. Chiral classes with three distinct nonzero coordinates split, so
   that series differs from this one.
4. **Open:** analogous orbit generating functions for other root lattices
   $D_n$ ($n\ge4$) and for the b.c.c. and diamond structures.

### What the settlement shows

Three ingredients carry the identity:
- an explicit graph distance;
- the cone decomposition of sorted representatives along the hyperplane $a=b+c$;
- a monomial parametrisation of each cone.

The numerator $1-x^5$ comes from adding the two cones' series: $(1-x^3)+x^3(1-x^2)$.
The same method applies to any lattice with a polyhedral distance function and a
signed-permutation point group. Items 3 and 4 above record the neighbouring
cases. The companion entry A023054 is defined from the conjectured function,
so its identification with these orbit counts now holds by this proof.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The bounded
screen in #26900 was reported by the proposer and was not independently
re-run, and the OEIS history page was unavailable. No claim is made about
other lattices or rotation-only counts.
