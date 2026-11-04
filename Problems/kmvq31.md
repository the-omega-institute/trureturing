---
slug: kmvq31
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.result
---

# Kaygorodov–Martín González–Viruel Question 31

## Problem

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of results and a list of open problems*, arXiv:2610.22248v1, section 2.2.5, page 24, ask: “Let G be a linear algebraic group over 𝕜. Is there a finite-dimensional evolution 𝕜-algebra A with Aut(A) ≅ G(𝕜) as abstract groups? with Aut(A) ≅ G as algebraic groups? with 𝐀𝐮𝐭(A) ≅ G as group schemes?”

The second and third interrogatives have a negative answer. The counterexample is $G=\mathrm{SL}_3$ over $\mathbb C$. The public `claim` is the affirmative universal statement for polynomial-closed matrix groups and full natural automorphism functors over every commutative unital complex coefficient algebra. It includes coefficient algebras with nilpotents. The abstract-group interrogative is outside this assertion.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Linear algebraic group $G$ over a field. | `LinearAlgebraicGroup` with a matrix degree, polynomial equations, points, zero-locus characterization and change-of-algebra stability. | The field is specialized to $\mathbb C$, sufficient to refute the universal question. |
| Finite-dimensional evolution algebra $A$. | Existential $d\in\mathbb N$ and bilinear product on $\mathrm{Fin}(d)\to\mathbb C$, satisfying `IsEvolutionAlgebra`. | An arbitrary natural basis is existential; zero dimension and degenerate algebras are included. |
| Full automorphism group or group scheme. | `automorphisms` contains all invertible linear maps preserving multiplication; `Realizes` gives multiplicative equivalences at every coefficient algebra and naturality for every algebra homomorphism. | No identity or associativity is imposed on multiplication. |
| Algebraic groups and group schemes. | The literal functor formulation in `claim`. | The comparison uses characteristic-zero smoothness; no theorem about arbitrary abstract point groups is asserted. |
| Is there such an $A$ for every $G$? | `result` proves the negation of `claim`. | The witness group is `slGroup 3`. |

## Motivation

A natural basis restricts the semisimple derivation algebra to orthogonal factors. Naturality of a full automorphism realization recovers its tangent Lie algebra, so the restriction obstructs continuous symmetry even when the evolution algebra has a nonzero annihilator.

## Gap

Preregistration [#21840](https://github.com/the-omega-institute/trureturing/issues/21840) supplies the source and binding functor conventions. The bounded literature screen found no settlement of these selected interrogatives in its inspected scope. Exhaustive priority and journal/preprint equivalence are `ASSUMED-UNVERIFIED`.

## Route

`EvolutionAutomorphismTangentBridge.tangent_lie_equivalence` reconstructs the derivative of a natural realization using dual numbers. Iterated dual numbers recover the Lie bracket. For a realization of $\mathrm{SL}_3$, this gives a Lie equivalence between all derivations and $\mathfrak{sl}_3$.

The settling proof applies `SemisimpleDerivationClassification.result`. A semisimple derivation algebra of a finite-dimensional complex evolution algebra is a finite direct sum of $\mathfrak{so}_{m_i}$ with $m_i\geq3$. The private dimension and radical arguments in the settling module exclude $\mathfrak{sl}_3$ from this classification. This is a structural obstruction, with no bound on the dimension of the evolution algebra.

## Falsifier

A full natural realization of $\mathrm{SL}_3$ by a finite-dimensional complex evolution algebra would contradict `AlgebraicGroupRealizationRefutation.result`. A mere abstract-group isomorphism on complex points would not contradict its statement. An error in the functor correspondence, tangent reconstruction or orthogonal classification would invalidate the claimed source application and must be distinguished from the kernel-checked proposition.

## Evidence

The settling declaration is `D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation.result`. Its Scribe displays the expanded negation of the affirmative proposition. The source note is the existing DOI owner `Library/QuadraticForms/kaygorodov2026evolution.md`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The audit for `EvolutionAutomorphismTangentBridge.tangent_lie_equivalence` and the published `SemisimpleDerivationClassification.SmallOrthogonal.diagonal_zero` and `coefficient_skew` remains unfinished under [#22191](https://github.com/the-omega-institute/trureturing/issues/22191); no `declared_validated` status is asserted.

### Exact experiment

The experiment is [kmv-q31-autgroups at revision 6a5d095d8b948ceca624b302c76f840f9ba78340](https://github.com/the-omega-institute/trureturing-experiments/tree/6a5d095d8b948ceca624b302c76f840f9ba78340/docs/reports/kmv-q31-autgroups). The immutable script is `docs/reports/kmv-q31-autgroups/check.py`, SHA-256 `0b891178c925416e3970a55a7058fa0e7cc64814046aa52be1ce50b91359f39f`. Executing that script with Python 3 (`python3 /Users/auric/.sshx/2563f1b2e6348950e15c8f21/attempt-1/check.py`, exit 0) returns `ALL_CHECKS_OK`.

Its exact scope is Proposition 14 examples $1\leq m\leq7$, generic bilinear products in dimensions $1\leq d\leq3$, the $8\times8$ adjoint Killing matrix of $\mathfrak{sl}_3$ with determinant $-5038848$, two polynomial identities, and the simultaneous rank/dimension search for $2\leq n\leq256$. The simultaneous matches are $(n,m)=(2,3),(4,6)$. Dimension alone also admits $(11,16)$, among other matches. The finite sweep is not an unbounded family proof and is not used as a Lean axiom or premise.

## Triage

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| Every orthogonal factor below dimension nine is $\mathfrak{so}_3$ or $\mathfrak{so}_4$; their dimension sums cannot be eight. | proved | Kernel-checked private `Dimensions.so_small_of_finrank_le_eight`, `Dimensions.no_sum_three_six` and `Obstruction.orthogonal_sum_not_eight` in the settling module, on the path of `result`; the classification is supplied by `SemisimpleDerivationClassification.result`. |
| $\mathrm{SL}_3$ is excluded as the full natural automorphism group functor of every finite-dimensional complex evolution algebra, including degenerate algebras. | proved | Kernel-checked `AlgebraicGroupRealizationRefutation.result`, using `Obstruction.derivations_not_sl3` and `EvolutionAutomorphismTangentBridge.tangent_lie_equivalence`. |
| Exact checker samples and arithmetic identities. | computed | The immutable experiment above, command exit 0 and matching SHA-256, covers exactly $1\leq m\leq7$, $1\leq d\leq3$, the specified Killing matrix, two polynomial identities and $2\leq n\leq256$. Finite sweeps are not unbounded proofs. |
| The full $n\geq3$, $n\neq4$ family. | open | No family theorem is formalized here; the additional Cartan-rank argument is required. |
| $\mathrm{SL}_2$, $\mathrm{SL}_4$, positive characteristic and abstract-group realization. | open | The tangent coincidences are not realization results. These categories and groups remain outside this settlement. |
| Finite, general-linear and orthogonal group realizations. | open | No new realization or non-realization theorem is delivered for these classes. The obstruction does not overturn the source examples. |

### What the settlement shows

The failure mechanism is the incompatibility of an eight-dimensional semisimple tangent algebra with orthogonal factors: $\dim\mathfrak{so}_m=m(m-1)/2$ and $m\geq3$ force each summand of dimension at most eight to have dimension three or six. Every finite sum is divisible by three, whereas $\dim\mathfrak{sl}_3=8$. These statements are proved by the private dimension and obstruction declarations named in Triage. The naturality theorem connects this invariant to the full automorphism functor.

The argument covers arbitrary finite-dimensional products with a natural basis, including degenerate ones. It leaves the source's finite, general-linear and orthogonal examples intact. The broader special-linear family requires rank information: the finite checker explicitly exhibits why dimension alone is insufficient. No downstream source theorem is revoked; the universal realization question receives a negative answer in the two selected categories.

## ASSUMED-UNVERIFIED

The literature screen is bounded; completeness and priority are `ASSUMED-UNVERIFIED`. The identification of the declared functor convention with the source's categories uses the stated characteristic-zero interpretation. The full special-linear family, positive characteristic and abstract-group interrogative remain open here. The unfinished four-slot escape audit is tracked in #22191 and is separate from Lean verification.
