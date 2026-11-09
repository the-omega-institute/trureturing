---
slug: kmvq12
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation.result
---

# Kaygorodov–Martín González–Viruel Question 12: direct sums

## Problem

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of results and a list of open problems*, arXiv:2610.22248v1, §2.2.2, Question 12, p. 22, ask:

> Characterise the evolution algebras all of whose subalgebras are evolution algebras. Is this property detected by the graphs? Is it preserved by tensor products and direct sums? What about ideals?

The affirmative direct-sum assertion is false. There are rational hereditary evolution algebras of dimensions four and three whose direct sum contains a multiplication-closed subspace with no intrinsic natural basis. The source permits arbitrary fields and assumes finite dimension unless stated otherwise. Heredity quantifies over every closed linear subspace, including zero and the whole space; its natural basis need not extend to one of the ambient algebra. Multiplication is bilinear and need not be associative or unital.

### Statement echo

| Source clause or binding convention | Formal counterpart | Fidelity |
| --- | --- | --- |
| “Let $\Bbbk$ be a field.” | `claim` quantifies over `K` with a field instance. | No characteristic restriction is imposed on the assertion; a rational counterexample refutes it. |
| “Unless stated otherwise, algebras are finite-dimensional.” | `claim` quantifies over $m,n\in\mathbb N$ and products on $\mathrm{Fin}(m)\to K$ and $\mathrm{Fin}(n)\to K$. | Every finite-dimensional vector space has such a coordinate presentation; zero dimensions are included. |
| An evolution algebra admits a natural basis with zero mixed products. | Existing `DerivationAnnihilatorObstruction.IsEvolutionAlgebra`. | Its index type and actual `Module.Basis` are existential, with commutativity and zero mixed products. |
| “all of whose subalgebras are evolution algebras” | `Hereditary` quantifies over every `Submodule` and every multiplication-closure proof; `inheritedProduct` restricts the given product. | Intrinsic natural bases are required; no extension property, nondegeneracy or perfectness hypothesis is added. |
| “Is it preserved by tensor products and direct sums?” | `directSumProduct` is componentwise multiplication; `claim` selects its direct-sum implication; `result` negates it. | Tensor-product preservation is a separate open clause. |
| Characterization, graph detection and ideals. | Outside the settling proposition. | These clauses remain open in this delivery. |
| Two evolution-algebra premises and two hereditary premises. | The four implications in `claim`. | They express the source's preservation question; every premise is supplied for the rational witness. |

The public definitions retain the literal binding conventions of [#21985](https://github.com/the-omega-institute/trureturing/issues/21985). Restriction and componentwise multiplication use Mathlib's existing linear-map constructions. The intrinsic evolution-algebra predicate is reused at its existing owner.

## Motivation

One symmetric scalar-output form can be diagonalized on each subspace. A subalgebra of a direct sum can couple two output directions, requiring simultaneous zero mixed products. The example separates individual hereditary factors from that joint constraint.

## Gap

Preregistration [#21985](https://github.com/the-omega-institute/trureturing/issues/21985) gives the exact source, quantifiers and literature screen. Its bounded screen found no published settlement of the selected direct-sum clause. Completeness is `ASSUMED-UNVERIFIED`.

Camacho–Khudoyberdiyev–Omirov, arXiv:1405.7126, Example 3.5 concerns the stronger extension property P. Its displayed two-dimensional subalgebra already has an intrinsic natural basis, so that example does not settle the present assertion. García-Martínez–Pérez-Rodríguez, arXiv:2512.12418v1, distinguishes the subalgebra notions. Bustamante–Mellon–Velasco, DOI 10.3390/math8081349, arXiv:2102.04493, gives simultaneous-diagonalization recognition results. These are literature context, not dependencies of the Lean proof.

## Route

The module is `D5/S3/QuadraticForms/EvolutionAlgebras/DirectSumHeredityRefutation`, with generality `G` and `admission_basis: open-problem-resolution (#21985; Refuted)`. All theorem proofs are conservatively classified `bind-only`; the settling conclusion uses the named external-problem admission basis. The private helpers are consumed by the settling proof.

For a finite-dimensional vector space over a field with invertible two, the private `rank_one_hereditary` applies `LinearMap.BilinForm.exists_orthogonal_basis` to the symmetric form restricted to each closed subspace. Orthogonal vectors have zero product under a scalar-output multiplication $ab=\beta(a,b)w$. The private `rank_one_evolution` supplies the corresponding ambient premise.

Over $\mathbb Q$, use the forms $\operatorname{diag}(1,-1,1,-1)$ and $\operatorname{diag}(1,-1,1)$, with output vectors $u=(1,1,0,0)$ and $v=(1,1,0)$. In the product impose $a_0=a_1$, $b_0=b_1$ and $b_2=a_2+a_3$. The private `coupled_closed` proves closure, and `product_readouts` extracts the equations forced by a zero product. For any proposed natural basis, `readouts_proportional` forces the functionals $f=a_2+a_3$ and $g=a_2-a_3$ to be proportional. Evaluation at the explicit vectors $((0,0,1,0),(0,0,1))$ and $((0,0,0,1),(0,0,1))$ gives a contradiction. The private `coupled_not_evolution` allows an unrestricted basis index type. The public `result` connects these facts to the negation of the full direct-sum implication.

## Falsifier

A defect in closure, the all-subspace hereditary argument, or the exclusion of every intrinsic natural basis would invalidate the mathematical application. Finite enumeration cannot substitute for either universal assertion. A positive statement restricted to perfect factors, or a statement about extending a basis, does not contradict this result.

## Evidence

The public settling theorem is `D5.S3.QuadraticForms.EvolutionAlgebras.DirectSumHeredityRefutation.result`, with type the negation of the literal `claim`. Its Scribe displays the full negated proposition and contains one Refuted `OpenProblemResolutionClaim` for `kmvq12`. The source note is the existing DOI owner `Library/QuadraticForms/kaygorodov2026evolution.md`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact experiment

The experiment is [kmv-question12-direct-sum-heredity at revision 412a0ac7ec48f149dba0ae5c1725d15cee29db94](https://github.com/the-omega-institute/trureturing-experiments/tree/412a0ac7ec48f149dba0ae5c1725d15cee29db94/docs/reports/kmv-question12-direct-sum-heredity). Its script is `docs/reports/kmv-question12-direct-sum-heredity/check.py`, SHA-256 `95b35ad9aced5ae548c7ed8ce9e05a02fbe5eeb94713cb6a437a689a53dd17bf`. The command `python3 docs/reports/kmv-question12-direct-sum-heredity/check.py`, run from that repository with those script bytes, exits 0 and reports `ALL_CHECKS_OK`. Arithmetic uses integers, rational fractions and exact symbolic expressions.

The tested family has $m=4,\ldots,9$ and $n=3,\ldots,8$ over $\mathbb Q,\mathbb F_3,\mathbb F_5,\mathbb F_7$: 144 cases. Each case verifies the rank-one factor product spans, zero factor annihilators, $\dim S=4$, $\dim S^2=2$, and all sixteen ordered products of the four displayed generators. The checker verifies ten function-algebra idempotent counts, for $1\leq n\leq5$ over $\mathbb F_3,\mathbb F_5$.

For hereditary factors it exhausts the subspaces of $A_4$ and $B_3$. Over $\mathbb F_3$, it checks 212/28 subspaces, of which 50/10 are closed; over $\mathbb F_5$, it checks 1120/64 subspaces, of which 110/14 are closed. Each closed subspace has an independently verified natural basis. Quotient enumeration checks 81, 625, 2401, 14641 and 28561 ordered pairs over $\mathbb F_3,\mathbb F_5,\mathbb F_7,\mathbb F_{11},\mathbb F_{13}$, respectively, and finds zero independent zero-product pairs. The symbolic product identity and nonzero square-zero matrix check explain the obstruction; they are computed evidence, not additional Lean theorems.

## Triage

| Item | Status | Evidence kind and boundary |
| --- | --- | --- |
| The arbitrary-field affirmative direct-sum assertion is false, witnessed over $\mathbb Q$ by factor dimensions four and three; hereditary premises quantify over every closed subspace. | proved | Kernel-checked `DirectSumHeredityRefutation.result`, through private `rank_one_hereditary`, `rank_one_evolution`, `coupled_closed` and `coupled_not_evolution`. |
| Every finite-dimensional symmetric scalar-output rank-one product is hereditary when two is invertible. | proved | Kernel-checked private `rank_one_hereditary`, a direct application of the classical orthogonal-basis theorem to every closed subspace. |
| The explicit coupled submodule is closed and has no intrinsic natural basis, without restricting the basis index type. | proved | Kernel-checked private `coupled_closed` and `coupled_not_evolution`. |
| The 144 rational/finite-field family cases, rank-one spans, zero annihilators, $\dim S=4$, $\dim S^2=2$, exhaustive factor-subalgebra checks over $\mathbb F_3,\mathbb F_5$, and quotient checks over $\mathbb F_3,\mathbb F_5,\mathbb F_7,\mathbb F_{11},\mathbb F_{13}$. | computed | The immutable exact experiment, command exit 0 and matching SHA-256 above, covers exactly the stated fields, dimensions and pair counts. |
| The unbounded-dimensional counterexample family over every field of characteristic different from two. | open | No such uniform theorem is delivered in Lean. The general hereditary helper alone does not prove that whole counterexample family. |
| Characteristic two, minimal dimensions, graph detection, tensor-product preservation, ideal clauses and full characterization. | open | These are outside `claim` or not settled by its negation; no theorem is claimed for them. |
| Perfect/regular evolution algebras remain a positive neighbour: every subalgebra is an evolution algebra, and a direct sum of perfect factors is perfect. | proved | Published Theorem 2 of Ladra–Pérez-Rodríguez, arXiv:2503.07187, DOI 10.5802/crmath.804; the direct-sum step is proved in prose below. This is a literature boundary, not a new kernel-checked theorem. |

### What the settlement shows

The failure mechanism is coupling two independent scalar-output forms on one subspace. Each factor permits its own orthogonal basis on every subalgebra, but the coupled restriction cannot have a basis with zero mixed products. The private declarations named in Triage establish that obstruction and the rational refutation in Lean.

Nondegeneracy alone does not repair the direct-sum assertion. In the displayed natural bases every square is nonzero. If an element annihilates a factor, multiplying it by each natural basis vector gives its corresponding coordinate times a nonzero square; each coordinate therefore vanishes. This is a prose proof for the displayed factors, consistent with the finite exact checks, rather than an additional Lean theorem.

A surviving positive statement assumes perfect factors. Here perfect means $A^2=A$, where $A^2$ is the linear span of all products; in this finite-dimensional evolution-algebra setting it is the regular case of Ladra–Pérez-Rodríguez Theorem 2. For two perfect factors, $(A\oplus B)^2=A^2\oplus B^2=A\oplus B$: products are componentwise, and each product supported in one factor is a product of two vectors supported there. Their direct sum is an evolution algebra by the union of natural bases, and the published theorem makes each subalgebra an evolution algebra. This implication is proved in prose using the cited theorem, not formalized here.

The source presents direct-sum preservation as a question. The negative answer changes that selected affirmative assertion; it does not revoke a source theorem. The stronger extension-property examples and the source's graph, tensor-product, ideal and characterization questions retain their distinct scopes. Uniform families and sharp dimensional boundaries remain follow-up candidates.

## ASSUMED-UNVERIFIED

Literature completeness and priority are `ASSUMED-UNVERIFIED`. The screen in #21985 includes arXiv sources and the final Ladra–Pérez-Rodríguez article; the final Camacho–Khudoyberdiyev–Omirov and García-Martínez–Pérez-Rodríguez publisher texts were inaccessible, arXiv:2311.00102v2 was withdrawn and unavailable, and citation-index endpoints were rate-limited. Those gaps are not negative search results. Numerical checks cover only their stated finite scopes; no unbounded family or characteristic-two settlement is claimed.
