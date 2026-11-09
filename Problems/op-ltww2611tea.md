---
slug: op-ltww2611tea
bibkey: litsaiwangwong2026tea
doi: 10.48550/arXiv.2611.06187
url: https://arxiv.org/abs/2611.06187v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.result
---

# Triangle equality attainment preservers on complex C*-algebras

## Problem

Li–Tsai–Wang–Wong, *Linear maps of C*-algebras preserving norm parallelism*, arXiv:2611.06187v1, Problem 1.1, asks:

> For which complex $C^*$-algebras $\mathcal A,\mathcal B$ must every
> linear bijection $T:\mathcal A\to\mathcal B$ preserving parallelism
> in both directions be a scalar multiple of an isometry?
> Does the same conclusion hold for arbitrary complex $C^*$-algebras
> if TEA pairs are preserved in both directions?

The settlement is **Proved** for the second sentence. The first sentence is outside the target. A TEA pair satisfies $\|a+b\|=\|a\|+\|b\|$.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Arbitrary complex C*-algebras | `NonUnitalCStarAlgebra A` and `NonUnitalCStarAlgebra B` in `claim` | Includes unital, nonunital and zero algebras. |
| Linear bijection | `T : A →ₗ[ℂ] B` and `Function.Bijective T` | No continuity or boundedness assumption. |
| TEA pairs in both directions | `PreservesTEABothDirections T`, using `CStarTriangleEqualityPlane.TEAPair` | The predicate is the literal norm equality, on every pair. |
| Scalar multiple of an isometry | `ScalarMultipleOfIsometry T` | A nonzero complex scalar and a surjective complex-linear isometry, with pointwise equality. |

The public definitions retain the preregistered expressions. `claim` and `result` have the same proposition. The Scribe displays the expanded proposition. The settling module has generality G, utility none, and admission basis `open-problem-resolution (#27007; Proved)`.

## Motivation

`D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.result` proves the exact TEA clause. The source is recorded in `Library/HilbertOperators/litsaiwangwong2026tea.md`; the source and literature screen are identified in [#27007](https://github.com/the-omega-institute/trureturing/issues/27007).

## Gap

The source's finite-dimensional, commutative and type-I results have additional scope restrictions. The TEA assertion here quantifies over arbitrary complex C*-algebras. The literature screen in #27007 covers the versioned source, related author material, related preserver papers, Crossref and web searches. It does not establish worldwide priority or exhaustive absence of another settlement. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For a complex-linear map $T$, pull back the codomain norm to the finite complex seminorm $p(a)=\|T(a)\|$. Forward TEA preservation makes $p$ additive on original TEA pairs. The private theorem `CStarTriangleEqualityPreservers.seminorm_rigidity` proves $p(a)=c\|a\|$ for a single $c\ge0$.

The plane argument controls the sup-norm geometry of two complex coordinates. Spectral-plane estimates and the Russo–Dye convex-hull theorem give unital rigidity. In an algebra with no algebraic identity, three spectral pieces and nine corners give a Lipschitz estimate without presupposing continuity. Local identity corners and joint approximation synchronize the scale. Injectivity makes the scale positive on a nonzero source; surjectivity gives the isometric equivalence. The zero source is represented with scalar one.

The imported supporting modules are closed Lean source, with generality G and utility none. Their admission basis is `escape-witness`; their content lies on the settling proof's dependency path. They are distinct from frozen membership, which is recorded only by a module state file.

## Falsifier

The settlement would fail source fidelity if it required a chosen identity, excluded the zero algebra, assumed continuity of $T$, used a weaker relation than the literal TEA equality, or produced only an injective isometry. None of these restrictions occurs in `claim`. The intermediate seminorm statement requires complex homogeneity and forward TEA additivity; it does not assert rigidity for arbitrary real C*-algebras or arbitrary Banach spaces.

## Evidence

The canonical settling source is `D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers.lean`; its public settling theorem is `D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.result`. It imports the hereditary, nonunital-continuity and plane modules directly. The unital proof consumes `RussoDye.closedConvexHull_unitary` through `CStarTriangleEqualityUnital.seminorm_bound_of_unitary_bound`. The licensed supplier and its full Apache-2.0 text are in `D5/S3/Quantum/Analysis/RussoDye.lean`, with its citation in `Library/HilbertOperators/suzuki2026russodye.md`.

The escape audit for all 15 public theorems is unfinished in [#27516](https://github.com/the-omega-institute/trureturing/issues/27516). The missing evidence is a faithful source-bound dependent-family reconstruction and typed bridge, with variation, sensitivity and observational-dependence proofs that retain arbitrary carriers and zero fibers. No registration is claimed `declared_validated`.

### Experiment

The experiment is [li-tsai-wang-wong-2026-tea-preservers at commit 0a8b5b395bf1de576349641f772fce816ed17ab2](https://github.com/the-omega-institute/trureturing-experiments/tree/0a8b5b395bf1de576349641f772fce816ed17ab2/docs/reports/li-tsai-wang-wong-2026-tea-preservers).

Command: `git -C /Users/auric/trureturing-experiments show 0a8b5b395bf1de576349641f772fce816ed17ab2:docs/reports/li-tsai-wang-wong-2026-tea-preservers/check.py | python3` (with pipeline failure propagation). Exit code: 0. Script SHA-256: `df7abc38df4149a730114037dcfad1740e3e4b877efe0c7b4db8f92e8c116dfb`.

The finite search tests 233 input TEA pairs. Its two-row, nine-symbol search enumerates 6561 maps and has 65 scalar sup-seminorm survivors; its one-row, five-symbol search enumerates 25 maps and has one survivor; its three-row, five-symbol search enumerates 15625 maps and has 481 survivors. The rational phase perturbation gives $p(v_t)^2=p(v_{-t})^2=256/257<1=p((v_t+v_{-t})/2)^2$. Rational local cutoffs sum to one and all nine corners reconstruct the input. The checker finishes with `ALL_CHECKS_OK`. These are finite computed results, not the universal proof.

## Triage

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Reverse preservation is unnecessary for the compiled seminorm lemmas and product/unital norm conclusions. | Proved; kernel-checked. | `CStarTriangleEqualityPlane.seminorm_product_rigidity`, `CStarTriangleEqualityUnital.seminorm_unital_rigidity`, and private `CStarTriangleEqualityPreservers.seminorm_rigidity` assume forward TEA additivity only. The source claim retains both directions. |
| The C² conclusion permits arbitrary complex normed codomains and non-injective linear maps; zero scale is allowed. | Proved; kernel-checked. | Private `CStarTriangleEqualityPlane.two_coordinate_rigidity` treats a complex-linear map into an arbitrary complex normed space without injectivity and allows zero scale. Public `seminorm_on_isometric_plane` transports the seminorm version along an isometric embedding. |
| Russo–Dye and directional real-part estimates bypass pure-state irreducibility and Kadison transitivity in the unital proof. | Proved; kernel-checked. | `CStarTriangleEqualityUnital.seminorm_unital_rigidity` uses `seminorm_realPart_le` and `seminorm_bound_of_unitary_bound`, which consumes `RussoDye.closedConvexHull_unitary`. The proof uses these estimates rather than a pure-state or Kadison-transitivity supplier. |
| Nonunital continuity requires only absence of an algebraic identity, without prior continuity of p. | Proved; kernel-checked. | `CStarTriangleEqualityNonunitalContinuity.seminorm_nonunital_lipschitz` assumes no element is a two-sided identity and concludes a Lipschitz bound. |
| Checker exit 0, ALL_CHECKS_OK; survivor counts 65/1/481, perturbation 256/257, and rational nine-corner reconstruction. | Computed. | The pinned experiment above, with its command, exit code and SHA-256; only its explicitly enumerated finite scope is claimed. |
| The first, norm-parallelism clause remains outside this target. | Open. | `claim` and `result` concern TEA pairs; neither states a parallelism-only classification. |
| Arbitrary complex C*-algebra TEA clause, including zero algebras and no continuity assumption. | Proved; kernel-checked. | `CStarTriangleEqualityPreservers.result : claim` has the unchanged source conclusion. |
| The stronger finite complex seminorm theorem allows zero scale and only forward TEA additivity. | Proved; kernel-checked. | Private `CStarTriangleEqualityPreservers.seminorm_rigidity` gives $\exists c\ge0,\ \forall a,\ p(a)=c\|a\|$ on every complex C*-algebra. |
| Joint localization needs no separability, countable global approximate unit, or strictly positive element. | Proved; kernel-checked. | `CStarTriangleEqualityHereditary.seminorm_cross_scale_of_continuous` uses private `exists_joint_local_corner` for the chosen pair; none of the three additional hypotheses appears. |
| Arbitrary real C*-algebras, arbitrary non-C*-Banach spaces, and parallelism-only preservers. | Open. | No extension to these classes is asserted by the delivered statements. |

### What the settlement shows

The decisive mechanism is seminorm rigidity: complex phase geometry constrains two-coordinate sections, the unital spectral and convex-hull estimates fix the norm scale, and nonunital continuity plus joint local identity corners extends that scale to the entire algebra. The stronger seminorm theorem allows zero scale and needs only forward preservation; bijectivity is used to obtain the source's nonzero scalar and surjective isometry.

The source's restricted TEA conclusions follow within the arbitrary-algebra conclusion. Its parallelism and operator-subspace classifications retain their own hypotheses and are not replaced by this settlement. Extensions to real algebras, general Banach spaces or parallelism alone remain open here.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The bounded screen is the one in #27007. The experiment supports the stated finite calculations only. Four-slot escape registration remains unfinished in #27516.
