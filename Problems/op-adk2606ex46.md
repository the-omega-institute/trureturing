---
slug: op-adk2606ex46
bibkey: alstadduffkatzman2026segre
doi: 10.48550/arXiv.2606.31965
url: https://arxiv.org/abs/2606.31965v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/FlatlandImageEquations.result
---

# Alstad–Duff–Katzman Example 4.6 set-theoretic image equations

## Problem

Example 4.6 asks whether, for $n>8$, the eight-point constraints in Equation (38) and the Segre-determinantal minors give set-theoretic equations for the closed image of the two-camera map. The formal claim is the equality

$$
\forall n\, (9\le n)\to\forall p\,,\quad p\in\operatorname{imageClosure}(n)\iff\operatorname{equations}(p).
$$

The delivered settling declaration is `D5.S3.Geometry.FlatlandImageEquations.result`, whose frozen module statement pin is `sha256:76c15a0bc6fd3f7f52d9013499ba9a3b86decf6d006404fcfef9d3ee3cc20e57`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every natural $n>8$ | `result` quantifies `n : ℕ` with `9 ≤ n` | Exact threshold form |
| Every configuration of two image points for each world point | `Configuration n` and the universal `p` binder | Exact carrier and quantifier |
| Closed image of the actual rational imaging map | `imageClosure n` over `ImagingDomain n` and multihomogeneous vanishing | Actual domain and closure retained |
| Segre-determinantal minors and eight-point constraints | `equations p` | Both conjuncts retained |

## Motivation

The source separates the set-theoretic question from the harder scheme-theoretic, radicality, ideal-generator and universal-Gröbner-basis questions. The settlement proves the first question for every $n\ge9$, including rank-one kernels, epipoles, coincident cameras and lower-rank cameras wherever the source map is defined.

## Gap

The source and the bounded literature screen did not contain an exact all-$n$ equality including the rank-one boundary. The literature screen is bounded and its completeness is `ASSUMED-UNVERIFIED`.

## Route

The forward implication proves every defining minor vanishes on the actual image and therefore on its multihomogeneous closure. The reverse implication extracts a nonzero singular Segre-kernel vector from the equations, reshapes it into a bilinear form, reduces by invertible coordinate transport to rank-one and rank-two normal forms, and uses the diagonal rank-two closure together with the simultaneous polynomial deformation to return to the original configuration. The helpers quantify over arbitrary finite index families; the result uses the complex field and every natural $n$ with the stated hypothesis.

## Falsifier

A configuration satisfying `equations` but outside `imageClosure`, or a configuration in the closed image violating one of the two equation families, would refute `result`. Scheme-theoretic equality, radicality, ideal generators and universal Gröbner bases are separate questions.

## Evidence

The kernel-checked declarations are `D5.S3.Geometry.FlatlandImageEquations.equations_imply_imageClosure`, `D5.S3.Geometry.FlatlandImageEquations.imageClosure_implies_equations` and `D5.S3.Geometry.FlatlandImageEquations.result`. Their accepted axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The Flatland modules use the following frozen repository declarations directly in the cofactor construction and proofs.

- `D5/S3/Arith/Lattices/CofactorKernel.cofactor` (`sha256:3166337f4d6d020e4b4c7683bf2c13d3987b090b3e99f722181e1790e47736fd`)
- `D5/S3/Arith/Lattices/CofactorKernel.augment` (`sha256:1b8ea5d92050b0800467ee3b6cec64a706ba07779c3d671002dadd0d4b97013c`)
- `D5/S3/Arith/Lattices/CofactorKernel.augment_succ` (`sha256:788160be84279da0dc13fa6d07028ab8f0ba53ea43b1ecad0e66bab5a6fd4250`)
- `D5/S3/Arith/Lattices/CofactorKernel.det_topRow` (`sha256:8f1dc771b93fd0f1d4e62ca10c9a2411049962bdd64b97ca70d0abccfe7fbee1`)
- `D5/S3/Arith/Lattices/CofactorKernel.cofactor_eq_adjugate` (`sha256:5d6763dae921f641fc4c08348c41dbf11eb06e9acaf299082ec24c39488485c4`)
- `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.cofactor_map` (`sha256:bb65039d475dcf1de876dded4c2107433b2f0c0931042edc05b0320132128700`)

The four-slot escape audit is unfinished for the public audit targets; issue [#30117](https://github.com/the-omega-institute/trureturing/issues/30117) records the missing dependent-family registration evidence. The designated settling result is admitted by `open-problem-resolution (#25719; Proved)`.

The deterministic experiment is [the experiments repository](https://github.com/the-omega-institute/trureturing-experiments/tree/28d9c6e3e55b322c710a12a7614ec04323b6ae33/docs/reports/alstad-duff-katzman-flatland-image-equations) at commit `28d9c6e3e55b322c710a12a7614ec04323b6ae33`. The command `python3 docs/reports/alstad-duff-katzman-flatland-image-equations/check.py` exits `0` with `ALL_CHECKS_OK`; the checked script has SHA-256 `9068c80ca350fc5ecbd98d6c7f572b61885dc3f4441493daecaeb2555acb4659`. Its finite scope is actual-image tests at $n=8,9,10$, rank-one-only kernel examples at $n=9,10$, 88 $E_{00}$ grid pairs, 61 $F_0$ grid pairs and symbolic identities. It supplies computed diagnostics, not an all-$n$ proof.

## Triage

### What the settlement shows

The equations characterize existence of a nonzero singular reshaped Segre-kernel vector, and this condition is equivalent to membership in the variable-camera closed image. The two implication helpers quantify over every natural $n$; the hypothesis $9\le n$ is used only by the final claim, so the helper composition also gives the same characterization for the empty minor families at smaller $n$. The rank-one deformation is uniform over every field and finite index family, while the closure argument delivered here is over $\mathbb C$. The source's other questions about schemes, radicals, generators, Gröbner bases, actual rational-image membership and fixed-camera reconstruction remain outside the result.

| Triage item | Status | Evidence |
| --- | --- | --- |
| Equations characterize a nonzero singular reshaped Segre-kernel vector and this is equivalent to variable-camera closed-image membership. | proved | Kernel-checked `equations_imply_singular_kernel`, `singular_compatible_closure`, `imageClosure_implies_equations` and `equations_imply_imageClosure`. |
| Both implication helpers quantify over every natural $n$; their composition gives the characterization at every $n$, including empty minor families. | proved | Kernel-checked helper statements and the proof of `result`. |
| Normalized rank-one deformation and epipole-complete rank-two closure are checked with the standard axiom closure; they are partial statements unless composed into `result`. | proved | Kernel-checked `normalized_rank_one_closure`, `normalRankOne_closure`, `normalRankTwo_closure` and `singular_compatible_closure`; the composition is used by `result`. |
| The simultaneous deformation is uniform over any field and index family; the closure argument is over the complex field. | proved | Kernel-checked declarations in `FlatlandImageAlgebra` and `FlatlandImageClosure`, with the complex specialization on the live path to `result`. |
| Finite diagnostics and checker status. | computed | `python3 docs/reports/alstad-duff-katzman-flatland-image-equations/check.py`, exit `0`, script SHA-256 `9068c80ca350fc5ecbd98d6c7f572b61885dc3f4441493daecaeb2555acb4659`; scope is the finite set listed in `Evidence`. |
| Scheme-theoretic equality, radicality, ideal generators and universal Gröbner bases. | open | No delivered declaration or cited paper argument settles these stronger questions. |
| Other camera dimensions or fields. | open | The required closure and algebraic-closedness arguments are outside the delivered complex two-camera theorem. |
| Exact rational-image membership and fixed-rank or fixed-camera reconstruction restrictions. | open | Closed-image equality does not imply these separate reconstruction statements. |

## ASSUMED-UNVERIFIED

The literature search is bounded to the sources recorded in preregistration issue #25719 and the cited repository and Mathlib scopes; completeness and worldwide priority are `ASSUMED-UNVERIFIED`. The experiment is finite and deterministic and does not certify the all-$n$ theorem. No claim is made for scheme-theoretic equality, radicality, ideal generators, universal Gröbner bases, other camera dimensions, other fields, the actual rational image or fixed-camera reconstruction.
