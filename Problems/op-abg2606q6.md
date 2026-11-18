---
slug: op-abg2606q6
bibkey: aouichaouibuchalagarcia2026mpartial
doi: 10.48550/arXiv.2606.12865
url: https://arxiv.org/abs/2606.12865v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.result
---

# The prescribed inverse need not admit a common inner product

## Problem

Aouichaoui, Buchała and Garcia, *On m-partial isometries: spectra, weighted shifts, and similarity*, arXiv:2606.12865v1, Question 6, page 17, ask: “If T is a 2-partial isometry, is 2T∗ − T∗²T the Moore–Penrose inverse of T with respect to some inner product?” The source is attested in [the Library note](../Library/HilbertOperators/aouichaouibuchalagarcia2026mpartial.md); [#27062](https://github.com/the-omega-institute/trureturing/issues/27062) fixes the full assertion and conventions.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Complex Hilbert space and bounded operator | `claim` quantifies over `H : Type`, its original norm, complex inner product and completeness, and `T : H →L[ℂ] H` | The original adjoint stays fixed. |
| A 2-partial isometry | `IsMPartialIsometry 2 T`, using the alternating operator sum `beta` | Includes the permitted source order $1\le m$. |
| The prescribed inverse | `candidateInverse T` | Exactly $2T^*-(T^*)^2T$. |
| With respect to some inner product | One `InnerProductSpace.Core ℂ H` | A positive definite form on the same vector space, with no norm-equivalence assumption. |
| Moore–Penrose inverse | `penroseIn` | $TST=T$, $STS=S$, and symmetry of both $TS$ and $ST$ in the same form. |
| Negative answer | `result : ¬ claim` | Refutes the entire universal assertion. |

## Motivation

A generalized inverse can satisfy the two algebraic Penrose equations while its two associated idempotents have no common symmetrizing positive definite form. Separate inner products for those idempotents do not provide the single inner product Question 6 requires.

## Gap

The literature screen recorded in #27062 found no answer in the inspected source version, accessible later papers by the authors, indexed citing works, relevant generalized-inverse literature, MathOverflow, Zenodo, MathDB and formalization catalogs. The finite-dimensional repository predicate `FiniteMoorePenroseInverse.IsMoorePenroseInverse` states the four conditions for the installed inner product; it is not on this module's dependency path and does not express the independently chosen form in the unrestricted claim. Literature completeness and priority are `ASSUMED-UNVERIFIED`.

## Route

The module has `generality: G` and `admission_basis: open-problem-resolution (#27062; Refuted)`. Its theorem proofs are classified `bind-only` after expanding the same-delivery helpers; the external named-problem settlement is the admission basis. Its certified-instance utility refutes `claim` through `result`.

For every real $r\ge2$, put $a=\sqrt{2-1/r}$, $b=(r-1)/\sqrt r$ and $T_r=\begin{pmatrix}a&0\\b&0\end{pmatrix}$. The private `family_parameters` proves $a,b>0$, $a^2+b^2=r$ and $a^2r=2r-1$. The private `family_partial` verifies the source operator equation. With the fixed $S_r=\operatorname{candidateInverse}(T_r)$, the private `q_apply` and `p_basis` determine $S_rT_r$ and $T_rS_r$. The private `incompatible_core` excludes a common form. The private `family_refutes` combines these conclusions, and `result` uses $r=25$.

## Falsifier

A common positive definite form would make the coordinate vectors orthogonal because $S_rT_r=\operatorname{diag}(1,0)$. Symmetry of $T_rS_r$ would then force $2abp=ab(2-r)q$ for their squared lengths $p,q>0$. Its left side is positive and its right side nonpositive for $r\ge2$. The contradiction includes $r=2$ and permits every complex positive definite Core, not just real diagonal matrices chosen in advance.

## Evidence

The kernel-checked settling declaration is `D5.S3.Quantum.MatrixAnalysis.MPartialIsometryCommonMetricInverseRefutation.result`; its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. All imports are pinned Mathlib; no D5 prerequisite is imported.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The exact experiment is [m-partial-isometry-common-metric-inverse at commit 5e1877b04635365ac9b30cc7a9232db960508634](https://github.com/the-omega-institute/trureturing-experiments/tree/5e1877b04635365ac9b30cc7a9232db960508634/docs/reports/m-partial-isometry-common-metric-inverse). The immutable script was retrieved from that revision and run as `python3 /tmp/op-abg2606q6/stageb-97558/check.py`, exit 0, SHA-256 `ea2f2dcd56f5302516d4b877b710518ab281da83b970f6eb52b26291b3f8aa02`. It uses exact rational multiplication and symbolic $r=2+t$ for all real $t\ge0$, and returns `ALL_CHECKS_OK`. The readings below are computation evidence, not additional Lean declarations.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| The binding universal assertion is false with only the three standard axioms. | proved | Kernel-checked `result`. |
| For every real $r\ge2$, $T_r$ is a 2-partial isometry and no Core satisfies `penroseIn` for its fixed candidate inverse. | proved | Kernel-checked private `family_refutes`; its full real parameter range is retained. |
| For arbitrary real diagonal coefficients, $Qe_0=e_0$, $Qe_1=0$ and real off-diagonal coefficients $c>0$, $d\le0$ preclude a common symmetric positive definite Core. | proved | Kernel-checked private `incompatible_core`. |
| Every family member is strict, rank one, nonzero and nonnormal; $TST=T$, $STS=S$, $(TS)^2=TS$ and $(ST)^2=ST$. | computed | The exact experiment above verifies symbolic $r=2+t$, $t\ge0$. These extra properties are not separate Lean theorems. |
| At $r=25$, $T=\begin{pmatrix}7/5&0\\24/5&0\end{pmatrix}$, $S=\begin{pmatrix}-161/5&48/5\\0&0\end{pmatrix}$ and a common metric requires $336p=-3864q$ with $p,q>0$. | computed | The same exact checker; rational multiplication is independently checked with `fractions.Fraction`. |
| Each of $P=TS$ and $Q=ST$ admits its own symmetrizing metric. | computed | The same checker verifies $Q=Q^*$ and $WP=P^*W$ for $W=P^*P+(I-P)^*(I-P)$, and the positive-definiteness identity. |
| Complete characterization of the admissible 2-partial isometries and full literature priority. | open | Neither the kernel result nor the screened literature supplies a complete classification or exhaustive priority determination. |

### What the settlement shows

**Proved in this module:** the obstruction is simultaneous symmetry in one positive definite form, as stated by private `incompatible_core` and realized by private `family_refutes`. Failure of symmetry in the original Hilbert structure alone would not suffice. The positive parameter family excludes all independent forms, including the endpoint $r=2$.

**Computed:** the two algebraic generalized-inverse equations and both idempotence identities survive throughout this family. Each idempotent remains individually orthogonalizable; their sets of admissible metrics have empty intersection. These claims have exactly the experiment scope above.

**Proved in prose:** for any idempotent $P$, $W=P^*P+(I-P)^*(I-P)$ is positive definite since $x^*Wx=\|Px\|^2+\|(I-P)x\|^2$ vanishes only when $x=0$, and multiplication using $P^2=P$ gives $WP=P^*W$. Thus the common-form requirement is stronger than individual orthogonalizability.

**Literature reading:** Lemma 2.8 proves the algebraic generalized-inverse identities without asserting this common form. Those identities and the source's earlier results retain their stated scope. Question 6 is presented as a question, not a premise of those results.

**Open:** a complete common-metric criterion for all 2-partial isometries, and a classification beyond this counterexample family. These are follow-up questions rather than statements added to the settling module.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`: shared OpenAlex limits, Semantic Scholar throttling, inaccessible global full-text services and unread journal sources limit the screen. The Mbekhta–Suciu, Garcia–Horn, Arias–Mbekhta and Dixmier leads are not all primary-source verified in the preregistration. Zero indexed matches is not an exhaustive absence claim. No experiment is treated as a Lean proof.
