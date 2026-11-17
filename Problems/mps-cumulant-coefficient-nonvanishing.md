---
slug: mps-cumulant-coefficient-nonvanishing
bibkey: mansanarez2024mmse
doi: 10.1109/TIT.2024.3466566
url: https://arxiv.org/abs/2311.04831v2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.result
---

# Universal cumulant-coefficient nonvanishing fails

## Problem

Paul Mansanarez, Guillaume Poly and Yvik Swan, *Derivatives of entropy and the MMSE conjecture*, arXiv:2311.04831v2, Remark 3.31 (PDF p. 24), asks:

> “Let X be a symmetric random variable determined by its moments. Then X verifies \eqref{Hypostar}.”

The referenced condition in Theorem 2.12 is $a_{2m}(K_2(X),\ldots,K_{2m-1}(X))\ne0$ for every $m\ge3$. The source and literal conventions are fixed by [#24312](https://github.com/the-omega-institute/trureturing/issues/24312). The [Library note](../Library/Estimation/mansanarez2024mmse.md) identifies the version and journal DOI.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Definition 2.1, symmetry in law | `SMD`, reflection invariance of a real measure | Equality of laws |
| Moments of every order | `AllMoments` | Integrability of every natural power |
| Determined by positive-order moments | `SMD`, uniqueness among probability laws with all moments | No MGF assumption |
| Definition 2.3, logarithmic characteristic-function cumulants | `cumulant` | Principal logarithm near characteristic-function value one; real part of the complex expression |
| Definitions 3.7–3.8, Lemma 3.4 | `shiftDerivative`, `sourceL`, `sourceH`, `sourceA`, `IsSourceSequence` | Initial values at 2 and 3, recurrence for all $n\ge3$ |
| Linear coefficient $a_n$ of $T_n$ in $R_{n+1}$ | `linearCoefficient`, `coefficientForm` | Terms with exponent exactly one, with that exponent erased |
| Every $m\ge3$ and every SMD law | `claim` | Probability guard, all recurrence sequences, all real laws |
| Existence of the source sequence | First conjunct of `claim` | Prevents vacuous universal quantification; the refutation uses a sequence supplied by this conjunct |
| Refutation | `result` | Literal negation of the closed proposition `claim` |

`linearCoefficient` is a total coefficient extractor. Definition 3.6's affine decomposition applies only on its source domain; an arbitrary polynomial need not be affine in the selected variable. The settlement uses the recurrence polynomials and does not assert that decomposition for all multivariate polynomials. No density, non-Gaussianity, positive-variance or nonzero-cumulant restriction is added to the universal claim.

## Motivation

The source proposes universal nonvanishing as a sufficient route to the MMSE injectivity conjecture for symmetric moment-determinate laws. An actual probability law with cancellation tests whether realizability of cumulants enforces this algebraic condition.

## Gap

The bounded literature screen in #24312 found no explicit prior settlement of Remark 3.31 in the inspected arXiv source, later-author papers, citation searches, MathOverflow and repository records. The screen distinguishes classical Gaussian and zero-fourth-cumulant degeneracies from the witness here, whose second, fourth, sixth and eighth cumulants are nonzero. Literature completeness is `ASSUMED-UNVERIFIED`.

The journal DOI metadata identifies *IEEE Transactions on Information Theory* 70(11), 7647–7663 (2024). The final journal text was not read in that screen; the statement addressed here is the arXiv v2 remark.

## Route

All private helper names below belong to the settling module's `MPSProbe` namespace.

For $0<p<1$, `law` is the probability measure with masses $p/2$, $1-p$ and $p/2$ at $-1$, $0$ and $1$. `law_probability`, `law_allMoments`, `law_symmetry` and `law_determinate` establish its probability, symmetry and moment determinacy. The determinacy proof uses the nonnegative polynomial $x^2(x^2-1)^2$: equality of moments forces any competing law onto the same three-point support, after which total mass, first moment and second moment determine its masses.

`law_cumulants` gives

$$K_2=p,\quad K_3=K_5=0,\quad K_4=p-3p^2,\quad K_6=p-15p^2+30p^3,\quad K_8=p-63p^2+420p^3-630p^4.$$

`source_coefficients` extracts the coefficients of the actual recurrence through $R_{11}$. On the symmetric law these evaluate to

$$a_6=-140K_4^2,\qquad a_8=-1008K_4K_6,\qquad a_{10}=-132(21K_6^2+20K_4K_8).$$

`root_exists` supplies a root $p\in(1/100,1/20)$ of

$$P(p)=56700p^4-56700p^3+18165p^2-1950p+41.$$

`root_cancellation` gives $21K_6^2+20K_4K_8=p^2P(p)=0$; `root_signs` gives $K_2,K_4,K_6>0$ and $K_8<0$. `counterexample` combines these properties with $a_6<0$, $a_8<0$ and $a_{10}=0$. `result` applies the alleged universal condition at $m=5$ to this same measure.

## Falsifier

The claim uses characteristic-function cumulants, not raw MGF derivatives. All probability, integrability and moment-determinacy properties concern the same three-point law. The cancellation has nonzero $K_4$, $K_6$ and $K_8$, so it does not depend on a Gaussian or zero-fourth-cumulant degeneracy. The source sequence is obtained from the existence conjunct of the asserted proposition; the contradiction uses its universal nonvanishing clause.

The source's Remark 1.5 prints $-210T_3T_6$ in $a_6$. The recurrence gives $-210T_3T_5$ instead. Both vanish when $K_3=0$, and the proof uses the recurrence rather than the printed mixed-term index.

## Evidence

The canonical module is `D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.lean`; its public theorem `result` proves the negation of `claim`. The definitions and result have their full formulas in the corresponding Blueprint Scribe. Generality is `I`; admission is `open-problem-resolution (#24312; Refuted)`; utility is a certified instance with `basis=refutes`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other public theorems or owner publications, and no Reg module is needed.

### Exact experiment

The program is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/121636b8a0d1915f363efab2ca1e2b51388bcba3/docs/reports/mps-cumulant-coefficient-nonvanishing), script `check.py`. The referenced object exists in that commit. Command: `python3 /tmp/op-mps2311-stageb/check.py`, using that object's bytes; exit 0, `ALL_CHECKS_OK`. Script SHA-256: `40cc67434d7d02e32cfb848d528482551e4bef896d2b65a8592daf4528e2cf54`.

The exact tested scope is the source recurrence through $R_{11}$, the displayed $R_2,\ldots,R_6$, the 42 terms of Example 1.6, cumulants through order eight, the quartic and its unique root in $(1/100,1/20)$ by Sturm arithmetic, the scaling identities for $a_6,a_8,a_{10}$, and the symbolic Gaussian-mixture, posterior-variance and normalized-fourth-cumulant certificates. These computations certify algebra, not analytic realization theorems.

## Triage

Tier 1: an auxiliary assertion explicitly posed in the source paper. Settlement: Refuted. Every theorem is classified `bind-only`; consumed private helpers organize the proof, and the named external settlement supplies the admission basis. No ordinary escape-witness admission or digestion atom is asserted.

### What the settlement shows

1. **Proved, kernel-checked:** universal cumulant-coefficient nonvanishing fails at $m=5$ for an actual finite-support SMD law; the preceding $m=3$ and $m=4$ coefficients are strictly negative. Evidence: `MPSProbe.counterexample` gives all three evaluations and the realized measure; `result` negates the universal proposition. `law_SMD` establishes the SMD property, and `root_signs` gives the nonzero cumulants.
2. **Computed:** the pinned checker verifies the quartic, a unique root in $(1/100,1/20)$ by exact Sturm arithmetic, scaling identities and Gaussian-mixture algebra. Evidence: the exact experiment entry above, exit 0 and `ALL_CHECKS_OK`. No interval or parameter range beyond that entry is claimed as a numerical search result.
3. **Proved, kernel-checked, with a source reading:** `MPSProbe.coefficient6` and `MPSProbe.source_coefficients` give $-210T_3T_5-140T_4^2$ for $a_6$. Remark 1.5 prints $-210T_3T_6-140T_4^2$. **Proved in prose:** both mixed terms vanish for a symmetric specialization with $T_3=0$, since each contains that factor; the two expressions then equal $-140T_4^2$.
4. **Open, outside the formal settlement:** Gaussian smoothing, positive analytic strongly log-concave densities and a continuum of normalized counterexamples are not formalized here. The checker verifies their algebraic certificates only. Analytic realization, moment determinacy after smoothing and the continuum claim require their own proofs.
5. **Open, outside the settlement:** the MMSE injectivity conjecture and a characterization of additional assumptions guaranteeing nonvanishing. Theorem 2.12 retains its stated nonvanishing hypothesis; this refutation does not contradict its conditional conclusion. The strict lower-order coefficients survive for this witness; no universal lower-order nonvanishing result is claimed.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The preregistration's final-journal-text access limitation remains; the arXiv v2 statement is the source addressed. The source's other theorems are not independently verified by this result.

Exhaustive helper-deletion and body-reuse probes are not claimed. The finite-support law is formalized; the experiment's smoothing and normalized-family certificates are algebraic evidence only. No theorem about positive analytic strongly log-concave densities or MMSE injectivity is claimed by the Lean module.
