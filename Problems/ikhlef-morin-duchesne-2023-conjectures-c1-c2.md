---
slug: ikhlef-morin-duchesne-2023-conjectures-c1-c2
bibkey: ikhlefmorinduchesne2024fusion
doi: 10.21468/SciPostPhys.17.5.132
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.result
url: https://arxiv.org/abs/2312.14837v2
---

# Product formulas for periodic Temperley–Lieb seed recurrences

## Problem

Yacine Ikhlef and Alexi Morin-Duchesne, *Fusion of irreducible modules in the
periodic Temperley–Lieb algebra*, Appendix C, Conjectures C.1 and C.2,
arXiv:2312.14837v2; SciPost Phys. 17, 132, DOI 10.21468/SciPostPhys.17.5.132.
The source note is `D5/L/QuantumContext/ikhlefmorinduchesne2024fusion`.
Preregistration: [#18569](https://github.com/the-omega-institute/trureturing/issues/18569).

Write $[k]=(q^k-q^{-k})/(q-q^{-1})$, $\{k\}=q^k+q^{-k}$ and
$\alpha_z=z+z^{-1}$. Proposition C.1 defines $X^{(p)}_m$ by (C.3)–(C.4):

$$
X^{(p)}_p=1,\qquad
X^{(p)}_{p+1}=\alpha_x+\frac{\alpha_y\alpha_w}{\{p+1\}},
$$

$$
X^{(p)}_{k+1}=\left(\alpha_x+
\frac{\{p\}\alpha_y\alpha_w}{\{k\}\{k+1\}}\right)X^{(p)}_k+
\frac{(\{p\}^2-\{k\}^2)(\alpha_y^2-\{k\}^2)(\alpha_w^2-\{k\}^2)}
{(q-q^{-1})^2[2k-1][2k+1]\{k\}^2}X^{(p)}_{k-1}.
$$

Conjecture C.1 states: “For p ⩾ 1, the function X^{(p)}_m(ω, x, y)
specialised to y = εq^m evaluates to” (C.5):

$$
X^{(p)}_m(w,x,\varepsilon q^m)=(wx)^{p-m}
\prod_{r=-(m-p-1)/2}^{(m-p-1)/2}
(xq^{2r}+\varepsilon w)(\varepsilon q^{2r}+xw).
$$

Proposition C.2 defines $\sigma^{(0)}_{0,m}$ by (C.24)–(C.25):

$$
\sigma_0=1,\qquad \sigma_1=\alpha_x+
\frac{\alpha_y\alpha_w}{\{1\}},
$$

$$
\sigma_{k+1}=\left(\alpha_x+
\frac{2\alpha_y\alpha_w}{\{k\}\{k+1\}}\right)\sigma_k-
\frac{[k]^2(\alpha_y^2-\{k\}^2)(\alpha_w^2-\{k\}^2)}
{[2k+1][2k-1]\{k\}^2}\sigma_{k-1}.
$$

Conjecture C.2 states: “The intermediate seed states σ^{(0)}_{0,m}(w, x, y)
specialised to y = εq^m evaluate to” (C.26), the same product with $p=0$.

### Statement echo

All Lean names in this dossier have prefix
`D5.S3.Quantum.Algebra.PeriodicTemperleyLiebSeedProduct`.

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Complex nonzero $q,x,w$ | `claim` quantifies complex parameters and requires each nonzero | Exact pointwise domain |
| $q$ not a root of unity | Every natural $n\ge1$ has $q^n\ne1$ | All recurrence poles in scope are avoided |
| $\varepsilon=\pm1$ | Sign disjunction in `claim` | Both signs |
| $[k]$, $\{k\}$, $\alpha_z$ | `qbr`, `qcb`, `al` | Literal source expressions |
| (C.3)–(C.4) | `seedX q x y w p n` denotes $X^{(p)}_{p+n}(w,x,y)$ | Three recursion cases, with $k=p+n+1$ |
| (C.24)–(C.25) | `seedSigma` | Independently transcribed three recursion cases |
| Symmetric product | `seedProduct` | $N$ factors, $2r=-N+1+2j$, $0\le j<N$ |
| (C.5), every $1\le p\le m$ | First conjunct of `claim` | $N=m-p$, including $N=0$ |
| (C.26), every $m\ge0$ | Second conjunct of `claim` | $N=m$, including $m=0$ |
| Both conjectures | `result` | Full conjunction; no dropped clause |

The natural subtraction agrees with the source integer difference under $p\le m$.
Natural-to-integer casts express the product exponents. Empty products equal one.
The recurrence definitions are total on complex arguments; the theorem restricts
them to the stated nonzero, non-root domain. No extra hypothesis narrows that domain.

## Motivation

The settling declaration is
`D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.result`.
These evaluations supply the specialized seed values used in the source's
Section 4 discussion of fusion decompositions. Scalar recurrence evaluation is
the formal scope; the representation-theoretic fusion theorem is outside it.

## Gap

Status: **Proved**, relative to the two recurrences in Appendix C.
The complete complex-parameter and natural-index statement is `claim`, proved by
`result`. Its admission basis is `open-problem-resolution (#18569; Proved)`;
generality is `G` and utility is `none`.

The four-slot escape audit of the public theorem `result` is unfinished:
[#20099](https://github.com/the-omega-institute/trureturing/issues/20099).
No `declared_validated` registration is claimed. The missing evidence is a
faithful source reconstruction, whole-family variation, role sensitivity and
actual observational dependence for the unbounded parameter family.

## Route

Set $Q=q^2$, $h=q^{p+1}$ and
$(a,b,c,d)=(h/(yw),hw/y,hyw,hy/w)$, with $T=-\alpha_x$.
`seed_eq_aw` identifies the source recurrence with the monic recurrence `IMDAW.P`.
`IMDDarboux.transform` establishes a coupled recurrence invariant;
`IMDAW.shift_transform` applies it to the shift $a\mapsto aQ$.
For degree $N+1$, the condition $abQ^N=1$ gives `IMDAW.a_vanish`.
`IMDAW.terminal_factorization` then inducts on the terminal degree and yields
one linear factor per shift. `seed_terminal` specializes the parameters and
normalizes the symmetric product. `sigma_eq_seed` identifies the separately
transcribed zero-depth recurrence with `seedX` at $p=0$.

The product-of-integer-powers step uses the frozen declaration
`NikolovSegal.UnitaryField.prod_zpow_base`, owned by
`D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalGeometry`.
The coupled invariant and the terminal induction remain after expanding the
same-module helpers. Algebraic normalization alone does not supply those steps.

## Falsifier

A counterexample would consist of admissible complex parameters and indices
violating either displayed product formula. An incorrect recurrence
transcription would break the source correspondence even if the Lean theorem
compiled. A product assertion for generic $y$ is not part of `claim`.

## Evidence

### Formal evidence

`result` proves both conjectures. All implementation helpers are private;
the only public theorem is `result`. The public definitions are `qbr`, `qcb`,
`al`, `seedX`, `seedSigma`, `seedProduct` and `claim`.
The Scribe displays each complete definition and the expanded result statement.
The axiom closure of every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`.

### Exact experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/9c938126e2a42c193e8fcc5db1abb1c4b2f1f847/docs/reports/ikhlef-morin-duchesne-2024-seed-state-specialisation).
Command from that experiments checkout:
`python3 docs/reports/ikhlef-morin-duchesne-2024-seed-state-specialisation/check.py`.
Exit code: 0. Script SHA-256:
`2212a263301dd747c64b084e29a8b2d0ce2dd3b09ca097f5b1b3bd438903be81`.
The computation uses exact rational arithmetic and seed 20261017.
For each $q\in\{2,3,3/2\}$ it samples four positive rational pairs $(x,w)$,
both signs, $1\le p\le5$ and $p\le m\le p+12$: 1560 C.1 cases.
It checks $0\le m\le12$: 312 C.2 cases, also comparing the $p=0$ recurrence.
There are zero failures. Adding $1/10$ to the off-diagonal coefficient breaks
18 of 18 control cases. The generic-$y$ control differs from the product.
These are finite computed checks, separate from the uniform theorem.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Both source conjectures, uniform in $m,p$ | Proved, kernel-checked `result` | Exact nonzero complex, non-root domain of `claim`; both signs |
| $p=0$ and sigma correspondence | Proved, kernel-checked `seed_terminal` and `sigma_eq_seed` | Every natural terminal degree; sigma is independently defined |
| Generic terminal AW factorization | Proved, kernel-checked `IMDAW.terminal_factorization` | $Q,a\ne0$, `IMDAW.Regular`, $abQ^N=1$; arbitrary $b,c,d,T$ subject to these guards |
| Vanishing and Darboux mechanism | Proved, kernel-checked `IMDAW.a_vanish`, `IMDDarboux.transform`, `IMDAW.shift_transform`, `IMDAW.terminal_factorization` | Terminal coefficient vanishes and repeated shifts yield the product; no factorization of intermediate seed values is asserted |
| Effect on Section 4 | Source consequence, proved in prose relative to Appendix C | Appendix C identifies these evaluations as needed for the fusion decompositions. Substituting the two proved evaluations discharges that evaluation gap; the full fusion theorem is not formalized |
| Roots of unity or finite-horizon pole guards | Open | Removable limits and weakened guards need separate statements and proofs |
| Finite rational checks and controls | Computed, pinned experiment above | Exactly 1560 C.1 and 312 C.2 cases; 18 perturbed controls and one generic-$y$ control |

### Declaration classification

The classification expands same-delivery helpers and stops at frozen owners
or pinned Mathlib. `result` is content, with `IMDAW.terminal_factorization`
on its surviving path through `seed_terminal`. Its direct frozen dependency
after that expansion is `NikolovSegal.UnitaryField.prod_zpow_base`.
The module admission basis is `open-problem-resolution (#18569; Proved)`.

| Declaration | `proof_shape` | `escape_witness` | Direct consumer(s) |
| --- | --- | --- | --- |
| `IMDAW.shift_off` | bind-only | `none` | `IMDAW.shift_transform` |
| `IMDAW.shift_diag0` | bind-only | `none` | `IMDAW.shift_transform` |
| `IMDAW.shift_diag` | bind-only | `none` | `IMDAW.shift_transform` |
| `IMDDarboux.transform` | content | `IMDDarboux.transform` | `IMDAW.shift_transform` |
| `IMDAW.regular_shift` | bind-only | `none` | `IMDAW.terminal_factorization` |
| `IMDAW.regular_den` | bind-only | `none` | `IMDAW.regular_square`, `IMDAW.shift_transform`, `IMDAW.source_initial` |
| `IMDAW.regular_square` | bind-only | `none` | `IMDAW.shift_transform`, `IMDAW.source_step_coefficients` |
| `IMDAW.shift_transform` | content | `IMDDarboux.transform` | `IMDAW.terminal_factorization` |
| `IMDAW.a_vanish` | bind-only | `none` | `IMDAW.terminal_factorization` |
| `IMDAW.terminal_factorization` | content | `IMDAW.terminal_factorization` | `seed_terminal` |
| `IMDAW.a_mul_var` | bind-only | `none` | `IMDAW.diag_symmetric` |
| `IMDAW.diag_symmetric` | bind-only | `none` | `IMDAW.diag_h` |
| `IMDAW.parameter_invariants` | bind-only | `none` | `IMDAW.beta0_h`, `IMDAW.diag_h`, `IMDAW.off_h`, `IMDAW.source_initial`, `IMDAW.source_regular`, `IMDAW.source_step_coefficients` |
| `IMDAW.diag_h` | bind-only | `none` | `IMDAW.diag_source` |
| `IMDAW.off_h` | bind-only | `none` | `IMDAW.off_h_source` |
| `IMDAW.beta0_h` | bind-only | `none` | `IMDAW.source_initial` |
| `IMDAW.beta_source` | bind-only | `none` | `IMDAW.diag_source` |
| `al_diff` | bind-only | `none` | `off_source` |
| `off_denominator` | bind-only | `none` | `off_source` |
| `off_source` | bind-only | `none` | `IMDAW.off_h_source` |
| `power_sub_inv_ne` | bind-only | `none` | `IMDAW.source_step_coefficients` |
| `qcb_al` | bind-only | `none` | `IMDAW.source_step_coefficients`, `qcb_nat` |
| `qcb_nat` | bind-only | `none` | `IMDAW.source_initial` |
| `symmetric_exponent_sum` | bind-only | `none` | `product_linear` |
| `prod_zpow_range` | bind-only | `none` | `product_linear` |
| `product_factor` | bind-only | `none` | `product_linear` |
| `product_linear` | bind-only | `none` | `seed_terminal` |
| `IMDAW.diag_source` | bind-only | `none` | `IMDAW.source_step_coefficients` |
| `IMDAW.off_h_source` | bind-only | `none` | `IMDAW.source_step_coefficients` |
| `qpow_double_minus` | bind-only | `none` | `qbr_pair` |
| `qpow_double_plus` | bind-only | `none` | `qbr_pair` |
| `qbr_pair` | bind-only | `none` | `IMDAW.source_step_coefficients` |
| `IMDAW.plus_den` | bind-only | `none` | `IMDAW.source_initial`, `IMDAW.source_step_coefficients` |
| `IMDAW.source_regular` | bind-only | `none` | `IMDAW.source_initial`, `IMDAW.source_step_coefficients`, `seed_terminal` |
| `IMDAW.source_initial` | bind-only | `none` | `seed_eq_aw` |
| `IMDAW.source_step_coefficients` | bind-only | `none` | `seed_eq_aw` |
| `seed_eq_aw` | content | `seed_eq_aw` | `seed_terminal` |
| `parameter_power` | bind-only | `none` | `seed_terminal` |
| `terminal_ab` | bind-only | `none` | `seed_terminal` |
| `seed_terminal` | content | `IMDAW.terminal_factorization` | `result` |
| `qcb_square` | bind-only | `none` | `sigma_coeff` |
| `sigma_coeff` | bind-only | `none` | `sigma_eq_seed` |
| `sigma_eq_seed` | content | `sigma_eq_seed` | `result` |
| `result` | content | `IMDAW.terminal_factorization` | settling result |

## ASSUMED-UNVERIFIED

Literature completeness and novelty are **ASSUMED-UNVERIFIED**.
The source v2 is the authoritative statement. The literature screen in #18569
reports no settlement in arXiv:2509.11756, 2602.15742, the revised 2302.12782,
2501.19288, 2606.31313v2 and 2308.00614; those later-paper readings are
seat-reported. Koekoek–Swarttouw, arXiv:math/9602214 §3.1, supplies the
classical Askey–Wilson context, not a Lean dependency.
Bounded reuse searches do not certify absence of every equivalent theorem.
The unfinished escape audit is #20099; a linked issue is not a validated registration.
