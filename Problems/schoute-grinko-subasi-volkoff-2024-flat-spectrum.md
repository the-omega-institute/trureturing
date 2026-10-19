---
slug: schoute-grinko-subasi-volkoff-2024-flat-spectrum
bibkey: schoutegrinkosubasivolkoff2024reflections
doi: 10.48550/arXiv.2411.03648
url: https://arxiv.org/abs/2411.03648v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/SGVFlatSpectrum.result
---

# Explicit flat-spectrum probe probabilities

## Problem

E. Schoute, D. Grinko, Y. Subaşı and T. Volkoff, *Quantum programmable reflections*, arXiv:2411.03648v2, Section 4.2.1, Conjecture 4.6:

> The probabilities $q_j$ for $j\in\{(n\bmod 2)/2,\ldots,n/2\}$ in Eq. (181), which define the probe state $\Phi_n$, could be chosen such that $\lVert|v_J\rangle\rVert^2=1/\binom{n+2}{2}$ for every $J\in\{n\bmod 2,\ldots,n-2,n\}$.

Equation (183) is the equivalent system

$$
\frac{2J+1}{\binom{n+2}{2}}
 =\sum_{j\ge J/2}\frac{q_j}{2j+1}
   \left|\sum_{m=-j}^{j}C^{J0}_{jm,j-m}\right|^2.
$$

Issue [#17082](https://github.com/the-omega-institute/trureturing/issues/17082) fixes the doubled-integer Racah convention and this system as the binding statement. The settlement is **Proved** by `D5.S3.Quantum.Measurement.SGVFlatSpectrum.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every copy number $n\ge1$ | `claim` quantifies natural $n$ with $1\le n$ | Exact |
| $j=n/2-k$, $0\le k\le\lfloor n/2\rfloor$ | The finite range in `claim` | Exact reindexing |
| Probabilities | Nonnegativity and the sum equal to one in `claim` | Exact |
| Real Condon–Shortley coefficients | `S` uses the frozen doubled-spin `CG` owner; `equal_spin_coefficient` proves its source Racah expression on the admissible summation inputs | Exact binding convention |
| Coherent sum over magnetic indices | `S` sums $i=0,\ldots,2j$, with $m=j-i$ | Exact |
| $J\le n$ of parity $n$ | The bound and remainder equality in `claim` | Exact |
| Terms with $2j\ge J$ | The conditional inside the finite sum | Exact |
| Flat spectrum (182) | The equality (183) in `claim`; source Eq. (181) divides by $2J+1$ | Source algebraic equivalence |

Integer division inside Racah's formula is Euclidean division; factorials use `Nat.factorial` after `Int.toNat`. Natural subtractions are truncated, and the summation guards preserve their intended ranges. The coefficient owner `DampedSpinKernelPositivityRefutation.CG` and this module have generality I. `S` calls the owner in doubled-integer argument order; the Scribe displays the source Racah expression. Inside `equal_spin_coefficient`, the square-root product and summation-range correspondence establish equality on every admissible summation input.

## Motivation

A flat spectrum makes the source's probe-state entropy and program-dimension argument explicit. The probabilities have a uniform formula for every copy number:

$$
q_{n/2-k}=\frac{(n-2k+1)^2\binom{2n-2k+1}{n-k}\binom{2k}{k}}
 {4^n\binom{n+2}{2}}.
$$

## Gap

The source v2 states Conjecture 4.6 and reports numerical solutions through $n=60$. The source and Grinko's 2025 thesis were read for the preregistration; no settlement was found. Din, *Letters in Mathematical Physics* 5 (1981), gives a different sum rule. No prior proof or explicit probabilities were found in the inspected literature. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The proof uses the coherent sums directly. Extracting the common square root in Racah's formula gives a rational binomial convolution. Geometric power series evaluate this convolution; the private lemma `S_sq_closed` proves

$$
S(J+2r,J)^2=
\frac{(2J+1)4^J(J+r)!^2(2r)!}{r!^2(2J+2r+1)!}.
$$

The private lemmas `W_sum` and `Q_sum` establish two finite factorial summation invariants by telescoping certificates and induction. `explicitQ_sum` uses the normalization invariant. `system_equations` uses the kernel invariant after cancellation and reflection of a finite index. `result` assembles the distribution, normalization and all equations. The polynomial connection formulas are outside this proof's dependency path.

## Falsifier

The settlement would fail to match the source if the coefficient convention, coherent sum, parity, allowed spin range, or probability normalization changed. The coefficient correspondence in `equal_spin_coefficient`, the displayed source expression and the predicate `claim` retain all five. The existential probability function is constrained only on its active finite range; its values outside that range have no uniqueness claim.

## Evidence

The formal source is [SGVFlatSpectrum.lean](../D5/S3/Quantum/Measurement/SGVFlatSpectrum.lean), with its [Blueprint](../Blueprint/D5/S3/Quantum/Measurement/SGVFlatSpectrum.md). Its public declarations are `S`, `claim`, `explicitQ` and the single theorem `result`. The admission basis is `open-problem-resolution (#17082; Proved)`; utility is `none` because the proof consists of uniform symbolic identities and a construction for all $n$, without a bounded enumeration or fixed numerical certificate.

The imports reuse `DampedSpinKernelPositivityRefutation.CG`, `Racah.deltaSq` and `AlternatingFactorialSum.opposite_inv_series_mul`. There are no supporting modules or owner publications in this delivery. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The escape audit of `result` is unfinished under [#17668](https://github.com/the-omega-institute/trureturing/issues/17668). A typed dependent-family attempt does not supply the source occurrence selection and complete validated binding evidence. No valid Reg mirror is delivered, and no `declared_validated` registration is claimed.

### Experiment

The program and data are in the [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/35c22679b731c75b7c622a521f50fff7316d4ae3/docs/reports/schoute-grinko-subasi-volkoff-2024-flat-spectrum-probe).

Command: `python3 /Users/auric/trureturing-experiments/docs/reports/schoute-grinko-subasi-volkoff-2024-flat-spectrum-probe/check.py`; exit 0, `ALL_OK`. The committed `check.py` has SHA-256 `c4d55836cc7be3e9ac78794aaf07af4a27b547b97768ab6f94088f7bef498342`.

The exact SymPy checks cover positivity, normalization, all equations (183) and finite-system uniqueness for $n=1,\ldots,12$; the kernel/Legendre identity for $2j=0,\ldots,12$; the positive Gegenbauer/Chebyshev connection for $n=0,\ldots,14$; and the doubled-integer Racah formula against SymPy Clebsch–Gordan coefficients in 2,924 cases with doubled spins at most 6, with zero mismatches. These are finite computations, not a proof of the corresponding unbounded polynomial identities.

## Triage

### What the settlement shows

- **Mechanism — kernel-checked.** `S_sq_closed` evaluates the coherent kernel. `W_sum`, `Q_sum`, `explicitQ_sum` and `system_equations` prove the factorial summation invariants, normalization and every flat-spectrum equation. Their scope is uniform in the natural parameters.
- **Polynomial interpretation — computed in the stated finite ranges; unbounded connection identities open in Lean.** The Legendre system is triangular by its index bounds and nonzero diagonal, as derived below. The interpretation of the explicit probabilities as positive Gegenbauer-to-Chebyshev connection coefficients is checked for $n=0,\ldots,14$ by the experiment. It is not a kernel-checked declaration of this module, and is not needed by `result`.
- **Strength — kernel-checked.** `explicitQ_pos` proves strict positivity for every natural $n$ and $k\le\lfloor n/2\rfloor$; `explicitQ_sum` proves normalization for every natural $n$; `system_equations` proves all admissible equations. `result` provides the required distribution for every $n\ge1$.
- **Consequences — source-paper arguments with their conjecture premise discharged.** Corollary 4.7's entropy formula and the qubit program-dimension lower bound in Theorem 4.10 no longer require Conjecture 4.6 as an additional assumption: substitute the proved existence statement into the source's arguments. Those entropy and dimension arguments are not Lean declarations in this module; the other hypotheses and scope of the source results remain in force.
- **Uniqueness — proved in prose on the active finite range; open in Lean.** Order the equations by $J=n,n-2,\ldots,n\bmod2$ and probabilities by $k=0,1,\ldots,\lfloor n/2\rfloor$. The equation indexed by $J=n-2r$ contains exactly $k\le r$. Its diagonal coefficient is $S(J,J)^2/(J+1)>0$, because the displayed kernel formula at $r=0$ has positive factorial factors. Back substitution therefore determines each probability uniquely. This does not determine values of a function outside the active range, and no uniqueness theorem is part of `claim` or `result`.
- **Experiment — computed.** The experiment entry gives the pinned program, exact scope, command, exit code and SHA-256. It independently checks the explicit probabilities and conventions in those finite ranges.
- **Literature — literature reading.** The source v2, Grinko's 2025 thesis and the inspected sum-rule references yielded no prior settlement or explicit probabilities. Completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness, complete citation enumeration and the absence of a settlement outside the inspected sources are `ASSUMED-UNVERIFIED`. The unbounded polynomial identities, the entropy and program-dimension derivations, and active-range uniqueness are not formalized by this module. Escape registration remains unfinished under #17668. None of these is an extra premise of the Lean theorem `result`.
