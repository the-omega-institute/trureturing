---
slug: bera-sarbicki-chruscinski-2023-gcd3-equator
bibkey: berasarbickichruscinski2023optimizedmaps
doi: 10.48550/arXiv.2309.09621
url: https://arxiv.org/abs/2309.09621v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.result
---

# The gcd-three equator formula for optimized positive maps is false

## Problem

A. Bera, G. Sarbicki and D. Chruściński, *Optimizing positive maps in the matrix algebra M_n*, arXiv:2309.09621v1, Conjecture 2, Eq. (13), asserts that when $1\le k<n$, $\gcd(n,k)=3$, and $v=\alpha v_1+\beta v_2$ with $|\alpha|^2+|\beta|^2=1$ and $|\alpha|=|\beta|$, the greatest nonnegative parameter for which $\tau_{n,k}-\lambda H_v$ is positive is

$$n-k+\frac{n-3}{n-2k/3}.$$

The assertion is **Refuted**. The [Library note](../Library/QuantumContext/berasarbickichruscinski2023optimizedmaps.md) gives the source statements and locators. [Preregistration #19282](https://github.com/the-omega-institute/trureturing/issues/19282) specifies the external named problem and the source conventions.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Eqs. (3)–(5), diagonal projection and cyclic shift | `tau` | The diagonal projection composes Mathlib's `diagonalLinearMap` and `diagLinearMap`; the shift has entry one exactly at $i=j+1$ in `Fin n`; conjugation uses `mulLeft` and `mulRight`. |
| Eq. (6), $H_v(X)=(vv^*)\circ X$ | `hadamardMap` | The rank-one matrix is `Matrix.vecMulVec v (star v)`; multiplication is entrywise. |
| Eqs. (10)–(11), the two Fourier vectors | `vr n 1`, `vr n 2` | Coordinate $j$ is $\exp(2\pi i rj/3)/\sqrt n$. |
| Greatest positivity parameter | `IsLambdaMax` | `IsGreatest` requires attainment and maximality among nonnegative real parameters, using the frozen `FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive`. |
| $1\le k<n$, $\gcd(n,k)=3$ | The first three hypotheses of `claim` | Natural-number parameters with `NeZero n`. The instance excludes dimension zero; the source hypotheses already force positive dimension. |
| $|\alpha|^2+|\beta|^2=1$, $|\alpha|=|\beta|$ | The coefficient hypotheses of `claim` | Complex coefficients and real norms. |
| Eq. (13) | The conclusion of `claim` | The displayed real parameter is used literally. |
| Negation of the universal assertion | `result` | The witness has $n=6$, $k=3$, $\alpha=\beta=1/\sqrt2$. |

## Motivation

Subtracting a rank-one Hadamard map from a positive map asks how much positivity remains. The proposed equator formula would determine that threshold on the equal-norm coefficients of the two-dimensional Fourier subspace.

## Gap

The literature inventory recorded in #19282 screens arXiv:2309.09621v1, later works 2312.02814, 2503.04158, 2510.06863 and 2604.18600, the predecessor 2207.03821v2 (Proposition 2, even $n$ and $k$), Yamagami, *Proc. AMS* 118 (1993), and the Chruściński–Sarbicki survey arXiv:1402.2413, §7. No settlement of this obstruction is identified within that inventory. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Set $n=6$, $k=3$, $\alpha=\beta=1/\sqrt2$, and $q=(1,0,0,1,0,0)$. Let

$$R=\frac1{60}I+\frac{27}{60}qq^*.$$

The matrix $R$ is positive semidefinite by closure under nonnegative scalar multiplication and addition, using the identity and a rank-one positive semidefinite matrix. The conjectured parameter is $15/4$. Only coordinates $0$ and $3$ enter the quadratic form at $q$. At those coordinates the Fourier coefficients give $v_i\overline{v_j}=1/3$. Finite matrix normalization yields

$$q^*\tau_{6,3}(R)q=\frac{59}{30},\qquad q^*H_v(R)q=\frac{11}{18}.$$

Consequently

$$q^*\bigl(\tau_{6,3}-(15/4)H_v\bigr)(R)q
=\frac{59}{30}-\frac{15}{4}\frac{11}{18}
=-\frac{13}{40}<0.$$

Positivity would require this output to be positive semidefinite, hence its quadratic form to be nonnegative. This contradicts attainment in `IsGreatest` at the conjectured parameter.

## Falsifier

The conclusion requires the source's shift direction, the diagonal projection after conjugation, entrywise Hadamard multiplication, and the source's two Fourier vectors. Reversing the optimization direction or replacing positivity by a condition on a different map would change the assertion. The statement echo and the expanded Scribe formulas fix these conventions.

## Evidence

The canonical module is [BeraSarbickiChruscinskiOptimizedMaps.lean](../D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.lean), with the [Blueprint mirror](../Blueprint/D5/S3/Quantum/QuantumChannels/BeraSarbickiChruscinskiOptimizedMaps.md).

The sole source-authored public theorem `D5.S3.Quantum.QuantumChannels.BeraSarbickiChruscinskiOptimizedMaps.result` proves the negation of `claim`. Its private certificate lemmas have named consumers on that proof's dependency path. The compiler also generates the congruence companion `IsLambdaMax.congr_simp`; this is not an additional source-authored theorem. The settling proof shape is `bind-only`: upstream facts, instantiation and finite normalization. Its admission basis is `open-problem-resolution (#19282; Refuted)`; no strict escape witness is claimed. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Universal Eq. (13) | **Proved in Lean (refutation):** `result` supplies the $(6,3)$ counterexample. |
| Failure mechanism | **Proved in Lean:** private `R_psd`, `tau_quadratic`, `hadamard_quadratic` and `negative_quadratic`, consumed by `result`, establish a positive semidefinite input and a negative output quadratic form at the asserted parameter. |
| Exact $\lambda_{\max}=3$ | **Open:** the experiment's equal-norm values at the three stated phases are numerical estimates only. |
| Positivity at the pole or refutation of Eq. (12) | **Open:** the experiment gives a numerical estimate $3.7500$ at $(6,3)$; the module proves no positivity bound there. |
| Interval assertion of Conjecture 2 | **Open:** the counterexample to Eq. (13) does not refute the interval assertion. |
| Unbounded compression family | **Open:** the experiment checks 31 pairs with $n\le30$; there is no uniform Lean theorem for all dimensions. |
| Full Fourier vector equality outside the consumed support | **Open as a formalization:** the proof uses only coordinates $0$ and $3$ of its six-dimensional witness. |
| Exact pole and whole Bloch-ball thresholds; $\gcd(n,k)>3$ (Conjecture 4) | **Open:** no such conclusion is asserted by the module. |
| Consequences for other source assertions | **Proved in prose:** any conjunction containing Eq. (13) is false because that conjunct is false. The repeated equator assertion in Conjecture 3, Eq. (36), has the same source expression. No consequence for Eq. (12), the interval assertion, or the source's independently proved results is claimed. |
| Delivery | One settling module, five public definitions, one source-authored public result; all nine private theorem helpers are consumed. No general module or additional source-authored public theorem. The designated refutation result is exempt from four-slot registration. |
| Exact rational experiment | **Computed:** the script below checks trace one, positive definiteness and the output value $-13/40$ for the $(6,3)$ input. |
| Finite compression experiment | **Computed:** the script below checks all 31 admissible pairs with $\gcd(n,k)=3$ and $n\le30$ at the conjectured value. |
| Numerical optimization experiment | **Computed:** the script below reports $3.0000$ at equator phases $0$, $\pi/3$ and $\pi$, and $3.7500$ at the pole for $(6,3)$; these are numerical estimates only. |
| Literature status | Partial inventory listed in Gap and #19282; no settlement identified in that inventory. Completeness is `ASSUMED-UNVERIFIED`. |
| Remaining mathematical goals required for this settlement | None: `result` negates the entire Eq. (13) universal assertion. The open items above are beyond that settlement. |

### Experiment

[The experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/0708c86148197df4a7e193bcd4b38e1c29e4d398/docs/reports/bera-sarbicki-chruscinski-2023-gcd3-equator) contains `check.py`, SHA-256 `b19ff7937b9e98a5fb1ab54df398c45010d2e5703b0522571971377f9471db6c`. Command: `python3 /Users/auric/trureturing-experiments/docs/reports/bera-sarbicki-chruscinski-2023-gcd3-equator/check.py`, using the script with the pinned SHA-256; exit 0, `RESULT PASS`.

It checks the exact rational $(6,3)$ witness, including trace one, positive definiteness and the value $-13/40$. Its residue-class compression checks nonpositivity at the conjectured value for all 31 admissible pairs with $\gcd(n,k)=3$ and $n\le30$. Numerical random-restart minimization and bisection at $(6,3)$ report $3.0000$ for equal-norm coefficients at phases $0$, $\pi/3$ and $\pi$, and $3.7500$ at $\alpha=1,\beta=0$. These numerical optimization values certify no exact global maximum.

The nearest unexcluded statement is the interval assertion together with a different equator threshold. The experiment supports candidates for that threshold only on its stated finite scope; this is not a general theorem.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source and literature inventory are those in #19282; a partial citation screen cannot establish global absence of a prior settlement. Numerical optimization is not a proof of exact maxima, and finite compression checks do not establish an unbounded family.
