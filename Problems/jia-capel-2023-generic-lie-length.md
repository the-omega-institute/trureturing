---
slug: jia-capel-2023-generic-lie-length
bibkey: jiacapel2024genericlielength
doi: 10.22331/q-2024-05-02-1331
url: https://arxiv.org/abs/2301.08241v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/GenericLieLength.result
---

# Generic logarithmic Lie-length of su(n)

## Problem

Yifan Jia and Angela Capel, *A generic quantum Wielandt's inequality*, arXiv:2301.08241v3, Quantum 8 (2024) 1331, Conjecture 6, p. 19:

> Let $S$ be a random Lie-generating set of $\mathfrak{su}(n)$, then $\mathtt{Lie}\ell(S)=\Theta(\log n)$ almost surely.

Definition 3, p. 17, counts generator letters in right-nested brackets. It takes $U_1=\mathrm{span}(S)$, $U_{k+1}=\mathrm{span}[S,U_k]$, and the least positive $L$ for which the cumulative layers span the Lie algebra. The number $g\ge2$ of generators is fixed independently of $n$. The random law is Lebesgue measure in real linear coordinates on $\mathfrak{su}(n)^g$; the almost-everywhere assertion also applies to probability laws absolutely continuous with respect to this measure (by the definition of absolute continuity).

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| $\mathfrak{su}(n)$ | `GenericLieLengthFiltration.suSet` | Real submodule with $X^*=-X$ and $\operatorname{tr}X=0$. |
| Right-nested brackets and cumulative layers | `layer`, `lieLength`, `rightWordEval`, `rightSpan` | `layer` at zero is bottom; at one it is the real span of the generators. |
| Fixed generator count | `GenericLieLength.claim` | For every $g\ge2$, positive constants precede the dimension quantifier. |
| Dimensions | `claim` | Every $n:\mathbb N$ with $2\le n$; dimension and Lie-length are cast to $\mathbb R$ in the estimates. |
| Random, almost surely | `suCoordinateMap`, `suPairMeasure`, `claim` | `Measure.map` of coordinate Lebesgue measure; a null exceptional set at each dimension. |
| $\Theta(\log n)$ | `GenericLieLength.result` | $c_g=1/\log(g+1)$ and $C=32/\log 2$ satisfy both inequalities. |
| Lie-generating | `GenericLieLength.ae_span_top_of_witness` with the explicit spanning pair | Generation follows almost everywhere; it is not an extra hypothesis that narrows the random law. |

The layer recurrence advances from $k+1$ to $k+2$, so the successor rule is asserted for $1\le k$. Matrix units are Mathlib's `Matrix.single`. The dimension quantifier and real casts are as stated in the table. These conventions avoid applying a positive-layer recurrence to the zero layer.

## Motivation

The settling declaration is `D5/S3/Quantum/Algebra/GenericLieLength.result`, with admission basis `open-problem-resolution (#15954; Proved)`. The source identifies logarithmic-length spanning words as its missing ingredient. Such a bracket-order bound bears on unitary control and the BCH expansion; it supplies no conditioning, accuracy or stable gate-synthesis guarantee.

## Gap

The source's determinant argument transfers a single spanning tuple to almost every tuple. A dimension-uniform explicit tuple with logarithmic word length supplies the missing construction. Preregistration: [#15954](https://github.com/the-omega-institute/trureturing/issues/15954).

The four-slot escape audit of all 19 public theorems is unfinished: [#16180](https://github.com/the-omega-institute/trureturing/issues/16180). The dependent-family statements still require faithful observation readouts, exact source-selection bridges, variation, sensitivity and observational-dependence evidence. No Reg mirror is delivered.

## Route

For dimension $n\ge2$, use the binary heap on vertices $1,\ldots,n-1$ and the anchor edge $0$--$1$. Give the root colour zero and give its two children the other two colours recursively modulo three. Set the diagonal energies to $7$ at the anchor and $0,1,3$ according to colour elsewhere. Subtract the mean energy to obtain a traceless diagonal matrix $A$; let $B$ be the adjacency matrix. The generators $iA,iB$ are traceless skew-Hermitian.

The eight edge gaps are $\{\pm1,\pm2,\pm3,\pm7\}$. Degree-seven Lagrange polynomials in $\operatorname{ad}_A$ select the corresponding edge classes from $B$, within eight letters. The unique anchor gaps give the two anchor matrix units. The colour-pair selectors propagate both anchored units through the heap, subtracting the already-reached parent contribution. At vertex $v$ their lengths are at most $8\,\operatorname{size}(v)$; the heap height is at most $D=1+\lfloor\log_2(n-1)\rfloor$.

Bracketing anchored units produces $E_{vw}-\delta_{vw}E_{00}$ within $16D$ letters. These adjusted units span the traceless complex matrices. The real-form argument returns the span of $\mathfrak{su}(n)$ for the skew-Hermitian pair. The Lie-Jacobi argument relates arbitrary bracket combinations to the right-nested filtration. The polynomial determinant and analytic null-set theorem give almost-everywhere spanning; extra generators preserve that span. Word counting supplies the lower estimate.

## Falsifier

A counterexample to the formal claim would require a fixed $g\ge2$ and $n\ge2$ for which the logarithmic inequalities fail on a set of positive `suPairMeasure` measure. A non-generating tuple or a tuple in a null exceptional set does not falsify the almost-everywhere assertion. Finite floating-point ranks do not decide the uniform claim.

## Evidence

The algebra modules are `GenericLieLengthFiltration`, `GenericLieLengthConstruction` and `GenericLieLength`, under `D5/S3/Quantum/Algebra/`. The shared null-set theorem is `D5/S3/Analytic/NullSets/AnalyticZeroSetNull.ae_ne_zero_of_analytic`; `PauliRotationCriticalValues` also uses it. Their Scribe projections give the public definitions and theorem statements. `result : claim` is the settling theorem. The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}.

### Finite experiment

[Experiment directory pinned to `7cfb71e62115a22ad686a621a4f8a4606994b638`](https://github.com/the-omega-institute/trureturing-experiments/tree/7cfb71e62115a22ad686a621a4f8a4606994b638/docs/reports/jia-capel-2024-generic-lie-length).

Command, executed in that directory: `python3 check.py`; exit 0. Script SHA-256: `221b081fc7103821316bdfb76e088eb2dcf4db3108cc362120c0d15f8167a4d6`. The reported error count is zero. Exact gap and colour checks cover $n=2,\ldots,2000$; exact integer propagation checks cover $n=3,\ldots,40$. Numerical rank calculations cover the construction and one seeded random pair for each $n=2,\ldots,14$, with tolerance $10^{-8}$ for span rank. At $n=14$ the computed lengths are 11 for the construction and 10 for the random pair. These numerical lengths are computed, not exact kernel-certified values. The experiment does not establish optimal asymptotic constants or free-Lie independence.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Binary-heap, three-colour selector mechanism and uniform upper bound | Proved; kernel-checked | `GenericLieLengthConstruction.anchored_units_mem` proves both anchored matrix-unit memberships. Its consumed selector and propagation helpers give the degree-seven, eight-letter selectors. `compactPair_span_top` gives saturation by $16(1+\lfloor\log_2(n-1)\rfloor)$ for all $n\ge2$. `GenericLieLength.ae_span_top_of_witness` transfers the explicit witness to almost every tuple. `GenericLieLength.result` gives the fixed-$g$ logarithmic bound. |
| Counting lower bound $\sum_{j=1}^{L}g^j\ge n^2-1$ at saturation | Proved; kernel-checked | `GenericLieLengthFiltration.card_words_le` bounds the word count. The consumed private `saturation_count` proves the displayed dimension inequality; `lower_lieLength_of_saturation` gives the logarithmic lower bound used by `result`. |
| Optimal upper constant | Open | The proved constant $32/\log 2$ is sufficient; neither the formal theorem nor the finite experiment establishes optimality. |
| Lloyd--Maity Conjecture III | Open | Its free-Lie independence through saturation is stronger than logarithmic spanning; this result supplies no such independence theorem. See `Library/QuantumBounds/lloydmaity2019quantumcontrol.md`. |
| Bai--Wang--Yin literature gap | ASSUMED-UNVERIFIED; literature reading | Quantum Information Processing 23 (2024) 47, DOI `10.1007/s11128-023-04247-z`: only the abstract, references and Appendix A were readable in the source screen. The full text was paywalled and Firecrawl returned HTTP 402. The accessible abstract concerns spectral distributions of composed random channels and generic primitivity through Weingarten calculus; the unavailable text is not claimed to have been excluded. |
| Shitov's viXra 2308.0028 | Literature reading | The full-text screen concerns the associative injectivity index and cites Jia--Capel for the generic associative $O(\log n)$ bound; it does not provide the Lie-length construction used here. |
| Finite selector checks | Computed | The experiment entry checks gap and colour conditions for $n=2,\ldots,2000$, with zero errors. |
| Finite propagation checks | Computed | The same entry checks integer-matrix propagation identities for $n=3,\ldots,40$, with zero errors. |
| Numerical Lie lengths | Computed | The same entry checks the construction and one random pair at each $n=2,\ldots,14$ against the counting lower bound and $16D$ upper bound. It reports 11 and 10 at $n=14$. |

The decisive additional information is an explicit dimension-uniform spanning pair with logarithmic length, combined with a faithful measure-zero transfer and a word-count obstruction to smaller asymptotic order. The construction already works at $n=2$. For larger fixed generator counts it extends by including the spanning pair and adding zero generators in the witness tuple, then applying the determinant argument to the full parameter space. The corresponding bounds for absolutely continuous probability laws follow in prose from null-set preservation under absolute continuity. The source's uses of logarithmic bracket generation consequently have that bound available; stable control, exact optimal constants and Lloyd--Maity independence remain separate questions.

## ASSUMED-UNVERIFIED

The inaccessible part of Bai--Wang--Yin is an unresolved literature boundary. The accessible-source screen in #15954 is literature evidence, not a kernel theorem about publication completeness. The existence of faithful four-slot registration evidence is unresolved in #16180. These boundaries do not alter the compiled mathematical claim or certify an escape registration.
