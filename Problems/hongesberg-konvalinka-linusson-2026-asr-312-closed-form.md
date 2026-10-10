---
slug: hongesberg-konvalinka-linusson-2026-asr-312-closed-form
bibkey: hongesberg2026asr
doi: 10.48550/arXiv.2610.07442
url: https://arxiv.org/abs/2610.07442v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/AlternatingSignRectangles/ExtendedAvoidanceClosedForm.result
---

# The closed form for extendably 312-avoiding alternating sign rectangles

## Problem

H. Höngesberg, M. Konvalinka and S. Linusson, *Pattern avoidance in alternating sign rectangles I: Extended avoidance*, arXiv:2610.07442v1, Conjecture 4.5, asks whether equation (4.2) counts all $r\times k$ extendably 312-avoiding alternating sign rectangles with $d$ nonempty rows. For $r,k,d\in\mathbb N$ with $d\le r$ and $d\le k$, the conjectured value is

$$
\begin{aligned}
S^{312}_{r,k,d}={}&\sum_{i=1}^{d}2^{i-1}\binom{k}{i}
 \left(\binom{r-2}{d-i}-2\binom{r-2}{d-i-2}\right)+\binom rd\\
&+\sum_{i=0}^{d}C_{2i}\binom{r-1+2i}{d-1-2i}
 +2\sum_{i=1}^{d}(-1)^i\binom r{d-i}.
\end{aligned}
$$

Here $C_n$ is the Catalan number. An integer upper argument uses the generalized binomial coefficient; a negative lower argument gives zero. Thus the finite Catalan sum equals the source's sum over all nonnegative $i$. The literal count is `SignLines.S`, the right side is `ExtendedAvoidanceClosedForm.F`, and `ExtendedAvoidanceClosedForm.result : claim` proves their equality. [Preregistration #14736](https://github.com/the-omega-institute/trureturing/issues/14736) specifies these conventions.

An ASR has entries in $\{-1,0,1\}$, alternating nonzero entries in each row and column, first and last nonzero row entries equal to $1$, and first nonzero column entries equal to $1$. An ASM is a square ASR with all row and column sums equal to $1$. A 312 occurrence consists of increasing rows $i_1<i_2<i_3$ and columns $j_1<j_2<j_3$ with entries $M_{i_1j_3}=M_{i_2j_1}=M_{i_3j_2}=1$. Extendable avoidance means existence of a 312-avoiding square ASM with the rectangle as its top-left corner, with no bound assumed on the extension size.

## Motivation

The closed form evaluates the literal cardinality without assuming the source recurrences or a counting equivalence. The zero-row convention is also proved from the literal count, including zero dimensions: $S^{312}_{r,k,0}=1$.

## Gap

The source states the general formula as Conjecture 4.5 and proves its recurrences and selected slices. The preregistration records the source and bounded literature checks. Those readings do not establish an exhaustive priority claim. The mathematical settlement is the kernel-checked equality in this delivery.

## Route

The sign-line API proves that extendable 312 avoidance permits at most one $-1$ in each row and column. `CanonicalCompletion.extAvoids312_iff_safe` characterizes the literal existential extension by concrete corner obstructions. Its construction has square order $m=r+|\operatorname{deficientColumns}(R)|$. Since the deficient columns form a subset of $\operatorname{Fin}k$, $m\le r+k$; this bound is a consequence of the checked construction, not an assumption in the public definition.

The empty-row filling and first-column factorization construct inverse maps and prove predicate preservation. They yield `EmptyRowFilling.S_col`, `SquareASMDecomposition.S_diagonal`, `RowCompleteRecurrence.S_row` and `InteriorRecurrence.S_interior`. `EmptyRowFillingConstruction.S_outside` and `SignLines.S_zero` supply the other cases. `RecurrenceSeries.Rational.rational_recurrence_unique` establishes uniqueness by induction on $r+k$; `RecurrenceSeries.recurrence_unique` applies it to the integer family through rational casts.

Let $a=r-d$, $b=k-d$, let $R(t)$ be the large-Schröder series satisfying $R=1+tR+tR^2$, and put $A=1+tR$. The coefficient family is

$$G_{a,b}(t)=\frac{A}{2}\left(R^b(1-tR)^{-a}+(1-t)^{-a}\right).$$

`RecurrenceSeries.Series.series_eq_T` identifies its coefficients with the recursively defined counts. The private `ExtendedAvoidanceClosedForm.Formula.formula_defect_series` identifies the same series with the right side of (4.2), using the formal diagonal coefficient identity and the even-Catalan identity. `literal_recurrenceSpec` supplies the literal counts to `result_of_recurrences`, whose conclusion is the public `result`.

## Falsifier

A single admissible triple with a literal count different from (4.2) would refute the conjecture. The proved universal equality excludes such a triple in the formal definitions. Finite computations check conventions independently and do not replace this proof.

## Evidence

The twelve modules under `D5/S3/Combinatorics/AlternatingSignRectangles/` and their Blueprint Scribes carry the proof and statement mirrors. The settling Scribe records `OpenProblemResolutionClaim` with `Proved`. The axiom closure of every public declaration is contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

Experiment entry: [published programs and README](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/hongesberg-konvalinka-linusson-2026-asr-312-closed-form). Run the following commands from that directory at the pinned commit.

| Program | Command | Exit | SHA-256 | Readings and exact scope |
| --- | --- | --- | --- | --- |
| `check.py` | `python3 check.py` | 0 | `09d135d95c3ac969c6fa57cf4764cc492e32107453bb3714084136fcfd9d6bd8` | All 2,870 triples with $0\le d\le r,k\le19$; 0 mismatches between the source recurrences and (4.2). $S(5,6,4)=373$; $S(3,3,3)=6=\mathrm{Sch}_2$. |
| `brute.py` | `python3 brute.py` | 0 | `12917d6916cadbaa7d256a1e40971cf36fb2d1a0efeea61f113c4b69ee52f8d7` | Enumerates 312-avoiding square ASMs of orders $1\le m\le6$, with counts $1,2,6,22,90,394$. Literal ASR corner counts agree on all 50 triples with $r+k\le6$; 0 mismatches. |

Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871. No validated four-slot registration is asserted for the new public theorem/lemma targets; the linked issue names their DTR verdicts and missing source-binding evidence.

## Triage

- **Mechanism — proved, kernel-checked declarations.** Defect re-indexing converts the three source recurrences to first-order relations in the large-Schröder series. `RecurrenceSeries.Series.series_eq_T` and `ExtendedAvoidanceClosedForm.Formula.formula_defect_series` give the common coefficient family $G_{a,b}$ displayed above. The formal diagonal and even-Catalan identities identify its coefficients with (4.2).
- **Source recurrences — proved, kernel-checked declarations and the construction bound.** Propositions 4.2 and 4.3 and Theorem 4.4 follow from the literal definitions in `S_row`, `S_col` and `S_interior`. `S_diagonal` proves $S(d,d,d)=\mathrm{Sch}_{d-1}$ for $d>0$. The canonical completion has $m=r+|\operatorname{deficientColumns}(R)|\le r+k$, as explained in Route. No extension bound or recurrence is a hypothesis of `claim`.
- **Numerical conventions — computed.** The two pinned experiment entries above have exit 0, with scopes $r,k\le19$ for the recurrence comparison and $r+k\le6$ for literal enumeration. The computations make no claim outside these finite scopes; the all-parameter formula is proved separately by `result`.
- **Other patterns — open, source/literature reading.** The source also treats recurrences for 132, 213 and 231. Their closed forms remain open in the cited source and are not conclusions of this delivery. No numerical observation for these other patterns is claimed here.
- **Paper II — open, source/literature reading.** The companion paper on classical avoidance is described by the source as in preparation. No theorem about its eventual contents is asserted.

### What the settlement shows

**Proved.** The decisive mechanism is compatibility of the concrete decomposition recurrences with a single defect-indexed generating function. It gives (4.2) for every $r,k,d\in\mathbb N$ with $d\le\min(r,k)$, including $d=0$ and zero dimensions under the literal conventions. The sign-line restrictions and finite canonical completion justify the passage from unbounded existential extension to finite combinatorial decompositions.

**Proved.** The square slice and the source's already established slices are compatible with the general formula. Results in the source conditional on Conjecture 4.5 may use this equality when their conventions and hypotheses are the same; this is not a formal verification of every later statement in the source.

**Computed.** The two finite numerical checks in Evidence independently test the generalized binomial convention and the top-left extension convention within their stated scopes.

**Open.** No claim of sharpness for the extension bound is proved. Closed forms for 132, 213 and 231, and the contents of the companion classical-avoidance paper, remain outside this settlement.

## ASSUMED-UNVERIFIED

Exhaustive literature priority and results beyond the bounded preregistration literature scope are not verified. The status of the companion paper beyond the cited source is not verified. The linked unfinished escape audit is not a mathematical proof gap and is not `declared_validated` evidence.
