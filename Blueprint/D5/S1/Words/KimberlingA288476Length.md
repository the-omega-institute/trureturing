# Kimberling's replacement-iterate length conjecture

## Abstract

Every native replacement-iterate length is the integer recurrence sequence of OEIS A288476.

The binary alphabet is Bool, with false representing 0 and true representing 1. Each pass reads the original input from left to right, consumes a matched block, and appends its replacement. Newly emitted output is scanned only on the next pass. The index starts at zero and includes both parities.

**Definition 1.1 (The native replacement pass).**

$$\begin{aligned}\operatorname{sourceScan}\left([]\right) = []\\\forall v \in \operatorname{List}\left(Bool\right),\; \operatorname{sourceScan}\left(false :: false :: v\right) = [false,true,false,true] ++ \operatorname{sourceScan}\left(v\right)\\\forall v \in \operatorname{List}\left(Bool\right),\; \operatorname{sourceScan}\left(true :: v\right) = [false,true,true] ++ \operatorname{sourceScan}\left(v\right)\\\operatorname{sourceScan}\left([false]\right) = [false]\\\forall v \in \operatorname{List}\left(Bool\right),\; \operatorname{sourceScan}\left(false :: true :: v\right) = false :: \operatorname{sourceScan}\left(true :: v\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/KimberlingA288476Length.sourceScan` (`✓ std3`).

*Citation.* Clark Kimberling (2017). *OEIS A288476: lengths of nonoverlapping replacement iterates*. URL: <https://oeis.org/A288476>.

*Commentary.*

The source operation is the StringReplace program in OEIS A288473. The displayed cases are disjoint: an empty input, a leading 00, a leading 1, a final unmatched 0, or a leading 01. In the last case the first 0 is retained and scanning resumes at the original 1. The recurrence calls are on the remaining original input, never the emitted replacement.

**Definition 1.2 (The source iterates).**

$$\forall n \in \mathbb{N},\; \operatorname{sourceIter}\left(n\right) = \operatorname{Function}.\operatorname{iterate}\left(sourceScan, n, [false,false]\right)$$

*Formalization.* `D5/S1/Words/KimberlingA288476Length.sourceIter` (`✓ std3`).

*Citation.* Clark Kimberling (2017). *OEIS A288476: lengths of nonoverlapping replacement iterates*. URL: <https://oeis.org/A288476>.

*Commentary.*

The initial word is 00. Function.iterate applies the native pass exactly n times, including the identity pass at zero.

**Definition 1.3 (The independent integer recurrence).**

$$recurrence = \operatorname{LinearRecurrence}.\operatorname{mk}\left(3, ![-2,4,1]\right)$$

*Formalization.* `D5/S1/Words/KimberlingA288476Length.recurrence` (`✓ std3`).

*Citation.* Clark Kimberling (2017). *OEIS A288476: lengths of nonoverlapping replacement iterates*. URL: <https://oeis.org/A288476>.

*Commentary.*

OEIS A288476 defines a(n) = a(n-1) + 4*a(n-2) - 2*a(n-3), with a(0)=2, a(1)=4, a(2)=8. The coefficient vector is indexed in ascending order: -2, 4, 1. Its coefficient type is Int, so subtraction is integer subtraction.

**Definition 1.4 (The OEIS sequence).**

$$recurrenceSeq = \operatorname{LinearRecurrence}.\operatorname{mkSol}\left(recurrence, ![2,4,8]\right)$$

*Formalization.* `D5/S1/Words/KimberlingA288476Length.recurrenceSeq` (`✓ std3`).

*Citation.* Clark Kimberling (2017). *OEIS A288476: lengths of nonoverlapping replacement iterates*. URL: <https://oeis.org/A288476>.

*Commentary.*

Mathlib's mkSol constructs the sequence from the recurrence and its initial values. This definition contains no word, scanner or coding assumption.

**Theorem 1.5 (Every iterate has the conjectured length).**

$$\forall n \in \mathbb{N},\; (\operatorname{List}.\operatorname{length}\left(\operatorname{sourceIter}\left(n\right)\right):Int) = \operatorname{recurrenceSeq}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/KimberlingA288476Length.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a288476-replacement-iterate-length` (proved) by `D5/S1/Words/KimberlingA288476Length.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a288476-replacement-iterate-length","declaration_gid":"D5/S1/Words/KimberlingA288476Length.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling (2017). *OEIS A288476: lengths of nonoverlapping replacement iterates*. URL: <https://oeis.org/A288476>.

*Commentary.*

OEIS A288476, COMMENTS: Conjecture:  a(n) is the number of letters (0's and 1's) in the n-th iteration of the mapping 00->0101, 1->011, starting with 00; see A288473. The proof uses the auxiliary code D=00, E=01, O=1 and substitution D->EE, E->DOO, O->EO. For each code letter and every binary suffix, scanning its code followed by the suffix gives its substituted code followed by the scan of the suffix. List.foldr_hom extends this boundary identity to every finite code word. Function.Semiconj.iterate_right transports it to every source iterate. The existing image_add, image_one and subst_append give integer length states A(n+1)=2B(n), B(n+1)=A(n)+2C(n), C(n+1)=B(n)+C(n). Eliminating B and C gives A(n+3)=A(n+2)+4A(n+1)-2A(n). Mathlib's LinearRecurrence.eq_mk_of_is_sol_of_eq_init then identifies the native lengths with the independent sequence using initial values 2,4,8. No finite cutoff, parity condition or limiting-word assertion occurs.

## References

- Truth anchor: `D5/S1/Words/KimberlingA288476Length.recurrence`
- Truth anchor: `D5/S1/Words/KimberlingA288476Length.recurrenceSeq`
- Truth anchor: `D5/S1/Words/KimberlingA288476Length.result`
- Truth anchor: `D5/S1/Words/KimberlingA288476Length.sourceIter`
- Truth anchor: `D5/S1/Words/KimberlingA288476Length.sourceScan`
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundDefs](RankOneMorphismIterationBoundDefs.md)
