# Hardin's recurrence for OEIS A303956

## Abstract

The literal rooted binary king-strip counts satisfy Hardin's seventh-order recurrence.

**Definition 1.1 (The literal array predicate).**

$$\forall n: Nat, (\forall A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(2\right), (\operatorname{Admissible}\left(A\right) = \left((\forall i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \Rightarrow (A\left((i,0)\right) = 0))) \land (\forall p: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(3\right), (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((q: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(3\right) \mapsto (q \ne p) \land ((\operatorname{Fin}.\operatorname{val}\left(q.1\right) \le \operatorname{Fin}.\operatorname{val}\left(p.1\right) + 1) \land ((\operatorname{Fin}.\operatorname{val}\left(p.1\right) \le \operatorname{Fin}.\operatorname{val}\left(q.1\right) + 1) \land ((\operatorname{Fin}.\operatorname{val}\left(q.2\right) \le \operatorname{Fin}.\operatorname{val}\left(p.2\right) + 1) \land ((\operatorname{Fin}.\operatorname{val}\left(p.2\right) \le \operatorname{Fin}.\operatorname{val}\left(q.2\right) + 1) \land (A\left(q\right) \ne A\left(p\right))))))), \operatorname{Finset}.\operatorname{univ}\right)\right) \in \{0,1,2,5\}))\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.Admissible` (`✓ std3`).

*Citation.* R. H. Hardin (2018). *OEIS A303956: rooted binary arrays with prescribed unequal king neighbours*. URL: <https://oeis.org/A303956>.

*Commentary.*

R. H. Hardin, OEIS A303956, NAME: "Number of n X 3 0..1 arrays with every element unequal to 0, 1, 2 or 5 king-move adjacent elements, with upper left element zero." A is a labelled function from Fin n × Fin 3 to Fin 2. The root conjunct fixes the first row's first bit to zero. The finite set contains distinct other cells whose two coordinate distances are at most one and whose bits differ. Each count belongs to {0,1,2,5}. All boundaries are clipped to the rectangle, without self-neighbours, wrapping, padding, symmetry quotient or complement division. The coordinate statement adapts Hardin's source under CC BY-SA 4.0, attributed to Hardin and the OEIS Foundation.

**Definition 1.2 (The original array count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = (\operatorname{Nat}.\operatorname{card}\left(\{A: (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(3\right)) \to \operatorname{Fin}\left(2\right) | \operatorname{Admissible}\left(A\right)\}\right): Int))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin (2018). *OEIS A303956: rooted binary arrays with prescribed unequal king neighbours*. URL: <https://oeis.org/A303956>.

*Commentary.*

R. H. Hardin, OEIS A303956, NAME: "Number of n X 3 0..1 arrays with every element unequal to 0, 1, 2 or 5 king-move adjacent elements, with upper left element zero." The count is the cardinality of the actual array subtype, cast to the integers. It is defined independently of the recurrence and of the transfer matrix. The source concerns positive heights; the vacuous root condition at height zero does not occur in the asserted recurrence.

**Definition 1.3 (The empirical assertion).**

$$claim = (\forall n: Nat, ((8 < n) \Rightarrow (\operatorname{a}\left(n\right) = \operatorname{a}\left((n - 1)\right) + 2 \cdot \operatorname{a}\left((n - 2)\right) + 3 \cdot \operatorname{a}\left((n - 3)\right) + 2 \cdot \operatorname{a}\left((n - 4)\right) - 2 \cdot \operatorname{a}\left((n - 5)\right) - 6 \cdot \operatorname{a}\left((n - 6)\right) - 4 \cdot \operatorname{a}\left((n - 7)\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.claim` (`✓ std3`).

*Citation.* R. H. Hardin (2018). *OEIS A303956: rooted binary arrays with prescribed unequal king neighbours*. URL: <https://oeis.org/A303956>.

*Commentary.*

R. H. Hardin, OEIS A303956, FORMULA: "Empirical: a(n) = a(n-1) +2*a(n-2) +3*a(n-3) +2*a(n-4) -2*a(n-5) -6*a(n-6) -4*a(n-7) for n>8." All lag indices use natural subtraction. Values and the signed equality lie in the integers. Every natural n greater than eight is quantified; the smallest count argument is at least two.

**Theorem 1.4 (The seventh-order recurrence).**

$$\forall n: Nat, ((8 < n) \Rightarrow (\operatorname{a}\left(n\right) = \operatorname{a}\left((n - 1)\right) + 2 \cdot \operatorname{a}\left((n - 2)\right) + 3 \cdot \operatorname{a}\left((n - 3)\right) + 2 \cdot \operatorname{a}\left((n - 4)\right) - 2 \cdot \operatorname{a}\left((n - 5)\right) - 6 \cdot \operatorname{a}\left((n - 6)\right) - 4 \cdot \operatorname{a}\left((n - 7)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin-a303956` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin-a303956","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2018). *OEIS A303956: rooted binary arrays with prescribed unequal king neighbours*. URL: <https://oeis.org/A303956>.

*Commentary.*

Each row is coded by its three binary entries, with column zero as the least significant bit. An ordered pair of rows is a state. The initial weight checks the zero root and the top row, each transition checks exactly one interior row, and the terminal weight checks the bottom row. Coding and reconstruction give inverse correspondences at every height k+2, so the array count is v T^k t, including k=0. For the polynomial with ascending coefficients (4,6,2,-2,-3,-2,-1,1), its initial row-vector residual r has rt=0, rTt=0 and rT²=0. These identities for the actual local predicate imply vanishing after every power: the first two cases use the scalar identities and every later case uses rT²=0. Expanding gives exactly Hardin's formula. Minimal order, threshold sharpness and other widths require separate arguments.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.Admissible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.claim`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.result`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer](../NarayanaStrip/CiglerCycleWalkTransfer.md)
