# Actual-Carrier CKZ Conjecture 2 for Separable Records

## Abstract

The actual separable right-maximum series satisfies the source weighted quadratic and the complete CKZ peak-three law.

**Theorem 1.1 (The actual quadratic with singleton and proper-cut terms).**

$$J = z + z \cdot (1 + \operatorname{C}\left(q\right)) \cdot J + \operatorname{C}\left(q\right) \cdot (1 + \operatorname{C}\left(q\right)) \cdot J^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_weighted_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J is the positive bivariate series whose outer coefficient marks the strict right-maximum count and whose inner coefficient marks length. q is the positive-length counting series of the literal permutations of Fin n avoiding 2413 and 3142. z is the singleton term, and C is the constant-series embedding into the outer PowerSeries.

The proof uses the frozen minimum-cut enumeration on the actual carrier. It restricts the block record laws to exact record fibers, combines the opposite-sign transport with the actual Schröder cardinalities, and derives I0(1+q)=q from the scalar Schröder equation. The proper-cut series then satisfies R=C(q)J and the all-avoider series satisfies U=(1+C(q))J, yielding the displayed quadratic.

The result is the source-faithful actual-carrier bridge needed before coefficient extraction. The same module proves the exact binomial coefficient normalization, identifies the Section 8 Newton kernels on the actual carrier, and extracts every length coefficient. Coefficientwise nonnegativity of the frozen kernels gives the arbitrary-index decline from record three. Exact reversal and complement transports then give all four literal distributions, including the zero tail and the singleton convention.

**Theorem 1.2 (The complete source-faithful peak-three conclusion).**

$$\forall n \in \mathrm{Nat},\; (5 \le n) \Rightarrow ((\forall k \in \mathrm{Nat},\; (k < 3) \Rightarrow ((\operatorname{irreducibleCount}\left(n, rmax, k\right) \le \operatorname{irreducibleCount}\left(n, rmax, k + 1\right)) \land \left((\operatorname{irreducibleCount}\left(n, lmin, k\right) \le \operatorname{irreducibleCount}\left(n, lmin, k + 1\right)) \land \left((\operatorname{reducibleCount}\left(n, lmax, k\right) \le \operatorname{reducibleCount}\left(n, lmax, k + 1\right)) \land (\operatorname{reducibleCount}\left(n, rmin, k\right) \le \operatorname{reducibleCount}\left(n, rmin, k + 1\right))\right)\right))) \land \left((\forall k \in \mathrm{Nat},\; (3 \le k) \Rightarrow ((\operatorname{irreducibleCount}\left(n, rmax, k + 1\right) \le \operatorname{irreducibleCount}\left(n, rmax, k\right)) \land \left((\operatorname{irreducibleCount}\left(n, lmin, k + 1\right) \le \operatorname{irreducibleCount}\left(n, lmin, k\right)) \land \left((\operatorname{reducibleCount}\left(n, lmax, k + 1\right) \le \operatorname{reducibleCount}\left(n, lmax, k\right)) \land (\operatorname{reducibleCount}\left(n, rmin, k + 1\right) \le \operatorname{reducibleCount}\left(n, rmin, k\right))\right)\right))) \land (\forall k \in \mathrm{Nat},\; (\operatorname{irreducibleCount}\left(n, rmax, k\right) \le \operatorname{irreducibleCount}\left(n, rmax, 3\right)) \land \left((\operatorname{irreducibleCount}\left(n, lmin, k\right) \le \operatorname{irreducibleCount}\left(n, lmin, 3\right)) \land \left((\operatorname{reducibleCount}\left(n, lmax, k\right) \le \operatorname{reducibleCount}\left(n, lmax, 3\right)) \land (\operatorname{reducibleCount}\left(n, rmin, k\right) \le \operatorname{reducibleCount}\left(n, rmin, 3\right))\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_ckz_conjecture_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least five, the carrier is the literal set of permutations of Fin n avoiding 2413 and 3142. The four counts are the actual positive irreducible and proper-cut fibers for strict right maxima, strict left minima, strict left maxima and strict right minima. The index is unshifted: k records means exactly k record positions.

The first conjunct is the weak rise for k below three. The second is the weak decline for every k at least three. The final conjunct states the resulting global maximum at record count three for each of the four distributions and every natural index, including indices beyond the length through the explicit zero-tail branch.

The proof starts from the actual direct-cut weighted quadratic. Its coefficient extraction is over the rationals, so signed differences retain equality rather than using natural-cardinality subtraction. The scalar Schröder equation supplies q=t+tq+q^2 and hence the exact time relation. The frozen RecordNewtonPositivity theorem applies to the definitionally identical actual M and t series. The resulting finite binomial sums have nonnegative coefficients. RecordTransport supplies the other three statistics, with its singleton correction zero in the n at least five range.

This is the complete Stage A mathematical target. Registration is USER-PAUSED by the owner of issue 12664; this delivery does not freeze, deposit or publish the result.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_ckz_conjecture_two`
- Truth anchor: `D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_weighted_quadratic`
- Dependency: [D5/S1/Words/Patterns/Separable/RecordFirstDecline](RecordFirstDecline.md)
- Dependency: [D5/S1/Words/Patterns/Separable/RecordNewtonPositivity](RecordNewtonPositivity.md)
