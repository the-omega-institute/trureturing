# Kasel displacement-ladder definitions

## Abstract

Dyadic horizons, normalized stage schemes and distinguished displacement values.

**Definition 1.1 (Dyadic block index).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.block`

*Formalization.* `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

block(v) is Nat.clog 2 v. For v at least two it is the unique k with 2^(k-1)<v<=2^k. The definition is total on the natural numbers.

**Definition 1.2 (The finite dyadic horizon).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.SA`

*Formalization.* `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.SA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SA(m) filters the inclusive interval [1,4^m] by block(v)>=2 and Even(block(v)). It is S_A intersected with this finite horizon.

**Definition 1.3 (Stage concatenation order).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.lexLess`

*Formalization.* `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.lexLess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lexLess(s,r,a,b) means s(a)<s(b), or s(a)=s(b) and r(a)<r(b). It compares stage first and fibre position second.

**Definition 1.4 (A valid finite scheme).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.Valid`

*Formalization.* `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Valid(X,s,r) requires that for a,b in X, equality of both stage and fibre position implies a=b. For every x<y<z in X with x+z=2*y, it excludes both lexLess(x,y) and lexLess(y,z) together, and both lexLess(z,y) and lexLess(y,x) together. Thus neither monotone AP occurs in the concatenation.

**Definition 1.5 (Nonnegative displacement).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.Normalized`

*Formalization.* `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.Normalized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normalized(X,s) requires floor(block(v)/2)<=s(v) for every v in X. Stages are natural numbers and division is natural-number division.

**Definition 1.6 (The distinguished values).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.distinguished`

*Formalization.* `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.distinguished` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

distinguished is the finset {3,4,9,10,11,12,13,14,15,16}, namely S_A intersected with [1,16].

**Theorem 1.7 (Identifying a dyadic block).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.block_eq_of_pow_pred_lt_le_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.block_eq_of_pow_pred_lt_le_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If k>=1 and 2^(k-1)<v<=2^k, then block(v)=k.

**Theorem 1.8 (Distinguished values lie in every relevant horizon).**

Lean statement: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.distinguished_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.distinguished_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m>=2, distinguished is a subset of SA(m).

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.Normalized`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.SA`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.Valid`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.block`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.block_eq_of_pow_pred_lt_le_pow`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.distinguished`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.distinguished_subset`
- Truth anchor: `D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.lexLess`
