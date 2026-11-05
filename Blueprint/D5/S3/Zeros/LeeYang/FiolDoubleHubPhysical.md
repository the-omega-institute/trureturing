# Double-hub physical

## Abstract

The physical double-hub family: physical.

For every m>=1 and cutoff>=3, the roots and multiplicities are those of the coefficient extracted from the original physical source. The coefficient identity supplies the nonzero scalar relating that source to R_m; scalar multiplication preserves the complete root multiset, every root predicate and every multiplicity.

There is a strictly increasing list of N upper angles in (0,pi). The actual physical coefficient has precisely their exponentials, their conjugates, and h copies of 1. Every other root is simple with norm 1. The point -1 is absent. The points i and -i occur exactly for m mod 4 equal to 1, each with multiplicity one.

The independent homogeneous identity holds at arbitrary complex a,b. Both punctured coordinate axes have nonzero value, and the origin has value zero. Thus neither projective axis adds a missing zero to the ratio description. The result concerns this infinite family and this assignment-summed formal coefficient at tau=-1; it does not establish the conjecture for all trees or for a fixed labelled placement.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Definition 1.1 (spinTruncation).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinTruncation`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines spinTruncation for the physical double-hub family.

**Definition 1.2 (spinCoefficient).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinCoefficient`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines spinCoefficient for the physical double-hub family.

**Theorem 1.3 (spin coefficient eq source).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spin_coefficient_eq_source`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spin_coefficient_eq_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connects two independently defined formal coefficients through the spin-sign proof. Exact source statement: theorem spin_coefficient_eq_source (m cutoff : ℕ) :     spinCoefficient m cutoff = sourceCoefficient m cutoff.

**Theorem 1.4 (physical root classification).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.physical_root_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.physical_root_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uses the actual spin/source bridge and nonzero normalization to transfer complete root/multiplicity classification. Exact source statement: theorem physical_root_classification (m cutoff : ℕ) (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :     let p := (spinCoefficient m cutoff).map Complex.ofRealHom     p.natDegree = 4*m+6 ∧ p ≠ 0 ∧     ∃ theta : Fin (N (m+1)) → ℝ, StrictMono theta ∧       (∀ j, 0 < theta j ∧ theta j < Real.pi) ∧       p.roots = Multiset.replicate (h (m+1)) 1 +         Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) +         Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) ∧       Polynomial.rootMultiplicity 1 p = (if Even m then 2*m+2 else 2*m) ∧       (∀ z : ℂ, p.IsRoot z → z ≠ 1 →         Polynomial.rootMultiplicity z p = 1 ∧ ‖z‖ = 1) ∧       (p.roots.filter (fun z => z ≠ 1)).card = (if Even m then 2*m+4 else 2*m+6) ∧       ¬ p.IsRoot (-1) ∧       (p.IsRoot Complex.I ↔ m % 4 = 1) ∧       (p.IsRoot (-Complex.I) ↔ m % 4 = 1) ∧       (m % 4 = 1 → Polynomial.rootMultiplicity Complex.I p = 1 ∧         Polynomial.rootMultiplicity (-Complex.I) p = 1).

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.physical_root_classification`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinCoefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinTruncation`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spin_coefficient_eq_source`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubRoots](FiolDoubleHubRoots.md)
