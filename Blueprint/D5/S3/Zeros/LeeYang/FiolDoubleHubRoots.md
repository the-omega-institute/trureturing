# Double-hub roots

## Abstract

The physical double-hub family: roots.

The corrected samples yield N distinct upper roots of Q. Their conjugates give N distinct lower roots, exhausting its degree 2N. The complete root multiset is the sum of those two families and is duplicate free.

For R_m, add exactly h copies of 1. Its other roots are simple and have norm 1. The multiplicity at 1 is 2m+2 for even m and 2m for odd m. The number of other roots is 2m+4 for even m and 2m+6 for odd m.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Theorem 1.1 (corrected samples).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.corrected_samples`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.corrected_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs the complete strictly ordered alternating sample family for every d>=2 and every residue. Exact source statement: theorem corrected_samples (d : ℕ) (hd : 2≤d) :     ∃ s : ℕ → ℝ, s 0=0 ∧ s (N d)=Real.pi ∧       (∀ k, k<N d → s k<s (k+1)) ∧       (∀ k, k≤N d → 0<(-1:ℝ)^k*(phaseValue d (s k)).re).

**Theorem 1.2 (Q complete roots).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.Q_complete_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.Q_complete_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combines the corrected family with actual degree exhaustion for a full simple root multiset. Exact source statement: theorem Q_complete_roots (d : ℕ) (hd : 2≤d) :     ∃ theta : Fin (N d) → ℝ, StrictMono theta ∧       (∀ j, 0<theta j ∧ theta j<Real.pi) ∧       ((Q d).map Complex.ofRealHom).roots =         Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) +         Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) ∧       ((Q d).map Complex.ofRealHom).roots.Nodup.

**Theorem 1.3 (candidate full root multiset).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_full_root_multiset`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_full_root_multiset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives the exact R multiset using its independent factorization. Exact source statement: theorem candidate_full_root_multiset (m : ℕ) (hm : 1≤m) :     ∃ theta : Fin (N (m+1)) → ℝ, StrictMono theta ∧       (∀j,0<theta j ∧ theta j<Real.pi) ∧       ((R m).map Complex.ofRealHom).roots =         Multiset.replicate (h (m+1)) 1 +         Finset.univ.val.map (fun j => Complex.exp ((theta j:ℂ)*Complex.I)) +         Finset.univ.val.map (fun j => star (Complex.exp ((theta j:ℂ)*Complex.I))) ∧       ((Q (m+1)).map Complex.ofRealHom).roots.Nodup.

**Theorem 1.4 (candidate nonunit root multiplicity).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_nonunit_root_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_nonunit_root_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transfers exhaustive Q simplicity to each non1 R root and proves its norm. Exact source statement: theorem candidate_nonunit_root_multiplicity (m : ℕ) (hm : 1≤m) (z : ℂ)     (hz : ((R m).map Complex.ofRealHom).IsRoot z) (hz1 : z≠1) :     Polynomial.rootMultiplicity z ((R m).map Complex.ofRealHom)=1 ∧ ‖z‖=1.

**Theorem 1.5 (candidate other roots card).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_other_roots_card`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_other_roots_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counts the complete filtered R multiset with both parities. Exact source statement: theorem candidate_other_roots_card (m : ℕ) (hm : 1≤m) :     (((R m).map Complex.ofRealHom).roots.filter (fun z => z≠1)).card =       if Even m then 2*m+4 else 2*m+6.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.Q_complete_roots`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_full_root_multiset`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_nonunit_root_multiplicity`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_other_roots_card`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.corrected_samples`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubSamples](FiolDoubleHubSamples.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
