# Unbounded a2 AllEndpoint

## Abstract

Unbounded a2 AllEndpoint

For every natural b,c,d with c>=3, c+2<=d and d<b, at k=2+b+c+d and seed 1+2^2+2^(2+b)+2^(2+b+c), construct a permutation sigma of every Fin k label exactly once and j<=k. The literal earWord has complete OriginalOrder at k+1 and doubled seed. Every natural repetition and take, including zero and overlong takes, has its actualSource sum in the old strip [0,modulus(k)/2] or new strip [0,modulus(k)] respectively. Old and new complete repeated totals are separately zero. The exponent transport reuses physical_order and zero_period_transport. This is the full a=2 second-peak unit; the unrestricted Circle problem remains open.

**Theorem 1.1 (actualSource_second_peak_a2_all_h_joint_lift).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllEndpoint.actualSource_second_peak_a2_all_h_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllEndpoint.actualSource_second_peak_a2_all_h_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actualSource_second_peak_a2_all_h_joint_lift (b c d : ℕ)     (hc : 3≤c) (hd : c+2≤d) (hb : d<b) :     ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧       OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧       OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))         (earWord (2+b+c+d) sigma j) ∧       (∀ r n : ℕ, ((((List.replicate r sigma).flatten).take n).map         (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum ∈         Set.Icc (0:ℤ) (modulus (2+b+c+d)/2)) ∧       (∀ r n : ℕ, ((((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).take n).map         (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum ∈         Set.Icc (0:ℤ) (modulus (2+b+c+d))) ∧       (∀ r : ℕ,         (((List.replicate r sigma).flatten).map           (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum=0 ∧         (((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).map           (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum=0)

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllEndpoint.actualSource_second_peak_a2_all_h_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical](../SecondPeakA2/Physical.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/AllSelection](AllSelection.md)
