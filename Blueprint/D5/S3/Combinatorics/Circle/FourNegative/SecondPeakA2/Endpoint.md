# Endpoint

## Abstract

Second peak SecondPeakA2: Endpoint

For every natural b,c,d with c>=3, d>=c+2, and b=d+1 or d+2, at k=2+b+c+d and seed 1+2^2+2^(2+b)+2^(2+b+c), the theorem supplies a permutation sigma of every Fin k label exactly once and one cut j<=k. Its literal earWord satisfies the complete new OriginalOrder at doubled seed. For every natural repetition r and take n, both prefix sums remain in their respective closed strips; every finite repetition has old total zero and new total zero separately, including r=0 and n=0. Existing zero_period_transport is reused. This closes the original a=2 near-b unit only; unrestricted Circle J/C3.1 and the all-b>d extension are not asserted.

**Theorem 1.1 (actualSource_second_peak_a2_joint_lift).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Endpoint.actualSource_second_peak_a2_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Endpoint.actualSource_second_peak_a2_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actualSource_second_peak_a2_joint_lift (b c d : ℕ)     (hc : 3≤c) (hd : c+2≤d) (hb : b=d+1 ∨ b=d+2) :     ∃ sigma : List (Fin (2+b+c+d)), ∃ j : ℕ, j≤2+b+c+d ∧       OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma ∧       OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))         (earWord (2+b+c+d) sigma j) ∧       (∀ r n : ℕ, ((((List.replicate r sigma).flatten).take n).map         (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum ∈         Set.Icc (0:ℤ) (modulus (2+b+c+d)/2)) ∧       (∀ r n : ℕ, ((((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).take n).map         (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum ∈         Set.Icc (0:ℤ) (modulus (2+b+c+d))) ∧       (∀ r : ℕ,         (((List.replicate r sigma).flatten).map           (actualSource (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)))).sum=0 ∧         (((List.replicate r (earWord (2+b+c+d) sigma j)).flatten).map           (actualSource (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c))))).sum=0)

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Endpoint.actualSource_second_peak_a2_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical](Physical.md)
