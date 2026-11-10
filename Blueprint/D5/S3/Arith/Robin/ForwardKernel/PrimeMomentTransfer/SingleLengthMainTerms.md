# Single-length main terms

## Abstract

Scalar logarithmic integrals control the single-length main terms.

Write B=1−γ−log(2π) and M_k(Y,v)=μ_k v^(k/2) times the integral of (log(y/v)+B)^(k/2) from 1 to Y, with μ_2=1 and μ_4=3. The logarithm integral gives the exact second main term. Pointwise logarithm and power differences control rounding of the length; the integral on the terminal interval controls rounding of the cutoff.

**Theorem 1.1 (Logarithmic floor error).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.floor_log_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.floor_log_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For v at least one, the absolute difference between log v and the logarithm of its natural floor is at most the reciprocal of that floor.

**Theorem 1.2 (Second main exact).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.second_main_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.second_main_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Y at least one and v positive, the second main term equals v·[Y log(Y/v)+(B−1)Y+1+log v−B].

**Theorem 1.3 (Length main second).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.length_main_second`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.length_main_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 2≤Y and 1≤v≤Y, rounding v down changes the second main term by at most C Y log Y, for an absolute positive constant C.

**Theorem 1.4 (Length main fourth).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.length_main_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.length_main_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 2≤Y and 1≤v≤Y, rounding v down changes the fourth main term by at most C Y v (log Y)², for an absolute positive constant C.

**Theorem 1.5 (Cutoff main term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.cutoff_main_term`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.cutoff_main_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For moment order two or four, 2≤Y, and integer length 1≤K≤Y, rounding Y down changes the main term by at most C K^(k/2) (log Y)^(k/2).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.cutoff_main_term`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.floor_log_difference`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.length_main_fourth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.length_main_second`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMainTerms.second_main_exact`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentAsymptotic](../FourthTransfer/FourthMomentAsymptotic.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs](SingleLengthMSDefs.md)
