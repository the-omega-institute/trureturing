# Double-hub reciprocal

## Abstract

The physical double-hub family: reciprocal.

Reflection of H_r and S_r gives reflection of U,V,W. The seven terms of Q have the same reflection degree 2N. Its constant coefficient is A+B+C+D+E+G+9 and is strictly positive. Reflection therefore gives exact degree 2N, equal positive leading and constant coefficients, and reciprocity.

Multiplying by (1-X)^h gives a reciprocal polynomial R_m of exact degree 4m+6 with the same positive endpoint coefficient. Evaluation at i by residues modulo four gives a root exactly when m mod 4 is 1; the derivative is nonzero there, so both i and -i are simple.

The phase-normalized value exp(-i N theta)Q(exp(i theta)) is real for every real theta and is continuous. Its zeros are exactly the corresponding unit-circle zeros of Q.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Definition 1.1 (baseDegree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.baseDegree`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.baseDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines baseDegree for the physical double-hub family.

**Definition 1.2 (endpointCoefficient).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.endpointCoefficient`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.endpointCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines endpointCoefficient for the physical double-hub family.

**Theorem 1.3 (Q coeff zero).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_coeff_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_coeff_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem Q_coeff_zero (d : ℕ) (hd : 2 ≤ d) :     (Q d).coeff 0 = endpointCoefficient d.

**Theorem 1.4 (endpointCoefficient pos).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.endpointCoefficient_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.endpointCoefficient_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem endpointCoefficient_pos (d : ℕ) (hd : 2 ≤ d) :     0 < endpointCoefficient d.

**Theorem 1.5 (candidate degree reciprocity).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_degree_reciprocity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_degree_reciprocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Establishes exact degree and reciprocity of this full Q family through polynomial coefficient symmetry. Exact source statement: theorem candidate_degree_reciprocity (d : ℕ) (hd : 2 ≤ d) :     (Q d).natDegree = 2*N d ∧ (Q d).reverse = Q d ∧     (Q d).leadingCoeff = endpointCoefficient d ∧     (Q d).coeff 0 = endpointCoefficient d ∧ Q d ≠ 0.

**Theorem 1.6 (candidate R structure).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_R_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_R_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combines both parity degree and endpoint arguments on the independently defined R family. Exact source statement: theorem candidate_R_structure (m : ℕ) (hm : 1 ≤ m) :     (R m).natDegree = 4*m+6 ∧ (R m).reverse = R m ∧     (R m).leadingCoeff = endpointCoefficient (m+1) ∧     (R m).coeff 0 = endpointCoefficient (m+1) ∧ R m ≠ 0.

**Theorem 1.7 (Q eval I).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_eval_I`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_eval_I` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem Q_eval_I (d : ℕ) :     (Q d).eval₂ Complex.ofRealHom Complex.I =       if d%4 = 0 then ((4*(8*(d:ℝ)*(2*d-1))+8*(16*((d:ℝ)-1))+72 : ℝ) : ℂ)       else if d%4 = 1 then ((2*(8*(d:ℝ)*(2*d-1))+2*(16*((d:ℝ)-1))+18 : ℝ) : ℂ)       else if d%4 = 2 then 0       else ((-2*(16*((d:ℝ)-1))-18 : ℝ) : ℂ).

**Theorem 1.8 (candidate I iff).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_I_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_I_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem candidate_I_iff (m : ℕ) (hm : 1 ≤ m) :     ((R m).map Complex.ofRealHom).IsRoot Complex.I ↔ m%4 = 1.

**Theorem 1.9 (candidate neg I iff).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_neg_I_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_neg_I_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem candidate_neg_I_iff (m : ℕ) (hm : 1 ≤ m) :     ((R m).map Complex.ofRealHom).IsRoot (-Complex.I) ↔ m%4 = 1.

**Theorem 1.10 (Q derivative I).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_derivative_I`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_derivative_I` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem Q_derivative_I (d : ℕ) (hd : d%4 = 2) :     (Q d).derivative.eval₂ Complex.ofRealHom Complex.I =       ((8*(d:ℝ)^4+16*(d:ℝ)^2*(2*d-1):ℝ):ℂ).

**Theorem 1.11 (candidate I simple).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_I_simple`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_I_simple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem candidate_I_simple (m : ℕ) (hm : 1 ≤ m) (hi : m%4 = 1) :     Polynomial.rootMultiplicity Complex.I ((R m).map Complex.ofRealHom) = 1.

**Theorem 1.12 (candidate neg I simple).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_neg_I_simple`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_neg_I_simple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem candidate_neg_I_simple (m : ℕ) (hm : 1 ≤ m) (hi : m%4 = 1) :     Polynomial.rootMultiplicity (-Complex.I) ((R m).map Complex.ofRealHom) = 1.

**Definition 1.13 (phaseValue).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines phaseValue for the physical double-hub family.

**Theorem 1.14 (phaseValue real).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_real`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem phaseValue_real (d : ℕ) (hd : 2 ≤ d) (theta : ℝ) :     (phaseValue d theta).im = 0.

**Theorem 1.15 (phaseValue zero iff).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem phaseValue_zero_iff (d : ℕ) (theta : ℝ) :     phaseValue d theta = 0 ↔       ((Q d).map Complex.ofRealHom).IsRoot (Complex.exp ((theta:ℂ)*Complex.I)).

**Theorem 1.16 (phaseValue continuous).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem phaseValue_continuous (d : ℕ) : Continuous (phaseValue d).

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_coeff_zero`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_derivative_I`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.Q_eval_I`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.baseDegree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_I_iff`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_I_simple`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_R_structure`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_degree_reciprocity`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_neg_I_iff`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.candidate_neg_I_simple`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.endpointCoefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.endpointCoefficient_pos`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_continuous`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_real`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubReciprocal.phaseValue_zero_iff`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation](FiolDoubleHubOrientation.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
