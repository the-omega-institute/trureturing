# Type-A Radical Actions

## Abstract

Type-A Radical Actions.

**Theorem 1.1 (actual positive graph radical coordinates).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions.actual_positive_graph_radical_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions.actual_positive_graph_radical_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derived from actual inverse-transpose and actual radical inverse; these are not supplied root-action laws.

**Theorem 1.2 (actual radical middle square).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions.actual_radical_middle_square`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions.actual_radical_middle_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Paired coordinates have the SAME sign even when the two directed root entries are distinct; no inverse-transport assumption is made. -/ private theorem graph_pair (a : Fin (k+2) → Fˣ) (phi : RingAut F) (eps : Bool) (g : Matrix.SpecialLinearGroup (Fin (k+2)) F) (hg : InRadical g) (j : Fin (k+2)) (hj0 : j≠first) (hjl : j≠last) : PartIIProposition6_5.diagonalFieldGraph a phi eps g first j= (a first:F)*(((a j)⁻¹:Fˣ):F)* (if eps then (-1:F)^(j.val+1)*phi (g j.rev last) else phi (g first j)) ∧ PartIIProposition6_5.diagonalFieldGraph a phi eps g j.rev last= (a j.rev:F)*(((a last)⁻¹:Fˣ):F)* (if eps then (-1:F)^(j.val+1)*phi (g first j) else phi (g j.rev last)) := by have h := actual_positive_graph_radical_coordinates g hg j hj0 hjl cases eps <;> simp only [PartIIProposition6_5.diagonalFieldGraph,fieldGraphAut,Bool.false_eq_true,ite_false,ite_true,mul_one,MulAut.mul_apply] · constructor · rw [(unitOdd% diagonal_entry)] change (a first:F)*phi (g first j)*(((a j)⁻¹:Fˣ):F)=_ ring · rw [(unitOdd% diagonal_entry)] change (a j.rev:F)*phi (g j.rev last)*(((a last)⁻¹:Fˣ):F)=_ ring · constructor · rw [(unitOdd% diagonal_entry)] change (a first:F)*phi (positiveGraph g first j)*(((a j)⁻¹:Fˣ):F)=_ rw [h.1,map_mul,map_pow,map_neg,map_one]; ring · rw [(unitOdd% diagonal_entry)] change (a j.rev:F)*phi (positiveGraph g j.rev last)*(((a last)⁻¹:Fˣ):F)=_ rw [h.2,map_mul,map_pow,map_neg,map_one]; ring /-- Actual square on every selected middle root pair. Hypotheses refer to the concrete diagonal entries; they will be constructed by the p263 determinant-one inner torus.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions.actual_positive_graph_radical_coordinates`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalActions.actual_radical_middle_square`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates](PartIIRadicalCoordinates.md)
