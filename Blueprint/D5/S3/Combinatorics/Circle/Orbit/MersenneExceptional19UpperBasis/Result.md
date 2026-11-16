# The selected integer span and the exact upper basis endpoint

## Abstract

The selected integer span and the exact upper basis endpoint.

**Theorem 1.1 (actual selected upper span eq kernel).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result.actual_selected_upper_span_eq_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result.actual_selected_upper_span_eq_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient by the actual selected span annihilates precisely the selected indicators, so selected reconstruction identifies all coordinate classes. Cancellation of 19(B-1) occurs only in integers and proves the original kernel equality. The explicit primitive-sum surjection gives kernel rank 3d-1; Mathlib rank-nullity and the existing Orzech basis theorem turn the spanning selected family of that cardinality into the exact integer basis.

**Theorem 1.2 (actual selected upper integer basis).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result.actual_selected_upper_integer_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result.actual_selected_upper_integer_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient by the actual selected span annihilates precisely the selected indicators, so selected reconstruction identifies all coordinate classes. Cancellation of 19(B-1) occurs only in integers and proves the original kernel equality. The explicit primitive-sum surjection gives kernel rank 3d-1; Mathlib rank-nullity and the existing Orzech basis theorem turn the spanning selected family of that cardinality into the exact integer basis.

Quotient by the actual selected span. Let L be span_Z(range selectedRow), on the original integer-valued functions over Fin(3d). Its coordinate classes quotientLabel L annihilate every selectedMask because that indicator belongs to L. Applying actual_selected_upper_reconstruction yields [e_i]=primitive_i*c, with c the class of coordinateGenerator=-3e00+2e20. Therefore [z]=(sum_i z_i primitive_i)c. This argument genuinely discharges the selected presentation hypothesis; it never infers selected spanning from the earlier all-zero-family theorem.

Recovering the original integer kernel. The shared source_eq_scale_primitive gives integerWeightedSum(z)=19(B-1) sum_i z_i primitive_i. The factor is nonzero for every r including zero. Cancellation occurs only in Z, proving that an element of the original weighted kernel has zero primitive sum and hence zero quotient class. This proves the candidate actual_selected_upper_span_eq_kernel, together with the existing literal-zero membership of each selected indicator.

Rank and the exact basis. The primitive-sum map P:Z^(3d)->Z sends coordinateGenerator to -3a+2b=1, so it is surjective and has the same kernel as integerWeightedSum. Mathlib first-isomorphism and rank-nullity over the domain Z give quotient finrank 1 and kernel finrank 3d-1. The actual selectedKernelRow family spans this kernel and UpperIndex has exactly that cardinality. Only at this point does the proof use basisOfTopLeSpanOfCardEqFinrank to produce a Basis whose underlying functions are precisely row(selectedMask r k). No independent matrix, span, determinant or certificate premise is added to the final telescope.

Exact endpoint. actual_selected_upper_integer_basis(r:Nat) produces b:Basis (UpperIndex r) Z (ker(integerWeightedSum r)) with (b k).val=row(selectedMask r k) for every k. The telescope retains r=0, all original physical labels and the one exceptional disjoint-union indicator.

Scope. The theorem concerns the selected integral basis and retains every physical coordinate. The broader full-permutation and unrestricted J conclusions require their own proofs. The preserved Boundary, EliminationFactors and Rearrangement sources are not prerequisites of the direct quotient-and-rank argument.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result.actual_selected_upper_integer_basis`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result.actual_selected_upper_span_eq_kernel`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Reconstruction](Reconstruction.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Result](../MersenneExceptional19ZeroLattice/Result.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Weights](../MersenneExceptional19ZeroLattice/Weights.md)
