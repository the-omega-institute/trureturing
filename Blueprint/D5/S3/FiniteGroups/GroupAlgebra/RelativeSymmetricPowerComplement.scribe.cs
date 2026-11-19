using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class RelativeSymmetricPowerComplementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For 1<=k<p and pk+1<|E|, the genuine symmetric power of V_(p+1) has relative stable class V_(pk+1), including the original faithful two-dimensional representation.",
        H("The relative class of the actual symmetric-power complement"),
        Blocks(
            Paragraph(Text("This extends Lemma 3.8 of Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1. The actual direct-summand question after Lemma 3.9 is addressed by the separate symmetric-power splitting theorem. Here the extra conclusion is that the actual symmetric quotient has exactly the relative stable class of its polynomial coefficient-sum summand. This source asserts neither a decomposition at k>=p nor a worldwide novelty or priority claim.")),
            Describe.Lean(
                DescribeId.Create("symmetric-quotient-actual-average-section"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RelativeSymmetricPowerComplement.quotientAverage_id_section"),
                H("Averaging splits the genuine quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any representation and degree n with n! nonzero in K, quotientAverage applied to the tensor identity is an actual equivariant section of the quotientIntertwiner into Mathlib's SymmetricPower. On a pure tensor all n! permutations have the same quotient image. Normalized averaging therefore composes to the actual identity. The quotient is not replaced by invariant tensors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-block-tensor-relative-stability"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RelativeSymmetricPowerComplement.block_tensor_stable"),
                H("The tensor power carries one polynomial relative class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a prime p, a characteristic-p field K and an injective additive embedding alpha:E->K of a finite nontrivial additive group, 1<=k<p and pk+2<=|E|, the k-fold tensor power of V_(p+1) is relatively stably isomorphic to V_(pk+1). Each binary step uses the already classified original relative tensor criterion, with nonzero scalar choose(n+1,1)=n+1 for n+1<p. Explicit tensor equivalences retain the actual actions. The p=2 case has only k=1 and is included by the base case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-symmetric-power-relative-stability"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RelativeSymmetricPowerComplement.polynomial_symmetric_power_stable"),
                H("The symmetric power has its coefficient summand's relative class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With the same embedding and bounds, Sym^k(V_(p+1)) is relatively stably isomorphic to V_(pk+1), relative to the paper's direct sum of V_p,V_(2p),...,V_(|E|). The genuine symmetric quotient is an actual retract of the tensor power, and the coefficient-sum copy already has a constructed actual retraction. Polynomial retract absorption joins these splittings to the tensor stable class. No additional finiteness premise is imposed on factorization witnesses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-w-symmetric-power-relative-stability"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/RelativeSymmetricPowerComplement.originalW_symmetric_power_stable"),
                H("The conclusion for the original faithful W"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be prime and K a field of characteristic p. Let E be finite and nontrivial with p*e=0 for every e, and let rho be a faithful representation on a two-dimensional K-vector space W. For every 1<=k<p and pk+1<|E|, the actual Sym^k(V_(p+1)) has relative stable class V_(pk+1) for the original M action. The existing faithful normal form supplies one injective alpha and actual equivalences for all original V and M factors. These transport the genuine symmetric quotient and the original relative-projective witnesses together. K need not be finite; this interface retains K,W:Type and an independent universe for E."))),
                DescribeRole.Theorem))));
}
