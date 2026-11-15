using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class SymmetricPowerBlockSplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dual symmetric tensor multiplication and permutation averaging construct actual retractions on genuine symmetric quotients.",
        H("Actual quotient splittings from dual tensor sections"),
        Blocks(
            Paragraph(Text("Let K be a field of type Type, E an additive group in an independent universe, and A and B vector spaces of type Type with E-actions rho and sigma. Write T_n(A) for the Fin n indexed tensor power with diagonal action, and q for Mathlib's actual quotient T_n(A)->SymmetricPower K (Fin n) A. The quotient helpers are reused from SymmetricPowerTranslation. The coefficient-ring universe restriction comes from this pinned quotient API, rather than a finiteness or characteristic assumption.")),
            Describe.Lean(
                DescribeId.Create("symmetric-block-coefficient-inclusion"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion"),
                H("The actual dual multiplication inclusion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given a finite basis b of A and an equivariant map mu:T_n(A)->B, coefficientInclusion is the composite of the ordinary dual of mu, the inverse of the genuine finite tensor-dual equivalence, and the actual quotient T_n(A*)->Sym^n(A*). No symmetric-power duality equivalence is assumed. This definition alone asserts neither injectivity nor splitting."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-block-actual-coefficient-retraction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.exists_coefficient_retraction"),
                H("Averaging descends a tensor retraction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose an equivariant s:B->T_n(A) satisfies mu s=id, mu is invariant under every actual permutation of tensor positions, and (n!:K) is nonzero. The theorem constructs an equivariant retraction of coefficientInclusion from the genuine Sym^n(A*) quotient to B*. Its composite with the inclusion is exactly id, with no stable equivalence or relative-projectivity substitution.")),
                    Paragraph(Text("Dualizing the supplied tensor section gives a tensor retraction. Permutation invariance of mu makes its dual inclusion fixed under the actual factor permutations, proved through the tensor-dual pairing. Averaging the tensor retraction over all n! permutations gives a symmetric multilinear map and hence descends through the existing quotient universal property. Each summand has the same composite on the inclusion; division by n! gives the identity. These are the classical finite-group averaging and finite tensor-duality mechanisms. The tensor section is an explicit premise of this general helper; its construction for bounded polynomials is supplied by ElmerKadrSymmetricPowerSplitting."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-block-exact-ordered-coefficients"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion_basis"),
                H("Ordered coefficient sums retain multiplicities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If mu sends each tensor-basis word indexed by t:Fin n->I to c(degree t), then coefficientInclusion sends c*(i) to the sum of the actual quotient classes of the dual words over every ordered t with degree t=i. Repeated quotient monomials remain repeated terms. This exact tensor-dual basis expansion proves the image identification used for the paper's coefficient-sum submodule, without assuming a monomial normalization or dividing by the degrees of the factors."))),
                DescribeRole.Theorem))));
}
