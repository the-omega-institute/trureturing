using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeCosetFieldSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeCosetFieldSeparation", H("All-state transverse field substitution"), Blocks(
            Describe.Lean(DescribeId.Create("coset-field-transverse-commutator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeCosetFieldSeparation.field_transverse_commutator"),
                H("field_transverse_commutator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive definite original lattice D of arbitrary finite rank, every finite external rank, integral rectangular B and symmetric even-diagonal C, every external source charge a, every original source state u, external direction j, natural oscillator frequency k, integer mode m and arbitrary ambient target v, the actual native field Y_E(J_a u)[m] on T(j,k)v equals T(j,k) Y_E(J_a u)[m]v minus transversePair(a,j) times Y_E(J_a u)[m-(k+1)]v. The original cocycle and integer zero-mode exponent remain literal. Ground fields satisfy the native polynomial-convolution identity. Old current derivatives commute with transverse multiplication, so normalMinusOne and the native multiplication_recursion extend it through every original source polynomial and finite charge sum. Native operator truncation justifies the normal-product sums. No ambient positivity or assumed factorization is used."))), DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, math/0402315v1, section 4.1, fixes the native oscillator conventions. The normal products reuse the repository's native residue operators with their Carnahan Apache-2.0 attribution. This all-state, arbitrary-target relation supplies transverse translation. The complete two-source comparison combines this relation with the inner creation-factor expansion and finite coefficient assembly in LatticeCosetOperatorCorrection.")))));
}
