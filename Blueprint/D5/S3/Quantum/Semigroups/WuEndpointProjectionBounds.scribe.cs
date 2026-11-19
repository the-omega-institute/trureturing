using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointProjectionBoundsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointProjectionBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace pairing with the signed map is bounded on rank-one and mixed rank projections.",
        H("Projection bounds at the Wu endpoint"),
        Blocks(
            Paragraph(Text("The unweighted twirl fixes total measured mass, and the Pauli frame bounds control sums over the first and last degree levels. The projection onto the first two vectors of a basis and its orthogonal complement resolve the identity. The decreasing conjugation weights combine with the resulting prefix bounds.")),
            Describe.Lean(DescribeId.Create("rank-one-bound"), DeclarationHandle.Create(Owner + "A1_rankOne_rankOne"),
                H("Two rank-one projections"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any two unit vectors u and v, the real trace of the product of the projector onto u and the image of the projector onto v lies between β² and α²."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mixed-rank-bound"), DeclarationHandle.Create(Owner + "A1_rankOne_rankTwo_basis"),
                H("Rank-one and rank-two projections"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any unit vector u and any orthonormal basis of the two-mode space, the real trace pairing of the projector onto u with the image of the sum of the first two basis projectors is at most α."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-resolution"), DeclarationHandle.Create(Owner + "sum_endpointProjector"),
                H("Resolution of the identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four projectors of an orthonormal basis sum to the identity."))), DescribeRole.Theorem))));
}
