using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class RationalQubitMixedEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit arithmetic witness for a maximally mixed qubit marginal.",
        H("Rational joint states with a maximally mixed endpoint"),
        Blocks(Describe.Lean(DescribeId.Create("rational-mixed-endpoint"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint."
                + "rational_rank_two_of_maximally_mixed_endpoint"),
            H("Rank two for a maximally mixed endpoint"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let c be a rational Bloch vector with squared length strictly between "
                    + "zero and one. Then half the identity and the trace-one Bloch matrix for c are "
                    + "partial traces of a positive semidefinite joint matrix of rank exactly "
                    + "two whose entries have rational real and imaginary parts.")),
                Paragraph(Text(
                    "Lagrange's theorem supplies a rational quaternion H with squared "
                    + "norm one minus the squared length of c. Choose a nonzero rational vector "
                    + "v perpendicular to c and to the imaginary part of H. The product of H "
                    + "with the pure quaternion v has zero real part, and its imaginary part y "
                    + "has squared length equal to the product of the two squared norms. "
                    + "These vectors satisfy the witness equations for the rational qubit projector "
                    + "construction."))),
            DescribeRole.Theorem))));
}
