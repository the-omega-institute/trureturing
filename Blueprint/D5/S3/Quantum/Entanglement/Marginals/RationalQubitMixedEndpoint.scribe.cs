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
            H("Rank two for a maximally mixed endpoint and a rational Bloch length"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let c be a rational Bloch vector of rational length r with 0 < r < 1. "
                    + "Then half the identity and the trace-one Bloch matrix for c are "
                    + "partial traces of a positive semidefinite joint matrix of rank exactly "
                    + "two whose entries have rational real and imaginary parts.")),
                Paragraph(Text(
                    "Write 1 − r² as four rational squares p² + q² + s² + t² using "
                    + "Lagrange's theorem. Reorder so that D = p² + q² is positive. "
                    + "The vector (D, ps − qt, pt + qs) has squared length D(1 − r²), "
                    + "while (p, q, 0) has squared length D. A rational reflection carries "
                    + "the third coordinate unit vector to c/r. Apply it to (p, q, 0) "
                    + "to obtain v perpendicular to c without changing its squared length. "
                    + "These vectors satisfy the two witness equations of the rational "
                    + "qubit projector construction."))),
            DescribeRole.Theorem))));
}
