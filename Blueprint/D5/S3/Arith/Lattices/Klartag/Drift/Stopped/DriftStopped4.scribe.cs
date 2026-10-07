using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped4Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped4.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped4"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped4 to the stochastic ellipsoid construction.")),
            Node("claim-3", "stoppedErr_split", "stopped Err split",
                "The two cases, kept apart. Each summand vanishes outside its own case, so the first sums by the freeze count and the second by the disjointness of {τ = k+1}.", DescribeRole.Theorem),
            Node("claim-7", "SlackHyp", "Slack Hyp",
                "The numeric side condition the value of B closes: the middle case's total, C₁·2B, must fit the slack the existence step has. With C₁ ≤ 3n and B ≈ n^{−3.5} this is ≈ 6 n^{−2.5}.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
