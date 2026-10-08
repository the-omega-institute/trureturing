using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped5.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped5"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped5 to the stochastic ellipsoid construction.")),
            Node("claim-1", "mid_iff", "mid iff",
                "The middle case pins k to τ − 1. k < τ and ¬(k+1 ≤ τ−1) force τ−1 ≤ k < τ.", DescribeRole.Theorem),
            Node("claim-2", "sum_mid_eq", "sum mid eq",
                "Summing the middle term is a single evaluation.", DescribeRole.Theorem),
            Node("claim-4", "measurable_tau", "measurable tau",
                "τ is measurable — it is a stopping time, so {τ ≤ k} is measurable for every k, and a ℕ-valued map with measurable sublevel sets is measurable.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
