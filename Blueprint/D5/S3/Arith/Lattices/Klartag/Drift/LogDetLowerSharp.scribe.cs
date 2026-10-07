using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class LogDetLowerSharpDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Log Det Lower Sharp"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate log det lower sharp to the stochastic ellipsoid construction.")),
            Node("claim-3", "log_det_one_add_ge_sharp", "log det one add ge sharp",
                "LogDetVariance.log_det_one_add_ge with the sharp constant. The hypothesis is two-sided (|λ| ≤ r) where 94a's was one-sided (λ ≥ −1/2); the chain supplies it from the operator norm, which is what 94a's own proof already derived.", DescribeRole.Theorem),
            Node("claim-4", "log_det_add_ge_sharp", "log det add ge sharp",
                "LogDetVariance.log_det_add_ge with the sharp constant.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
