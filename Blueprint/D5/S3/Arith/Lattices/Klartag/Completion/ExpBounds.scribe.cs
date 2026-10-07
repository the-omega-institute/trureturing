using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class ExpBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/ExpBounds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Exp Bounds"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate exp bounds to the stochastic ellipsoid construction.")),
            Node("claim-3", "exp_three_le", "exp three le",
                "e³ ≤ 20.0856.", DescribeRole.Theorem),
            Node("claim-4", "exp_six_le", "exp six le",
                "e⁶ ≤ 403.429. Note this is not (e³)²: 20.0856² = 403.4313 overshoots.", DescribeRole.Theorem),
            Node("claim-5", "exp_half_le", "exp half le",
                "e^{1/2} ≤ 1.64873, from (e^{1/2})² = e < 2.7182818286 < 1.64873².", DescribeRole.Theorem),
            Node("claim-9", "exp_half_mul_KcR_le", "exp half mul Kc R le",
                "The hypothesis TerminalRatio.thetaTight_terminal_le takes, discharged. Verbatim its hKcR binder (TerminalRatio.lean:78).", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
