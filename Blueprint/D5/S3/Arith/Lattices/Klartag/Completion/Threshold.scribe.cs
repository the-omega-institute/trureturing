using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class ThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Threshold.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Threshold"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate threshold to the stochastic ellipsoid construction.")),
            Node("claim-2", "smallConst", "small Const",
                "The small-dimension constant at the adopted threshold: min_{1 ≤ m < 839} Vol(B^{m+1})/m².", DescribeRole.Definition),
            Node("claim-3", "const", "const",
                "The theorem's constant: c = min c₀ c₁, positive.", DescribeRole.Definition),
            Node("claim-4", "klartag_packing_of_phi", "klartag packing of phi",
                "Final.klartag_packing_of_hyps with the large-n branch in φ form. Final.Remaining is stated through Assembly.Lemma52, which is the *lattice*-level packaging; the Params route (Assembly.exists_phi_of_params) produces the φ directly, so this variant lets it feed the endgame without repackaging.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
