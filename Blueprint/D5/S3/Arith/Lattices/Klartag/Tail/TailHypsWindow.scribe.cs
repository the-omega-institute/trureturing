using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailHypsWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailHypsWindow.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail Hyps Window"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail hyps window to the stochastic ellipsoid construction.")),
            Node("claim-6", "hprop_win", "hprop win",
                "The constraint process's tail at the window, named in the argument order both_sums_windowR2 reads. This is TailSideSetup3W2.tailSideHyp_latZR' at W := shellR, since windowOfR2 α p m g = (shellR α (m+1)).filter (· ∈ latZ p (m+1) g) definitionally.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
