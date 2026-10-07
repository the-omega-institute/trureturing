using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailSideSetup3W2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup3W2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail Side Setup3W2"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail side setup3w2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "tailSideHyp_of_gap", "tail Side Hyp of gap",
                "TailSideHyp from the initial gap alone. TailSideSetup2.tailSideHyp_of_rawData's proof with hraw.hA₀ and hraw.hr replaced by hypotheses — no window, and no new mathematics.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
