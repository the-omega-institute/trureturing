using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class CutRunCorrespondenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Parking/CutRunCorrespondence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/recioui2026circular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut and uncut coordinates identify the circular first-free process with the classical linear parking run.",
        H("Cut-Run Correspondence"),
        Blocks(
            Node("cut-a-circular-spot", "Cut the circle at a vacancy", "cutSpot",
                "The linear coordinate of x relative to vacancy j is the canonical natural value of "
                    + "x-j, ranging from zero through n."),
            Node("uncut-a-linear-spot", "Restore a cut coordinate", "uncutSpot",
                "A natural linear coordinate p is placed back on the circle as j+p."),
            Theorem("scanner-cut-comparison", "Cutting identifies the two scanners", "firstFree_cut",
                "Assume the occupied list has no duplicates, its length is at most n, j is unoccupied, "
                    + "and the circular scanner does not land at j. Cutting at j sends the circular "
                    + "first-free result to the supplier's linear parkStep. The proof rotates j to zero, "
                    + "orders every skipped offset before the cut, and applies the supplier's vacancy "
                    + "and skipped-position specification."),
            Theorem("scanner-avoids-vacancy", "The reverse scanner does not cross the vacancy",
                "firstFree_ne_vacancy",
                "Let 1 <= p <= q <= n and suppose uncutSpot j q is free. The first circular free spot "
                    + "from uncutSpot j p cannot be j: the free offset q-p occurs strictly before the "
                    + "offset n+1-p that returns to the cut."),
            Theorem("forward-cut-simulation", "Cutting simulates the complete one-choice run", "cut_run",
                "Assume a duplicate-free occupied state, enough remaining capacity, an unoccupied cut j, "
                    + "and a future one-choice run that never lands at j. Then supplier parkFrom on the "
                    + "cut occupied list and cut anchors equals the cut circular landing list. The same "
                    + "induction also proves that every input anchor differs from j.")),
        []));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        string prose) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock Theorem(
        string id,
        string title,
        string declaration,
        string prose) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}

