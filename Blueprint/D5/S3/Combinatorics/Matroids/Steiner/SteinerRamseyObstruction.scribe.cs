using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids.Steiner;

internal sealed class SteinerRamseyObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/Steiner/SteinerRamseyObstruction";
    private static readonly LibraryNoteRef Ramsey = LibraryNoteRef.Create(
        "D5/L/ArithUnits/nathanson2026sumintersections");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four coordinate triples of one colour force a missed fixed-pair switch maximum.",
        H("A Ramsey obstruction to simultaneous switch maxima"),
        Blocks(Describe.Lean(
            DescribeId.Create("steiner-no-common-maximum-in-some-power"),
            DeclarationHandle.Create(Module + ".noCommonMaximumInSomePower"),
            H("A fixed finite binary fibre fails on some power"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Ramsey),
            Blocks(
                Paragraph(Text("Fix a nontrivial finite centreless Steiner loop and a finite nontrivial binary fibre. Some positive coordinatewise power of the loop has the following property. For every normalized label table there are distinct nonidentity pivots and a second label table that gives more successful starts at the two zero lifts. One table therefore cannot attain all individual fixed-pair maxima.")),
                Paragraph(Text("Choose one nonidentity element and put it in each pair of coordinate positions to obtain an edge point. The three edge points of each coordinate triple form an original block. Finite Ramsey gives four coordinates whose four face blocks all carry the same label. These blocks form an alternating square with opposite pivots and zero return. Prescribing nonzero returns on every component away from the identity retains the old successful starts and adds a start from this square."))),
            DescribeRole.Theorem))));
}
