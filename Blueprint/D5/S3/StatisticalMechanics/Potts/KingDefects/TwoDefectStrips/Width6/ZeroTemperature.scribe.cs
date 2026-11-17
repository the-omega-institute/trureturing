using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6;

internal sealed class ZeroTemperatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen six-column proper-colouring owner supplies the zero-temperature block.",
        H("Width-six proper successors from the zone owner"),
        Blocks(
            Node("offsets", "The translated row offsets", "offsets",
                "Offsets translate a proper row by its first entry, producing the owner zone word.", DescribeRole.Definition),
            Node("raw-iff-shift", "The exact allowed-shift image", "raw_iff_shift",
                "For a horizontally proper source row, the zero-defect successor rows are exactly the owner offset choices translated across that source.", DescribeRole.Theorem),
            Node("transition-counts", "The zero-temperature transfer row", "transition_counts",
                "For every horizontally proper source and every class column, the zero-budget successor sum equals the frozen width-six transfer row.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
