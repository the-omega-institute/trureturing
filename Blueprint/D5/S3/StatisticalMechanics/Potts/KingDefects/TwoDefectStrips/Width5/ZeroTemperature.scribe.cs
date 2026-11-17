using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5;

internal sealed class ZeroTemperatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The width-five proper block is the reflected-column restriction of the frozen width-six owner.",
        H("Width-five proper successors by restriction"),
        Blocks(
            Node("extend", "The reflected-column extension", "extend",
                "A width-five row is extended by reflecting its penultimate column into the sixth column. The new adjacent square reflects the preceding square, so it adds no new inequality.", DescribeRole.Definition),
            Node("raw5", "The width-five zero-defect relation", "raw5",
                "The raw successor relation records zero between-row and horizontal defects for width five.", DescribeRole.Definition),
            Node("proper-extend", "Properness is preserved by extension", "proper_extend",
                "The reflected extension has no horizontal defects exactly when the original width-five row has none.", DescribeRole.Theorem),
            Node("raw-extend", "Raw successors are preserved by extension", "raw_extend",
                "The width-six owner relation on reflected extensions is equivalent to the width-five raw relation.", DescribeRole.Theorem),
            Node("raw-iff-owner", "The restricted owner image", "raw_iff_owner",
                "Every width-five zero-defect successor is the restriction of an owner allowed shift, and every such restriction is a successor. The shift is recovered uniquely as r(0) xor p(0), giving fibre multiplicity one.", DescribeRole.Theorem),
            Node("transition-counts", "The zero-temperature transfer row", "transition_counts",
                "For every horizontally proper width-five source and every class column, the zero-budget successor sum equals the width-five transfer row.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
