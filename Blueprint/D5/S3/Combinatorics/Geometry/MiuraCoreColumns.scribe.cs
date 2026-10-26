using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreColumnsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreColumns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("Symmetric columns have no extrema"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorecolumns-0"),
                DeclarationHandle.Create(Prefix + "activeColumn"), H("Occupied columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A column is occupied exactly when an actual strict minimum or maximum lies in it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorecolumns-1"),
                DeclarationHandle.Create(Prefix + "numFrozenRuns"), H("Maximal unoccupied runs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A run starts at an unoccupied column whose predecessor is occupied, with a separate condition at the first physical column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorecolumns-2"),
                DeclarationHandle.Create(Prefix + "frozenColumn"), H("Symmetric internal columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Both horizontal neighbours exist and their heights sum to twice the middle height in every row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorecolumns-3"),
                DeclarationHandle.Create(Prefix + "numActiveColumns_le_numExtrema"), H("Occupied columns are bounded by extrema"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Projecting each actual extremum onto its column covers all occupied columns, so their number is at most the number of extrema."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorecolumns-4"),
                DeclarationHandle.Create(Prefix + "numFrozenRuns_le"), H("Runs lie between occupied columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("If both boundary columns are occupied, the number of maximal unoccupied runs plus one is at most the number of occupied columns."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorecolumns-5"),
                DeclarationHandle.Create(Prefix + "frozenColumn_not_active"), H("Symmetric columns have no extrema"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("In a symmetric interior column, the two horizontal neighbours exclude both signs of strict local extremum. No unit-edge assumption is needed for this implication."))), DescribeRole.Theorem))));
}
