using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreContractDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreContract.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("Unit edges survive deletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorecontract-0"),
                DeclarationHandle.Create(Prefix + "frozenSlope"), H("The actual signed slope"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The slope is the row-zero height difference between the frozen column and its left neighbour."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorecontract-1"),
                DeclarationHandle.Create(Prefix + "frozenSlope_eq"), H("Slope transport to every row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a unit-edge height function, this same signed slope equals that horizontal difference in every row."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorecontract-2"),
                DeclarationHandle.Create(Prefix + "frozenSlope_pm"), H("The slope is a unit sign"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The actual frozen slope is either one or negative one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorecontract-3"),
                DeclarationHandle.Create(Prefix + "contractAt"), H("Signed deletion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Delete one internal frozen column and subtract its uniform signed slope from every column to its right."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorecontract-4"),
                DeclarationHandle.Create(Prefix + "contractAt_isHeight"), H("Unit edges survive deletion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every pair of adjacent surviving grid cells, the contracted height difference has absolute value one, including the new seam."))), DescribeRole.Theorem))));
}
