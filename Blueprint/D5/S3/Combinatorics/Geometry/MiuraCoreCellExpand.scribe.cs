using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreCellExpandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("Seam differences preserve signs"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorecellexpand-0"),
                DeclarationHandle.Create(Prefix + "cellExpand"), H("The surviving-cell injection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The map embeds the smaller physical rectangle in the original rectangle by skipping exactly the deleted internal column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracorecellexpand-1"),
                DeclarationHandle.Create(Prefix + "cellExpand_injective"), H("No surviving cells are identified"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The surviving-cell map is injective on the actual rectangular cell type."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorecellexpand-2"),
                DeclarationHandle.Create(Prefix + "cellExpand_surjOn"), H("Every surviving cell is represented"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every original cell outside the deleted column is the image of one cell of the smaller rectangle."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorecellexpand-3"),
                DeclarationHandle.Create(Prefix + "contractAt_isCanonicalHeight"), H("The origin stays normalized"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A normalized unit-edge height function remains normalized after signed deletion because the origin lies strictly before the removed internal column."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorecellexpand-4"),
                DeclarationHandle.Create(Prefix + "contractAt_diff_seam_LtoR"), H("Seam differences preserve signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Across the new seam the contracted height difference equals the corresponding original incident difference, using the uniform frozen slope."))), DescribeRole.Theorem))));
}
