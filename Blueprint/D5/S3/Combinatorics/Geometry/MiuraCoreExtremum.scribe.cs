using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreExtremumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreExtremum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("Exact pointwise extremum correspondence"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracoreextremum-0"),
                DeclarationHandle.Create(Prefix + "contractAt_isSLM_of_h_max"), H("Maxima survive contraction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("An original ambient strict maximum at the image of a surviving cell is still a strict maximum after signed deletion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreextremum-1"),
                DeclarationHandle.Create(Prefix + "contractAt_isSLm_of_h_min"), H("Minima survive contraction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The same statement holds for ambient strict minima, including cells adjacent to the deleted column."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreextremum-2"),
                DeclarationHandle.Create(Prefix + "h_max_of_contractAt_isSLM"), H("No maximum is created"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every contracted strict maximum comes from a strict maximum at the corresponding original surviving cell."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreextremum-3"),
                DeclarationHandle.Create(Prefix + "h_min_of_contractAt_isSLm"), H("No minimum is created"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every contracted strict minimum comes from a strict minimum at the corresponding original surviving cell."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoreextremum-4"),
                DeclarationHandle.Create(Prefix + "contractAt_isSLE_iff"), H("Exact pointwise extremum correspondence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A surviving cell is a contracted strict extremum exactly when its image is an original strict extremum."))), DescribeRole.Theorem))));
}
