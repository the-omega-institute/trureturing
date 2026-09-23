using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class Erdos203NormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every original phase vector admits one common integer translation. This does not choose separate phases at separate points.",
        H("One common phase normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203normalization-0"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Normalization.normalize_original_phases"),
                H("Exhaustive common normalization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One translation normalizes the seven base phases to domains of sizes 1, 1, 2, 2, 4, 6 and 1, and transforms every original row event with that same translation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("erdos203-erdos203normalization-1"),
                DeclarationHandle.Create("D5/S3/Arith/Covering/Erdos203Normalization.six_row_kernel_coordinates"),
                H("Exact six-row homogeneous kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first six actual homogeneous congruences hold exactly at integer linear combinations of (360,0) and (228,24)."))),
                DescribeRole.Theorem)),
        []));
}
