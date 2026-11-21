using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class WeightedFilterCDFDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compact probability correction for the Robin tail",
        H("A compact probability correction for the Robin tail"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-compact-probability-weighted-tail-average"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/WeightedFilterCDF.exists_compact_probability_weighted_tail_average"),
            H("A compact probability correction for the Robin tail"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A probability supported in a fixed forward interval induces a corrected probability on the same interval. The corrected average of the weighted tail equals a kernel integral of the original forward average."))),
            DescribeRole.Theorem))));
}
