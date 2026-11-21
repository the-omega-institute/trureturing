using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class ActualUnattainedAbscissaFilterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A short filter with one dominant actual zero pair",
        H("A short filter with one dominant actual zero pair"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-dominant-actual-zero-filter"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ActualUnattainedAbscissaFilter.exists_dominant_actual_zero_filter"),
            H("A short filter with one dominant actual zero pair"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("When the actual zero abscissa is unattained, a protected pair can have arbitrarily high ordinate and a real part strictly above every other surviving mode."))),
            DescribeRole.Theorem))));
}
