using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualFilteredExplicitFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact averages of the actual explicit formula",
        H("Compact averages of the actual explicit formula"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-filtered-explicit-formula"),
            DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualFilteredExplicitFormula.actual_filtered_explicit_formula"),
            H("Compact averages of the actual explicit formula"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A compact probability average multiplies each actual zero coefficient by the exponential moment at that zero shifted by one. The formula retains the signed trivial-zero and constant correction."))),
            DescribeRole.Theorem))));
}
