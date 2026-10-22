using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExpRatioCM;

internal sealed class PositiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive exponential coefficients and complete monotonicity.",
        H("The coefficient criterion"), Blocks(
            Describe.Lean(DescribeId.Create("exp-ratio-cm-positive-expansion"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.cm_of_nonnegative_exponential_expansion"),
                H("Nonnegative exponential expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A smooth function whose every derivative is represented by a nonnegative exponential moment has alternating derivatives of the required sign on the positive half-line."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-positive-cases"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two"),
                H("Low-index positive cases"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The low-index quotient cases reduce to nonnegative exponential coefficient data for both reciprocal families; the coefficient criterion then gives complete monotonicity."))),
                DescribeRole.Theorem))));
}
