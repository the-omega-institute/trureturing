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
                Blocks(Paragraph(Text("A smooth function whose every derivative is represented by nonnegative coefficients at nonnegative exponential frequencies has alternating derivatives of the required sign on the positive half-line."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-positive-cases"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Positive.cm_of_le_two"),
                H("Low-index positive cases"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed exponential moments give complete monotonicity of the zeroth moment. Differentiating the reciprocal three times gives the low-index closed forms on the entire positive half-line. The first two ratios are a nonnegative constant plus a nonnegative multiple of the zeroth moment. The third ratio is one plus four times that moment minus twice its value at twice the argument. At every derivative order the even terms of the moment series bound this subtraction, proving the required sign. This is the same coefficient positivity as coefficient four at positive odd frequencies and coefficient two at positive even frequencies. The zeroth ratio of the second family equals the zeroth moment, and its positive-index ratios agree with the first family."))),
                DescribeRole.Theorem))));
}
