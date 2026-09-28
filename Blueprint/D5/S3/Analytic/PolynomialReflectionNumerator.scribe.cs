using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PolynomialReflectionNumeratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial reflection gives exact-degree palindromic generating-series numerators.",
        H("Polynomial Reflection and Numerator Reciprocity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("polynomial-reflection-numerator"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/PolynomialReflectionNumerator."
                    + "palindromic_numerator_of_reflection"),
                H("Reflection gives a palindromic numerator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real polynomial p of degree at most n, normalized by p(0)=1 "
                    + "and satisfying p(-1-x)=(-1)^n p(x), has a generating-series "
                    + "numerator of degree exactly n over (1-z)^(n+1). Its "
                    + "coefficients at j and n-j coincide. Expansion in the "
                    + "binomial polynomial basis converts reflection of p into "
                    + "coefficient reversal of the numerator."))),
                DescribeRole.Theorem))));
}
