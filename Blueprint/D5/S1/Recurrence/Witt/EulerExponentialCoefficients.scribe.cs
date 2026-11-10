using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Witt;
internal sealed class EulerExponentialCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Witt/EulerExponentialCoefficients.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive and increasing coefficients of actual formal exponentials", H("Positive and increasing coefficients of actual formal exponentials"), Blocks(
            Paragraph(Text("The input g has rational values and only its positive indices occur. All coefficients are extracted from the literal formal exponential. The recurrence comes from its actual differential equation, rather than a recursive definition of a desired coefficient sequence.")),
            Node("coefficient_recurrence", "coefficient recurrence", "Coefficient extraction from X times the derivative gives the sum over k=0,...,n-1 with input g(k+1). At n=0 the two sides vanish.", DescribeRole.Theorem),
            Node("coefficient_positive", "coefficient positive", "Strong induction applies the positive-index recurrence. Each summand is nonnegative, and the summand with residual degree zero is strictly positive. The constant coefficient is one.", DescribeRole.Theorem),
            Node("coefficient_monotone", "coefficient monotone", "Compare the convolution equations at n and n+1. Their difference is controlled by g(1)-1 and the adjacent positive-index ghost differences, multiplied by already positive coefficients. This proves monotonicity on all natural degrees.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("eulerexponentialcoefficients-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
