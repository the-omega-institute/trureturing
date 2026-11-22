using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointQuarticPrefixDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointQuarticPrefix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quartic variance bound for the four prefix averages of the Wu endpoint convolution.",
        H("Quartic positivity at the Wu endpoint"),
        Blocks(
            Paragraph(Text("At the tracial three-to-four endpoint, spectral majorization bounds the ordered eigenvalues of the signed two-mode output by the classical convolution. The four tail averages of that comparison vector are the candidates in the quartic maximization over the majorization polytope.")),
            Describe.Lean(DescribeId.Create("spectral-moment"), DeclarationHandle.Create(Owner + "spectralMoment"),
                H("Normalized spectral moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The moment of order j of a real four-vector is the sum of its jth powers divided by four."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("endpoint-prefix-average"), DeclarationHandle.Create(Owner + "endpointPrefixAverage"),
                H("Prefix average"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Keep the first k entries for k from zero to three and replace every remaining entry by the mean of that tail."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quartic-prefix"), DeclarationHandle.Create(Owner + "endpoint_quartic_prefix"),
                H("Quartic bound for every prefix average"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let x be any nonnegative nonincreasing real four-vector. Let y be any of the four prefix averages of the classical two-bit endpoint convolution of x with damping square root of two thirds. The product of the third moments of x and y minus the product of the second moment of x and fourth moment of y is at least one fifth of the square of the first moment of x times the square of its variance.")),
                    Paragraph(Text("For the constant prefix average, the estimate follows from Cauchy–Schwarz and nonnegativity of the variance. In the other three cases, expand in the smallest entry and the adjacent gaps of x. Splitting on the order of the two outer gaps gives polynomial expansions with nonnegative coefficients and weighted squares."))),
                DescribeRole.Theorem))));
}
