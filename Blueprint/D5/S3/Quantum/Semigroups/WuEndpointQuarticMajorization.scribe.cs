using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointQuarticMajorizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quartic prefix majorization and the normalized trace bound for the signed two-mode Wu map.",
        H("Quartic majorization at the Wu endpoint"),
        Blocks(
            Describe.Lean(DescribeId.Create("spectrum-four"), DeclarationHandle.Create(Owner + "Spectrum4"),
                H("Four-point spectrum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A four-point spectrum is a real vector indexed by zero through three."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quartic-sum"), DeclarationHandle.Create(Owner + "wuQuarticSum"),
                H("Quartic sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real coefficient κ, sum t⁴ − κt³ over the four entries t of the spectrum."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prefix-average-bound"), DeclarationHandle.Create(Owner + "wuQuartic_le_some_prefixAverage"),
                H("Comparison with a prefix average"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let v and y be nonincreasing real four-vectors, with v nonnegative. Suppose y has the same total sum as v and each of its three proper prefix sums is at most the corresponding prefix sum of v. For every real κ, some prefix average of v has quartic sum at least that of y.")),
                    Paragraph(Text("The majorization region is compact and invariant under permutations. Sort a maximizer and take its first slack prefix. The two entries straddling that prefix admit a small mass transfer in either direction. For a pair with mean m and half-difference d, stationarity and the quartic change under a transfer force d to vanish and m to be at most κ/2. Every later entry lies in the concavity interval from zero to κ/2, so Jensen’s inequality bounds the tail by its average. When all three prefixes are tight, the maximizer equals v."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prefix-maximum"), DeclarationHandle.Create(Owner + "wuQuarticPrefixMax"),
                H("Maximum over the four prefix averages"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each prefix length from zero to three, keep that prefix of v and replace the remaining entries by their mean. Take the maximum of the four resulting quartic sums."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prefix-maximum-bound"), DeclarationHandle.Create(Owner + "wuQuartic_le_prefixMax"),
                H("Quartic sum bounded by the prefix maximum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same ordering, nonnegativity, prefix inequalities and total equality, the quartic sum of y for each real κ is bounded above by the maximum over the four prefix averages of v."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("majorized-floor"), DeclarationHandle.Create(Owner + "endpoint_quartic_floor_of_majorization"),
                H("Variance bound for majorized spectra"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let x be a nonnegative nonincreasing real four-vector. Let y be nonincreasing, with the three proper prefix sums bounded by those of the classical Wu endpoint convolution of x and with the same total sum as that convolution. The product of the third moments of x and y minus the product of the second moment of x and fourth moment of y is at least one fifth of the squared first moment of x times its squared variance. Each moment is divided by four.")),
                    Paragraph(Text("For a positive second moment, take κ to be the third input moment divided by the second and use the quartic bound for the maximizing prefix average. If the second moment vanishes, the input vector vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-floor"), DeclarationHandle.Create(Owner + "A1_spectral_quartic_floor"),
                H("Variance bound for the signed endpoint spectrum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any positive semidefinite two-mode input X, take x to be its decreasing spectrum and y the decreasing spectrum of the signed Wu endpoint applied to X. The endpoint spectral majorization theorem supplies the prefix inequalities and total equality, so these spectra satisfy the same third- and fourth-moment variance bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("trace-moment"), DeclarationHandle.Create(Owner + "endpointTraceMoment"),
                H("Normalized trace moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural order k and each two-mode matrix, take the real part of the trace of its kth power, divided by four."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-floor"), DeclarationHandle.Create(Owner + "A1_quartic_floor"),
                H("Trace inequality at the tracial three-to-four endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive semidefinite two-mode matrix X, let Y be its image under the signed Wu endpoint. The product of the third normalized trace moments of X and Y minus the product of the second normalized trace moment of X and fourth normalized trace moment of Y is at least the squared first normalized trace moment of X times the squared normalized variance of X, divided by five.")),
                    Paragraph(Text("Unitary diagonalization of a Hermitian matrix identifies its normalized trace moments with its normalized spectral moments. Apply this identity to X and Y to transfer the spectral bound to the actual matrix map."))),
                DescribeRole.Theorem))));
}
