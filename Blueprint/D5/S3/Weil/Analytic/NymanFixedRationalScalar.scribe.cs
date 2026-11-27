using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanFixedRationalScalarDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanFixedRationalScalar";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed rational scalar forces the Riemann hypothesis",
        H("The fixed rational scalar forces the Riemann hypothesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar"),
                DeclarationHandle.Create(Owner + ".scalar"),
                H("The finite rational shell sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar at N is the sum of μ(n)bRat(n/N) over N < n ≤ 2N, with the weights and the sum evaluated over the rationals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("scalar-square-root"),
                DeclarationHandle.Create(Owner + ".ScalarSquareRoot"),
                H("Square-root growth with arbitrary positive slack"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each ε > 0 there is a nonnegative constant C such that the absolute value of the scalar is at most C N^(1/2+ε) for every positive natural N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rh-of-scalar"),
                DeclarationHandle.Create(Owner + ".rh_of_scalar"),
                H("The bound implies the Riemann hypothesis"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite rational sums agree with the real-scale test at t = 1/N. The Lipschitz estimate transfers growth from these samples to all small positive t. A zeta zero in the right half-strip would force a zero of the explicit Mellin product, which is nonvanishing there. Right-half-strip reduction gives the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
