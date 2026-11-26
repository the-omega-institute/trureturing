using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Weighted;

internal sealed class StrongDivisibilityBarrierDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/FactorialRatio/Weighted/StrongDivisibilityBarrier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong divisibility alone gives no uniform bound on compact factorial excess.",
        H("Unbounded excess at rank and window two"),
        Blocks(
            Paragraph(Text(
                "For a sequence u, define B(n) as the product of u(i) over 1<=i<=n. "
                + "Use B in the compact factorial products, with the same quotient factors "
                + "and legal parameters as in the ordinary factorial family. At r=s=2, "
                + "the legal parameters are b=0 and b=1. The full composition family has "
                + "two parts summing to four, corresponding to H=5 and M=1.")),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("A proposed uniform bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proposition asserts that a natural bound exists such that every "
                    + "sequence u positive at positive indices and satisfying "
                    + "gcd(u(a),u(b))=u(gcd(a,b)) for positive a,b has compact gcd at "
                    + "r=s=2, divided by its full-composition gcd at H=5,M=1, at most "
                    + "that bound. The gcds are taken over the actual finite families."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("No finite bound follows from strong divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem is the negation of the proposed bound. For each "
                        + "positive natural P, take u(n)=P at even indices and u(n)=1 "
                        + "at odd indices. The identity that 2 divides gcd(a,b) exactly "
                        + "when it divides both indices proves strong divisibility.")),
                    Paragraph(Text(
                        "The first five generalized factorials are 1,1,P,P,P^2. "
                        + "Every product from two parts summing to four is P or P^2, "
                        + "and the composition (1,3) attains P. Their gcd is therefore P. "
                        + "Both legal compact products equal P^2, so the exact quotient "
                        + "of the two gcds is P. Choosing P one larger than a proposed "
                        + "bound gives a contradiction.")),
                    Paragraph(Text(
                        "The pair r=s=2 already lies in the range r>=2, s<r^2. "
                        + "Consequently no error bound depending only on r and s can "
                        + "hold over all positive strong divisibility sequences. Uniform "
                        + "coefficient bounds in the weighted prime-power model supply "
                        + "additional information that strong divisibility does not provide."))),
                DescribeRole.Theorem))));
}
