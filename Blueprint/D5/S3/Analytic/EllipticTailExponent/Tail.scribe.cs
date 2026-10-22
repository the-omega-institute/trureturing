using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EllipticTailExponent;

internal sealed class TailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elliptic coefficient tails", H("Finite products and the sine remainder"), Blocks(
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-d"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Tail.d"),
                H("Normalized coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural k and real a, d k a is the product of a+j times the product of 1-a+j over 0 <= j < k, divided by (k!)^2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-t"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Tail.t"),
                H("Truncation summands"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The summand t k a is a d k a/(k+1). It is nonnegative for 0<a<=1/2. The finite truncation S n a sums these terms for 0<=k<=n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-d-product"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Tail.d_product"),
                H("Finite Euler product"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N and every real a, (N+1)d(N+1,a) equals a(1-a/(N+1)) times the product of 1-a^2/(j+1)^2 over 0<=j<N. The normalized coefficient recurrence gives the identity by induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-tail-eq-tsum"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Tail.tail_eq_tsum"),
                H("The analytic remainder as a coefficient tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n and every real a with 0<a<=1/2, sin(pi a)/(pi(1-a))-S n a equals the convergent sum of t(k+n+1,a) over natural k. The coefficient recurrence telescopes the finite sum to its weighted endpoint. The finite Euler product converges by the sine product theorem; nonnegativity identifies the sum, and removing the first n+1 terms gives the stated remainder."))), DescribeRole.Theorem))));
}
