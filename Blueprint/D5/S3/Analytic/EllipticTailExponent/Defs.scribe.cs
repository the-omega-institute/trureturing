using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EllipticTailExponent;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elliptic remainder parameter exponent", H("Definitions and supremum"), Blocks(
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-g6"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Defs.g6"),
                H("Coefficient polynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial g6 k a is a times the product of a+j and the product of 1-a+j, each over 0 <= j < k. Both products are one when k=0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-s"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Defs.S"),
                H("Finite truncation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial S n a sums g6 k a divided by (k+1)(k!)^2 for 0 <= k <= n. Its derivative is the ordinary real derivative of this finite polynomial."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-lambda10"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Defs.lambda10"),
                H("Remainder exponent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The function lambda10 n a is a/(1-a) times the quotient whose numerator is sin(pi a)+pi(1-a)cos(pi a)-pi(1-a)^2 deriv(S n)(a) and whose denominator is sin(pi a)-pi(1-a)S n a."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("elliptic-tail-exponent-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/EllipticTailExponent/Defs.claim"),
                H("Supremum for every truncation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, including zero, two is the least upper bound of the image of lambda10 n on the real interval (0,1/2]."))), DescribeRole.Definition))));
}
