using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class AlternatingFactorialSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/AlternatingFactorialSum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating factorial convolution for every pair of natural parameters.",
        H("Alternating Factorial Sum"),
        Blocks(
            Paragraph(Text(
                "The source is restored byte-for-byte from the archived matching-SOS report. "
                + "It supplies equation (5) for the monomial-fiber route; no matching-polynomial "
                + "coefficient formula follows without the separate combinatorial fiber proof.")),
            Describe.Lean(
                DescribeId.Create("opposite-series-product"),
                DeclarationHandle.Create(Prefix + "opposite_inv_series_mul"),
                H("Opposite Series Product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over every commutative ring, the two opposite negative-binomial series "
                    + "multiply to the series obtained by substituting the squared variable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-choose-convolution"),
                DeclarationHandle.Create(Prefix + "alternating_choose_convolution"),
                H("Alternating Choose Convolution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coefficient extraction gives the alternating binomial convolution "
                    + "for arbitrary natural d and h over the rationals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-factorial-identity"),
                DeclarationHandle.Create(Prefix + "alternating_factorial_sum"),
                H("Alternating Factorial Identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum over ell from zero to 2h of (-1)^ell choose(2h,ell) "
                    + "(d+ell)! (d+2h-ell)! equals (2h)! d! (d+h)! / h!. "
                    + "Both natural parameters remain universally quantified."))),
                DescribeRole.Theorem))));
}
