using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockLagValuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact valuations of differences between later Lucas blocks determine their congruence periods.",
        H("Exact lag valuations and periods of cubic Lucas blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-block-leading-unit"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.native_block_leading"),
                H("Leading term at two odd strides"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an odd Lucas seed and two odd strides, factor the difference "
                    + "of the squared traces using both the sum and the difference of the "
                    + "strides. Binomial lifting in the native golden integer ring "
                    + "identifies the leading residue in the ordinary integer difference. "
                    + "The identity does not require choosing a split p-adic root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-tail-lag"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_clock_valuation"),
                H("Exact valuation at every later lag"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let p divide the earlier cubic block B_i, and let h be its valuation there. "
                    + "For the later sequence starting with B_(i+1), the valuation of the "
                    + "difference at positive lag d is 2h plus the valuation of 9^d minus one. "
                    + "No assertion about which blocks have an exponent-one factor is implied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-tail-period"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockLagValuation.golden_cubic_tail_period"),
                H("All periods at every higher precision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At modulus p^(2h+r), a lag is a period of the later blocks exactly when "
                    + "the same power of nine returns to one modulo p^r. The onset of "
                    + "distinguishable residues is controlled by the earlier block depth; "
                    + "the resulting period is a separate multiplicative condition."))),
                DescribeRole.Theorem))));
}
