using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicDyadicClockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index cubic Lucas blocks fill a single residue class modulo 128, with exact periods at every dyadic precision.",
        H("Exact dyadic clock of cubic Lucas blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-dyadic-lag"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicDyadicClock.golden_cubic_dyadic_lag"),
                H("Native exact dyadic lag"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For B_n equal to the squared Lucas trace at index 3^n plus three, "
                    + "and n greater than m at least one, the valuation of B_n minus B_m "
                    + "is seven plus the valuation of n minus m. The proof squares an integer "
                    + "iterate whose displacement is odd after extracting the claimed power "
                    + "of two, then sums the increments for the odd part of the lag."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-dyadic-least-period"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_least_period"),
                H("Least period at every dyadic precision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Modulo 2^a, the least positive period of the positive-index sequence is "
                    + "one through precision seven and 2^(a-7) thereafter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-dyadic-one-cycle"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicDyadicClock.dyadicBlock_one_cycle"),
                H("Each residue is visited exactly once per cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At precision 7+k, every residue equal to 19 modulo 128 occurs at a unique "
                    + "index in the first 2^k positive-index blocks. No odd prime divisor or "
                    + "choice of p-adic root is needed."))),
                DescribeRole.Theorem))));
}
