using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockExponentOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ten actual cubic golden blocks have certified primes of initial Fibonacci depth one.",
        H("Exponent-one primes in cubic golden blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-block-exponent-one"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockExponentOne."
                    + "checked_block_and_rank"),
                H("Non-powerful Lucas blocks and exact Fibonacci ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For ten selected positive levels j, reduce the actual Lucas recurrence modulo "
                    + "the square of a proposed prime p. The residue of L_(3^j)^2 + 3 is a "
                    + "nonzero multiple of p. A factored p - 1 and modular order tests certify "
                    + "primality. Each block is therefore non-powerful, and the chosen prime "
                    + "has exact Fibonacci rank 2 * 3^(j + 1) and valuation one at that rank."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-block-fibonacci-wss-test"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockExponentOne."
                    + "checked_wss_test"),
                H("Independent original Fibonacci test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each chosen prime is one or four modulo five. A separate fast-doubling "
                        + "calculation gives a nonzero multiple of p for F_(p - 1) modulo p squared. "
                        + "Thus p divides the original split-prime test value but p squared does not.")),
                    Paragraph(Text(
                        "The levels are 6, 7, 10, 15, 16, 17, 23, 26, 27 and 29. "
                        + "The calculation uses bounded residues, not complete block factorization. "
                        + "It neither excludes all-WSS blocks at other levels nor settles "
                        + "the existence of a Wall–Sun–Sun prime."))),
                DescribeRole.Theorem))));
}
