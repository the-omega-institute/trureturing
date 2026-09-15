using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaChebyshevFiveDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Chebyshev factorial ratio is divisible by 5n+1 at every natural index.",
        H("Chebyshev Factorial Ratio Divisibility by 5n+1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-five"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FactorialRatio/"
                    + "BalaChebyshevFiveDivisibility.local_five"),
                H("Local five-modulus floor defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive modulus q, the floor defect is nonnegative; "
                    + "for q at least six dividing 5n+1, it equals one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bala-five-integrality"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FactorialRatio/"
                    + "BalaChebyshevFiveDivisibility.bala_five_integrality"),
                H("Bala's 5n+1 integrality clause"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n, including zero, (5n+1)(15n)!(10n)!(6n)! "
                        + "divides (30n)!n!. This is the 5n+1 clause of Peter Bala's "
                        + "August 2025 integrality conjectures for OEIS A211417, distinct "
                        + "from the previously proved 3n+1 and 30n-1 clauses.")),
                    Paragraph(Text(
                        "The known 3n+1 theorem supplies base factorial-ratio integrality. "
                        + "For prime powers q at least six dividing 5n+1, the floor defect "
                        + "is exactly one. The prime five does not divide 5n+1. At two, "
                        + "the factorial valuation equals that of the binomial coefficient "
                        + "8n choose 5n, and the adjacent-binomial identity supplies the "
                        + "extra factor. At three, the potentially missing contribution "
                        + "from q=3 is supplied at a different scale: the first power of "
                        + "three strictly above 10n is at most 30n and has floor defect "
                        + "one. It is larger than 5n+1, so this contribution does not "
                        + "duplicate any of the divisibility exponents."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility")),
        ]));
}
