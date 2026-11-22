using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRoundingFullLimitDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/ActualRoundingFullLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact limit of the actual prime rounding sum.",
        H("The prime rounding sum at the square-root scale"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-prime-gap-limit"),
                DeclarationHandle.Create(Gid + ".actual_prime_gap_limit"),
                H("The normalized rounding sum tends to twice the square root of two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "As the real parameter L tends to positive infinity, multiply the sum "
                        + "of BoundaryPrimePrice.integerGap p (ActualRobinClockCovariance.g L) "
                        + "over every prime p ≤ the natural floor of L by √L log L. "
                        + "The result tends to 2√2. The theorem has no premises.")),
                    Paragraph(Text(
                        "On each fixed shell ε√L < p ≤ M√L with 0 < ε < √2 < M, "
                        + "the finite chamber error controls the difference between L times "
                        + "the exact gap and min(L/p², 1/2). The profile splits at p = √2√L, "
                        + "with the equality point assigned to the constant branch. "
                        + "The prime count gives √2 − ε and the reciprocal-square sum gives "
                        + "2(1/√2 − 1/M), so the actual shell limit is 2√2 − ε − 2/M.")),
                    Paragraph(Text(
                        "The global finite price bound controls the primes at or below ε√L. "
                        + "The global logarithmic bound controls the primes above M√L up to "
                        + "the original endpoint. The two tail bounds vanish as ε decreases "
                        + "to zero and M increases without bound."))),
                DescribeRole.Theorem))));
}
