using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class PrimeSupportGapDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/PrimeSupportGapDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A count-then-sum minimal distinct odd cover cannot omit a smaller prime "
            + "from its common-modulus support while containing a larger prime.",
        H("Prime-Support Gap Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-gap-in-prime-support"),
                DeclarationHandle.Create(Prefix + "no_gap_in_prime_support"),
                H("Minimal covers have no prime-support gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be an odd distinct covering system that is minimal first "
                            + "in its number of classes and then in the sum of its moduli. "
                            + "If p and q are odd primes with p < q, p does not divide "
                            + "the common modulus, and q does divide it, then the stated "
                            + "minimality hypotheses are inconsistent.")),
                    Paragraph(Text(
                        "The q-divisibility of the common least common multiple supplies "
                            + "a modulus divisible by q. Sum minimality turns that modulus "
                            + "into a pure q class. Since p divides no original modulus, "
                            + "the adjacent profile exchange with zero p- and q-heights "
                            + "produces a covering system with fewer classes, contradicting "
                            + "class-count minimality.")),
                    Paragraph(Text(
                        "The result is conditional on the stated minimality and support "
                            + "hypotheses; it is not an unrestricted covering theorem."))),
                DescribeRole.Theorem))));
}
