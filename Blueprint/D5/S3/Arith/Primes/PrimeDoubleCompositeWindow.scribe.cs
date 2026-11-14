using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class PrimeDoubleCompositeWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/PrimeDoubleCompositeWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The doubles of arbitrarily large primes have prescribed finite windows without primes.",
        H("Composite windows centered at prime doubles"),
        Blocks(
            Paragraph(Text(
                "A finite collection of nonzero integer offsets can be assigned distinct odd "
                + "prime divisors. For an offset j and a fresh prime r larger than its absolute "
                + "value, the congruence 2a + j = 0 modulo r has a nonzero solution a modulo r. "
                + "The Chinese remainder theorem combines these solutions into a residue class "
                + "coprime to the product modulus. Dirichlet's theorem then supplies arbitrarily "
                + "large primes in that class. The size bound makes each prescribed divisor "
                + "strictly smaller than the corresponding integer.")),
            Describe.Lean(
                DescribeId.Create("prime-double-composite-window"),
                DeclarationHandle.Create(Prefix + "exists_prime_double_composite_window"),
                H("An arbitrary window and an arbitrary lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural numbers H and B there is a prime p greater than both B and H "
                    + "such that every natural number between 2p - H and 2p + H, inclusive, is "
                    + "not prime. Nonzero offsets use the prescribed prime divisors. The central "
                    + "integer 2p is divisible by 2 and exceeds 2. A finite induction constructs "
                    + "the residue class while retaining coprimality with its modulus; the fresh "
                    + "prime at each step exceeds both the old modulus and the offset magnitude. "
                    + "The argument invokes Mathlib's Chinese remainder construction and its "
                    + "Dirichlet theorem for coprime natural residue classes."))),
                DescribeRole.Theorem)),
        []));
}
