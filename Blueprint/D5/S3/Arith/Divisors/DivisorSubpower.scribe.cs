using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DivisorSubpowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The classical divisor subpower bound", H("The classical divisor subpower bound"),
        Blocks(Describe.Lean(DescribeId.Create("divisor-subpower-uniform"),
            DeclarationHandle.Create("D5/S3/Arith/Divisors/DivisorSubpower.card_divisors_subpower"),
            H("Every positive power bounds the divisor count"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real epsilon greater than zero there is a positive real constant C, depending only on epsilon, such that the number of positive divisors of every nonzero natural n is at most C times n to the real power epsilon. This is the classical divisor estimate, used by the Pascadi modular-zero partner bound; no novelty is claimed.")),
                Paragraph(Text("Write the divisor count as the product of e+1 over prime-power exponents. With r=2^epsilon>1, Bernoulli's inequality bounds e+1 by (1+1/(r-1))r^e. Only primes below a fixed epsilon-dependent cutoff need this constant. For all other primes p, e+1 is at most 2^e, which is at most (p^epsilon)^e. There are finitely many small primes, so their constants combine into a single uniform constant. Multiplying the prime-power contributions gives n^epsilon."))),
            DescribeRole.Theorem))));
}
