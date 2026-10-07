using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class LargeConcentratedPrimeDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/LargeConcentratedPrimeDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concentrated pure prime at least 73 cannot occur under the "
            + "terminal-donor period and minimality hypotheses.",
        H("Large Concentrated Prime Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("large-concentrated-pure-prime-impossible"),
                DeclarationHandle.Create(Prefix + "no_large_concentrated_pure_prime"),
                H("Large concentrated pure primes are impossible under terminal-donor hypotheses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be a distinct odd covering system minimal first in class count "
                            + "and then in modulus sum. If F contains a pure prime class p with "
                            + "p at least 73, all its private points have one residue modulo 3, "
                            + "and every original modulus divides 9 * p^G * W with W coprime to 3p, "
                            + "then no such F exists.")),
                    Paragraph(Text(
                        "The private projection modulo 9 has at most three values. The existing "
                            + "terminal-donor descent applies because 27 * 3 + 1 is at most p + 9, "
                            + "and its strict modulus-sum decrease contradicts count minimality or "
                            + "same-count sum minimality.")),
                    Paragraph(Text(
                        "The result is conditional: it does not supply a pure prime, the period "
                            + "factorization, or the concentration hypothesis for an arbitrary cover."))),
                DescribeRole.Theorem))));
}
