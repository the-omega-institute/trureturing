using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AffinePolynomialPairBalaDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/AffinePolynomialPairBalaDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a208509pair");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binomial column family h_d satisfies Bala's terminating identity, and for moduli coprime to "
            + "(d − 1)! the divisors of h_d(m) are exactly those of its product formula.",
        H("Bala's terminating identity and divisibility for h_d"),
        Blocks(
            Describe.Lean(DescribeId.Create("a208509-bala-divisibility-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Terminating identity and divisibility"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Here h_d(m) = [z^m](1 + z)/(1 − z)^d. For every d ≥ 0 and n ≥ 1, the sum over "
                        + "0 ≤ j ≤ n of (−1)^j h_d(j) · n(n − 1)⋯(n − j + 1) / ((n + d)(n + d + 1)⋯(n + d + j − 1)) "
                        + "vanishes, empty products being 1. For d ≥ 2 and q coprime to (d − 1)!, q divides h_d(m) "
                        + "exactly when q divides (2m + d − 1)(m + 1)(m + 2)⋯(m + d − 2). Hence q divides h_d(m) "
                        + "when q divides m + j for some 1 ≤ j ≤ d − 2, or q divides 2m + d − 1; in particular "
                        + "this holds for q = p^e with p > d − 1 prime and every e ≥ 0. The converse of this "
                        + "sufficient condition fails: h_3(2) = 9, while 9 divides neither m + 1 = 3 nor "
                        + "2m + d − 1 = 6.")),
                    Paragraph(Text(
                        "Multiplying the j-th term by (2n + d − 1)!/(n!(n + d − 1)!) turns it into "
                        + "(−1)^j h_d(j) C(2n + d − 1, n − j). The alternating series of h_d is (1 − z)/(1 + z)^d, so "
                        + "these integers are the coefficients of z^n in (1 − z)(1 + z)^{2n − 1}, namely "
                        + "C(2n − 1, n) − C(2n − 1, n − 1) = 0. For divisibility, (d − 1)! h_d(m) = "
                        + "(2m + d − 1)(m + 1)(m + 2)⋯(m + d − 2), and q is coprime to (d − 1)!, so it can be cancelled.")),
                    Paragraph(Text(
                        "The hypotheses are needed. At n = 0 the sum is h_d(0) = 1. For d = 1, m = 2 and "
                        + "q = 4, q divides 2m + d − 1 = 4 and is coprime to 0! = 1, but h_1(2) = 2. For d = 4, "
                        + "m = 1 and q = 2, q divides m + 1 but h_4(1) = 5; here q is not coprime to 3! = 6. "
                        + "The source states the identity for d ≥ 2 and the divisibility for prime powers with "
                        + "e ≥ 1; it is Corollary 7 of H. Ma and W. Zhang's note on A208509 "
                        + "(DOI 10.5281/zenodo.24211281), which credits the identity to Bala (2019) and notes that the "
                        + "prime-power case for d = 6 contains Adamchuk's 2007 divisibility assertions in A005585."))),
                DescribeRole.Theorem))));
}
