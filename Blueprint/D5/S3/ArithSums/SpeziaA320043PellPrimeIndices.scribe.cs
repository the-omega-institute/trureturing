using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SpeziaA320043PellPrimeIndicesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/SpeziaA320043PellPrimeIndices.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026a320043squares");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a prime p, the A320043 value a(p − 1) is a square exactly when p is a term of A001075; "
            + "for p > 2 exactly when p = x_{2^h}, and then p ≡ 7 (mod 90).",
        H("Prime terms of the Pell sequence and square values of A320043"),
        Blocks(
            Describe.Lean(DescribeId.Create("a320043-pell-r"),
                DeclarationHandle.Create(Prefix + "r"),
                H("The Pell sequence A001075"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "r_0 = 1, r_1 = 2 and r_{j+2} = 4r_{j+1} − r_j; equivalently "
                        + "r_j = ((2 + √3)^j + (2 − √3)^j)/2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a320043-pell-x"),
                DeclarationHandle.Create(Prefix + "x"),
                H("The even-index subsequence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "x_0 = 1, x_1 = 7 and x_{t+2} = 14x_{t+1} − x_t, the first coordinates of "
                        + "(7 + 2√12)^t."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a320043-pell-prime-indices"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Square values at prime rows and Pell primes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For a(n) = Σ_{k=1}^{n} (n + 1 − k)² k / gcd(n + 1 − k, k)³ every quotient is "
                        + "exact. Moreover r_{2t} = x_t; a prime p has a(p − 1) a square exactly when p "
                        + "is a term of (r_j); a prime p > 2 has a(p − 1) a square exactly when "
                        + "p = x_{2^h} for some h ≥ 0, and then p ≡ 7 (mod 90); and every x_{2^h} is 7 modulo 90, "
                        + "which implies the source's residue 7 modulo 30.")),
                    Paragraph(Text(
                        "The terms r_j are Mathlib's Pell solutions for a = 2, the first coordinates of "
                        + "the powers of 2 + √3, and these are all natural first coordinates of "
                        + "solutions of X² − 3Y² = 1. With the prime-row criterion a(p − 1) square ⟺ p² − 12y² = 1 for "
                        + "p ≥ 5, a(1) = 1 and a(2) = 6, this gives the first equivalence: odd-index "
                        + "terms are even, and even-index terms pair with an even second coordinate. "
                        + "The identity r_{i+2k} + r_i = 2 r_{i+k} r_k shows that r_m divides r at every "
                        + "odd multiple of m, so with 1 < r_m < r_{mk} a prime x_t forces t = 2^h; the "
                        + "doubling r_{2k} = 2r_k² − 1 maps the residue 7 modulo 90 to itself, since "
                        + "2·7² − 1 = 7 + 90. This is "
                        + "Corollary 4 of H. Ma and W. Zhang, OEIS A320043, COMMENTS, revision 43 "
                        + "(2026); the index restriction is Zhu's (2011), the congruence and "
                        + "divisibility appear in Tiffin's 2016 OEIS comments, and the paper credits "
                        + "the odd-multiple argument for the subsequence r_{4j} to Andrews (2019)."))),
                DescribeRole.Theorem))));
}
