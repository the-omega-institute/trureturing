using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ChenChenRootAnnulusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/ChenChenRootAnnulus.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026chenchenparity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For real m ≤ −3 and even n ≥ 2, every root of the row polynomial of the step-m Eulerian "
            + "triangle lies in the annulus between the least and largest consecutive coefficient "
            + "ratios, and these two ratios are reciprocal.",
        H("Root annulus of even rows"),
        Blocks(
            Describe.Lean(DescribeId.Create("chen-chen-no-root-outside"),
                DeclarationHandle.Create(Prefix + "no_root_outside"),
                H("Monotone Eneström–Kakeya bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "If 0 < b(0) ≤ b(1) ≤ … ≤ b(d), the polynomial ∑ b(k) w^k has no complex "
                    + "root with |w| > 1. Multiplying by 1 − w gives b(0) + ∑ (b(k+1) − b(k)) "
                    + "w^(k+1) − b(d) w^(d+1); at a root the last term would equal the sum of "
                    + "the others, whose modulus is at most b(d)|w|^d < b(d)|w|^(d+1)."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("chen-chen-root-annulus-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The root annulus"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For real m ≤ −3, every solution T of the step-m recursion and every even "
                    + "n ≥ 2, the ratios T(n,k)/T(n,k+1), 1 ≤ k < n, are positive; their least "
                    + "value L and largest value U satisfy L U = 1; and every complex root z of "
                    + "R(z) = ∑_{k=1}^{n} T(n,k) z^(k−1) satisfies L ≤ |z| ≤ U. Positivity comes "
                    + "from the sign theorem for even rows. The upper bound applies the monotone "
                    + "bound to the coefficients T(n,j+1) U^j. Reflection T(n,k) = T(n,n+1−k) "
                    + "makes the row palindromic, so 1/z is a root whenever z is, which gives "
                    + "the lower bound, and it pairs each ratio with its reciprocal, which gives "
                    + "L = 1/U. This is Corollary 5 of H. Ma and W. Zhang's proof of Chen and "
                    + "Chen's parity-positivity conjectures (DOI 10.5281/zenodo.23957560), an "
                    + "instance of the Eneström–Kakeya bound."))),
                DescribeRole.Theorem))));
}
