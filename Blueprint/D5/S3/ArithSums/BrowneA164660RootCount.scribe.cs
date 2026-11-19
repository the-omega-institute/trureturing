using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class BrowneA164660RootCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/BrowneA164660RootCount.";
    private static readonly LibraryNoteRef Browne =
        LibraryNoteRef.Create("D5/L/Factorization/browne2016a164660");
    private static readonly LibraryNoteRef MaZhang =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026a164660roots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every window of n consecutive integers contains n/D_r(n) roots of k^r ≡ 0 (mod n), "
            + "so Browne's floor product extends to all exponents and translates.",
        H("Arbitrary-power root counts and translated floor products"),
        Blocks(
            Paragraph(Text("For positive n and r write n=∏p^(e_p). These statements are "
                + "Proposition 3 of H. Ma and W. Zhang on A. Browne's final formula for "
                + "OEIS A164660; the square, cube and fourth-power counts are OEIS A000188, "
                + "A000189 and A000190.")),
            Node("D", "The ceiling-exponent divisor", "D",
                "D_r(n)=∏_{p∣n} p^⌈e_p/r⌉, built from the ceiling exponents (e_p+r−1)/r.",
                DescribeRole.Definition),
            Node("C", "The root count", "C", "C_r(n)=n/D_r(n), with natural division.",
                DescribeRole.Definition),
            Node("dvd", "Roots of zero modulo n", "dvd_pow_iff",
                "For every integer k, n ∣ k^r if and only if D_r(n) ∣ k. For k=0 both hold. "
                + "Otherwise compare p-adic valuations: e_p ≤ r·v_p(k) is equivalent to "
                + "⌈e_p/r⌉ ≤ v_p(k), and D_r(n) has exponent ⌈e_p/r⌉ at each p.",
                DescribeRole.Theorem),
            Node("window", "Translated windows", "window",
                "For every integer s, over k=s+1,…,s+n the floor differences "
                + "⌊k^r/n⌋−⌊(k^r−1)/n⌋ sum to C_r(n), and the product of 1−2 times them is "
                + "(−1)^(C_r(n)). Each difference is 1 when n ∣ k^r and 0 otherwise, so the "
                + "sum counts multiples of D_r(n) in (s,s+n]; since D_r(n) ∣ n, that count is "
                + "⌊(s+n)/D_r(n)⌋−⌊s/D_r(n)⌋=n/D_r(n), including windows that contain zero or "
                + "negative integers.", DescribeRole.Theorem),
            Node("threshold", "When the count is n/rad(n)", "threshold",
                "For n>1, C_r(n)=n/rad(n) exactly when r ≥ e_p for every prime p ∣ n; for n=1 "
                + "both sides are 1. Indeed C_r(n)=n/rad(n) means D_r(n)=rad(n), that is "
                + "⌈e_p/r⌉=1 for every p ∣ n, and since e_p ≥ 1 this is e_p ≤ r.",
                DescribeRole.Theorem),
            Node("numerator", "Identification with A164660", "window_eq_numerator",
                "For r ≥ 2 and every integer s the translated product equals a(n+1). The "
                + "2-adic valuation of C_r(n) is e_2−⌈e_2/r⌉, which is positive exactly when "
                + "e_2 ≥ 2, so C_r(n) is even exactly when 4 ∣ n; the existing Chebyshev "
                + "evaluation gives a(n+1)=1 when 4 ∣ n and −1 otherwise.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("browne-a164660-root-count-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Browne, MaZhang),
            Blocks(Paragraph(Text(prose))), role);
}
