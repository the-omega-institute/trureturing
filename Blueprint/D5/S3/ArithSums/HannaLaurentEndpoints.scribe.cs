using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaLaurentEndpointsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a391810");
    private static readonly LibraryNoteRef MaZhang =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026a391810");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The A391810 coefficients at x^(-m^2) and x^(-(m^2-1)) in rows 2m-1 and 2m are signed "
            + "multiples of 1, m, 2 and 2m.",
        H("Endpoint and penultimate coefficients of the A391810 rows"),
        Blocks(Describe.Lean(
            DescribeId.Create("hanna-laurent-endpoints"),
            DeclarationHandle.Create("D5/S3/ArithSums/HannaLaurentEndpoints.endpoints"),
            H("Endpoint and penultimate coefficients"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source, MaZhang),
            Blocks(
                Paragraph(Text(
                    "Let T(n,k) be the coefficient of x^(−k) in the formal Laurent expansion of "
                    + "the sum over j∈ℤ of x^j(1−x^j)^(n+j). For m≥1, T(2m−1,m²)=(−1)^(m−1) and "
                    + "T(2m,m²)=(−1)^(m−1)·m. For m≥2, T(2m−1,m²−1)=2(−1)^m and "
                    + "T(2m,m²−1)=2m(−1)^m. These are Corollary 3 of H. Ma and W. Zhang; "
                    + "P. D. Hanna posed the entry conjectures in A391810.")),
                Paragraph(Text(
                    "By the divisor formula, T(n,k) is the sum over divisors h≤n of k of "
                    + "(−1)^(q−1)·C(n−h,q−1) with q=k/h, and a term can be nonzero only when "
                    + "h+q≤n+1. For k=m², hq=m² gives h+q≥2m with equality only at h=q=m. In "
                    + "row 2m−1 this leaves h=m, contributing (−1)^(m−1). In row 2m the term h=m "
                    + "contributes (−1)^(m−1)·C(m,m−1)=(−1)^(m−1)·m, and every other surviving h "
                    + "has h+q=2m+1, so its term is (−1)^(q−1); the swap h↔q pairs these terms, "
                    + "and since h+q is odd their signs are opposite, so they cancel. For "
                    + "k=m²−1 and m≥2, (h+q)²≥4hq=4m²−4>(2m−1)², so h+q≤2m forces h+q=2m; "
                    + "then (h−q)²=4, so {h,q}={m−1,m+1}. In "
                    + "row 2m−1 these two terms contribute (−1)^m each. In row 2m they contribute "
                    + "(−1)^m·C(m+1,m) and (−1)^m·C(m−1,m−2), that is 2m(−1)^m in total, and the "
                    + "remaining terms with h+q=2m+1 cancel in pairs as before."))),
            DescribeRole.Theorem))));
}
