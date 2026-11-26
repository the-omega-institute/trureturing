using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaLaurentDivisorFormulaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a391810");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of the A391810 bilateral Laurent sum are divisor sums of signed "
            + "binomial coefficients.",
        H("Divisor formula for the A391810 Laurent coefficients"),
        Blocks(Describe.Lean(
            DescribeId.Create("hanna-laurent-divisor-formula"),
            DeclarationHandle.Create(
                "D5/S3/ArithSums/HannaLaurentDivisorFormula.divisor_formula"),
            H("Divisor formula and the first five columns"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For n≥1 let T(n,k) be the coefficient of x^(−k) in the formal Laurent "
                    + "expansion of the sum over j∈ℤ of x^j(1−x^j)^(n+j). Then T(n,0)=−1, and "
                    + "for every k≥1, T(n,k) is the sum over the divisors h of k with h≤n of "
                    + "(−1)^(k/h−1)·C(n−h,k/h−1), with C(a,b)=0 for b>a. Consequently "
                    + "T(n,1)=1, T(n,2)=−(n−2) for n≥2, T(n,3)=n(n−3)/2+2 for n≥3 and "
                    + "T(n,4)=−(n−3)(n²−3n+8)/6 for n≥4.")),
                Paragraph(Text(
                    "The coefficients of the nonpositive powers in the Laurent sum are those "
                    + "of the integer polynomial −1+Σ_{h=1}^{n} y^h(1−y^h)^(n−h) in the inverse "
                    + "variable y. "
                    + "Since (1−y)^m has coefficients (−1)^r·C(m,r), substituting y^h for y "
                    + "shows that y^h(1−y^h)^(n−h) contributes (−1)^(k/h−1)·C(n−h,k/h−1) to "
                    + "y^k exactly when h divides k, and nothing otherwise. Summing over h "
                    + "gives the divisor formula. The divisors of 1, 2, 3 and 4 give the "
                    + "five columns: for example "
                    + "T(n,4)=−C(n−1,3)−(n−2)+1=−(n−3)(n²−3n+8)/6."))),
            DescribeRole.Theorem))));
}
