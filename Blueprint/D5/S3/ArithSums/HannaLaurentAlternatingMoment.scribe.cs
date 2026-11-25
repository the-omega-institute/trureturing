using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class HannaLaurentAlternatingMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/HannaLaurentAlternatingMoment.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026a391810");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating first moments A_n=P_n'(−1) of A391810 have generating function "
            + "z(1−z+8z^2)/((1+z)^2(1−2z)^2).",
        H("A391810: the alternating first moment"),
        Blocks(
            Describe.Lean(DescribeId.Create("hanna-laurent-alternating-moment-def"),
                DeclarationHandle.Create(Prefix + "A"),
                H("The alternating first moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A n is −∑_{0≤k≤B_n} (−1)^k·k·rowEntry n k with B_n=⌊(n+1)/2⌋^2, where "
                    + "rowEntry n k is the coefficient of y^k in "
                    + "P_n(y)=−1+∑_{h=1}^n y^h(1−y^h)^(n−h), equal to the Laurent coefficient "
                    + "T(n,k) of x^(−k)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hanna-laurent-alternating-moment-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Formula (6) of A391810"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n≥1, A_n=−∑_k(−1)^k·k·T(n,k) with the literal Laurent coefficients, "
                    + "A_n=P_n'(−1), and the power series ∑_{n≥1}A_n z^n times "
                    + "(1+z)^2(1−2z)^2 equals z(1−z+8z^2). This is Corollary 6 of Ma and Zhang."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hanna-laurent-alternating-moment-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Proof through a closed form"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At y=−1 the summand y^h(1−y^h)^m has derivative h(m+2)2^(m−1) for odd h, "
                    + "and for even h it is −h, h or 0 according as m=0, m=1 or m≥2. Summing "
                    + "the odd terms, an auxiliary sum ∑ h·2^(n−h) and the even boundary terms "
                    + "by two-step recursions in n gives 27·P_n'(−1)=(15n−11)2^n+(11−30n)(−1)^n. "
                    + "The derivative of P_n at −1 is the alternating moment because P_n has "
                    + "degree at most B_n. The closed form satisfies "
                    + "A_n−2A_(n−1)−3A_(n−2)+4A_(n−3)+4A_(n−4)=0 for n≥4, and with "
                    + "A_0=0, A_1=1, A_2=1, A_3=13 this is the coefficient identity of "
                    + "(1−2z−3z^2+4z^3+4z^4)·∑A_n z^n=z−z^2+8z^3."))),
                DescribeRole.Theorem))));
}
