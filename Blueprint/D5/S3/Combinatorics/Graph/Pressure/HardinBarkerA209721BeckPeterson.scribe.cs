using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Pressure;

internal sealed class HardinBarkerA209721BeckPetersonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Pressure/HardinBarkerA209721BeckPeterson.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hardinbarker2012a209721");
    private static readonly LibraryNoteRef MaZhang =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a209723");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-column distinct-clockwise-difference count is A029744(n+1)+1, satisfies "
            + "a(n) = 2a(n−2)−1, and counts the integer third sides of a triangle with sides "
            + "a(n−1), a(n−2).",
        H("Beck and Peterson identities for the three-column array count"),
        Blocks(
            Describe.Lean(DescribeId.Create("a029744"),
                DeclarationHandle.Create(Prefix + "IsA029744"),
                H("The numbers 2^k and 3·2^k"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "IsA029744 m holds when m is 2^k or 3·2^k for some natural k. OEIS A029744 "
                    + "lists these numbers in increasing order with offset 1, so the term "
                    + "A029744(n+1) is Nat.nth IsA029744 n: 1, 2, 3, 4, 6, 8, 12, ..."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("third-sides"),
                DeclarationHandle.Create(Prefix + "thirdSides"),
                H("Integer third sides of a triangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For rationals x and y, thirdSides x y is the set of positive integers c "
                    + "with c < x + y, x < y + c and y < x + c, that is, the integer lengths c "
                    + "for which x, y, c are the sides of a nondegenerate triangle."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("beck-peterson-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Beck's and Peterson's assertions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Here a n is one quarter of the number of (n+1) × 3 arrays over 0..2 whose "
                    + "consecutive 2 × 2 squares have distinct clockwise edge differences "
                    + "(OEIS A209721). The claim has three parts. For n ≥ 1, a n = A029744(n+1) + 1 "
                    + "(G. Beck, 2022). For n ≥ 3, a n = 2 a(n−2) − 1 (R. L. Peterson, 2020). For "
                    + "n ≥ 3, the third sides for the sides a(n−1) and a(n−2) are exactly "
                    + "a(n−1) − a(n−2) + 1 ≤ c ≤ a(n−1) + a(n−2) − 1, and there are a n of them "
                    + "(Peterson). OEIS records the first two as empirical observations or "
                    + "conjectures."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("beck-peterson"),
                DeclarationHandle.Create(Prefix + "beck_peterson"),
                H("The Beck and Peterson identities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source, MaZhang),
                Blocks(Paragraph(Text(
                    "The established count satisfies a(m+4) = a(m+3) + 2a(m+2) − 2a(m+1) with "
                    + "a(1) = 3, a(2) = 4, a(3) = 5. The recurrence says "
                    + "a(m+4) − 2a(m+2) = a(m+3) − 2a(m+1), so a(n+2) − 2a(n) keeps its value "
                    + "a(3) − 2a(1) = −1, which is Peterson's formula. The sequence 1, 2, 3, ... in "
                    + "which each later term is twice the term two places earlier is strictly "
                    + "increasing and has "
                    + "range {2^k} ∪ {3·2^k}, so it is the increasing enumeration A029744(n+1); "
                    + "both it plus one and a satisfy the two-step law with the same first two "
                    + "values, which is Beck's formula. Since a is increasing, the triangle "
                    + "inequalities for integer c reduce to a(n−1) − a(n−2) < c < "
                    + "a(n−1) + a(n−2), an interval of 2a(n−2) − 1 = a(n) integers. The written "
                    + "proof is Corollary 1 of H. Ma and W. Zhang (doi:10.5281/zenodo.23903301)."))),
                DescribeRole.Theorem))));
}
