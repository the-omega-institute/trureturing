using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class LexShadowSizeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/LexShadowSize.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The recursive upper-shadow count for lexicographic segments satisfies two complementary inequalities. Together they control moving mass into an earlier component.",
        H("Upper-shadow counts and the block exchange"),
        Blocks(
            Node("sig", "sig", "Recursive upper-shadow size", DescribeRole.Definition,
                "Split the lex segment by the smallest element. The first block contains that element and the second block avoids it."),
            Node("sig-zero", "sig_zero", "The empty segment has empty shadow", DescribeRole.Lemma,
                "The recursion preserves zero mass."),
            Node("sig-n0-one", "sig_n0_one", "The shadow of the empty face", DescribeRole.Lemma,
                "The unique zero-element face has n one-element extensions."),
            Node("sig-full", "sig_full", "The shadow of a full layer", DescribeRole.Lemma,
                "For a full layer the recursion gives the capacity of the next degree."),
            Node("sig-r1", "sig_R1", "The first block recursion", DescribeRole.Lemma,
                "A segment fitting in the block containing the smallest element has the same shadow size as the corresponding segment on the remaining ground set in one lower degree."),
            Node("sig-r2", "sig_R2", "The second block recursion", DescribeRole.Lemma,
                "After the first block fills, its shadow contributes a full layer and the remaining mass is handled in the second block."),
            Node("sig-incr", "sig_incr", "The one-face shadow increment", DescribeRole.Lemma,
                "Adding one face of size k can add at most n-k upper-shadow faces, as shown by the block recursion."),
            Node("sig-r2-prime", "sig_R2_at_sum", "The recursion at a specified overflow", DescribeRole.Lemma,
                "Write the segment size as the capacity of the first block plus its overflow and use the second block formula."),
            Node("pp", "PP", "Exchange below capacity", DescribeRole.Definition,
                "The shadow cost of placing both masses in the earlier degree is bounded by their separate costs when they fit."),
            Node("qq", "QQ", "Exchange at capacity", DescribeRole.Definition,
                "The cost of a full earlier block and the remaining mass is bounded by the original cost when the earlier block fills."),
            Node("pq-zero", "PQ_zero", "Both exchanges on the empty ground set", DescribeRole.Lemma,
                "The capacities are zero or one and the upper-shadow sizes vanish."),
            Node("pq-succ-k-prime-0", "PQ_succ_second_degree_zero", "Exchange with a zero-degree second block", DescribeRole.Lemma,
                "The second mass is at most one. The one-face increment handles moving that mass."),
            Node("pq-all", "PQ_all", "The two block exchange inequalities", DescribeRole.Theorem,
                "Induct on the ground-set size and split each component at the capacity of the block containing the smallest element. The lower and upper overflow inequalities close the subproblems together."),
            Node("sig-p", "sig_P", "Below-capacity exchange in numerical form", DescribeRole.Theorem,
                "Specialize the first block exchange to the sum of the two input masses."),
            Node("sig-q", "sig_Q", "Exchange with overflow in numerical form", DescribeRole.Theorem,
                "Specialize the second block exchange to the sum in excess of the first capacity."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-lex-shadow-size-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
