using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13CountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Counts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal P13 continuations retain the complete ranked vertex word at every height.",
        H("Concrete completion decompositions"),
        Blocks(
            Node("p13-p13counts-firstclosuredata", "First closure survivor data", "FirstClosureData",
                "The data records two survivor block sizes below d and a literal completion from their normalized base with d-1 closures. The first rank a must satisfy m at most a+1.", DescribeRole.Definition),
            Node("p13-p13counts-firstclosureequiv", "First closure bijection", "firstClosureEquiv",
                "For m positive, an initial run of k openings and its first legal rank uniquely give a and b, with k=a+b+1-m. The remaining suffix is a literal completion from blocks(a,b). The finite bounds follow from acceptance.", DescribeRole.Definition),
            Node("p13-p13counts-c-first-sum", "Finite first closure count", "c_first_sum",
                "For m positive, c(m,d) is the finite sum over a and b below d of g(a,b,d-1), restricted to m at most a+1. Impossible block sizes have zero count.", DescribeRole.Theorem),
            Node("p13-p13counts-emptysingleequiv", "Removing the first opening", "emptySingleEquiv",
                "For positive d, a completion from the empty base starts with an opening. Removing that letter gives exactly a completion from S(1), and prepending it is the inverse.", DescribeRole.Definition),
            Node("p13-p13counts-c-empty-single", "The empty base boundary", "c_empty_single",
                "For positive d, c(0,d) equals c(1,d).", DescribeRole.Theorem),
            Node("p13-p13counts-c-zero-zero", "The empty completion", "c_zero_zero",
                "The empty word is the unique zero degree completion from S(0).", DescribeRole.Theorem),
            Node("p13-p13counts-c-first-difference", "Separating the least legal rank", "c_first_difference",
                "For 1 at most m at most d, c(m,d) equals c(m+1,d) plus the sum over b below d of g(m-1,b,d-1). This separates the first closure rank m-1 from every larger rank.", DescribeRole.Theorem),
            Node("p13-p13counts-c-diagonal", "Closing only the old block", "c_diagonal",
                "The count c(m,m) is one. No new opening can occur, so the unique word closes the old block in descending rank order.", DescribeRole.Theorem),
            Node("p13-p13counts-actualcount", "Actual P13 matching counts", "actualCount",
                "The carrier is the P13 avoiding perfect matchings on Fin(2n), with the original source occurrence convention.", DescribeRole.Definition),
            Node("p13-p13counts-c-triangular", "Concrete triangular recurrence", "c_triangular",
                "For 1 at most m at most d, c(m,d) equals c(m+1,d) plus c(m-1,d-1) plus the sum for j from 1 to d-m of choose(m+j-2,m-1)c(j,d-m). The forced prefix bijection and the first closure bijection give the recurrence, with support bounding every sum.", DescribeRole.Theorem),
            Node("p13-p13counts-actualcount-continuation", "Continuation recurrence for actual matchings", "actualCount_continuation",
                "The actual matching carrier has one element for degree zero. For positive d, its count equals c(2,d) plus c(0,d-1) plus the sum of c(j,d-1) for j from 1 to d-1. The matching equivalence identifies the empty base continuation carrier with actual perfect matchings.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
