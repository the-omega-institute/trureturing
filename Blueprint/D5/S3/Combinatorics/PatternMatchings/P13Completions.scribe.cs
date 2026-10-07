using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13CompletionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Completions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal P13 continuations retain the complete ranked vertex word at every height.",
        H("Concrete completion decompositions"),
        Blocks(
            Node("p13-p13completions-closingcount", "Closing vertices", "closingCount",
                "The closing count records every future closure, irrespective of its rank.", DescribeRole.Definition),
            Node("p13-p13completions-openingcount", "Opening vertices", "openingCount",
                "The opening count records every future opening.", DescribeRole.Definition),
            Node("p13-p13completions-vertex-count", "Partition of the vertices", "vertex_count",
                "A word has length equal to its opening count plus its closing count.", DescribeRole.Theorem),
            Node("p13-p13completions-continuation-balance", "Endpoint balance", "continuation_balance",
                "Every accepted suffix closes exactly the old survivors, pending openings and future openings.", DescribeRole.Theorem),
            Node("p13-p13completions-continuation-rank-bound", "Bounds on literal ranks", "continuation_rank_bound",
                "Every closing rank in an accepted suffix is less than its total number of future closures.", DescribeRole.Theorem),
            Node("p13-p13completions-completion", "Literal completions", "Completion",
                "A completion is a finite word accepted from the given base with zero pending openings and with exactly d closing vertices. Acceptance requires no unfinished endpoint at the end.", DescribeRole.Definition),
            Node("p13-p13completions-completion-bounds", "Derived finite support", "completion_bounds",
                "A completion from s has s.size at most d, exactly d minus s.size openings, length twice d minus s.size, and every closing rank below d. These bounds follow from acceptance.", DescribeRole.Theorem),
            Node("p13-p13completions-completion-finite", "Finiteness of the literal carrier", "completion_finite",
                "Each completion embeds into a fixed length tuple of opening letters and closing ranks below d. Thus its carrier is finite.", DescribeRole.Theorem),
            Node("p13-p13completions-c", "Single block counts", "c",
                "The number c(m,d) counts literal completions from S(m).", DescribeRole.Definition),
            Node("p13-p13completions-g", "Normalized block counts", "g",
                "The number g(a,b,d) counts literal completions from blocks(a,b). Empty blocks are deleted, so g(a,0,d) equals c(a,d) and g(0,b,d) equals c(b,d).", DescribeRole.Definition),
            Node("p13-p13completions-completion-count-zero", "Impossible endpoint balances", "completion_count_zero",
                "A base with more old survivors than future closures has no completion.", DescribeRole.Theorem),
            Node("p13-p13completions-c-support", "Single block support", "c_support",
                "The count c(m,d) vanishes for m greater than d.", DescribeRole.Theorem),
            Node("p13-p13completions-openingrun", "A run of openings", "openingRun",
                "The word consists of k successive opening vertices.", DescribeRole.Definition),
            Node("p13-p13completions-closingcount-append", "Additive closing count", "closingCount_append",
                "Concatenation adds the closing counts of the two literal words.", DescribeRole.Theorem),
            Node("p13-p13completions-openingrun-closingcount", "Opening runs contain no closures", "openingRun_closingCount",
                "A run of opening vertices contributes zero to the closing count.", DescribeRole.Theorem),
            Node("p13-p13completions-accept-openingrun", "Pending opening transitions", "accept_openingRun",
                "Reading a run of n openings increases the separate pending count by exactly n.", DescribeRole.Theorem),
            Node("p13-p13completions-first-closure-exists", "Parsing the first closure", "first_closure_exists",
                "Any word with a positive closing count begins with a run of openings followed by its first closing letter and a remaining suffix.", DescribeRole.Theorem),
            Node("p13-p13completions-first-closure-unique", "Unique first closure parsing", "first_closure_unique",
                "The initial opening count, first closing rank and suffix are uniquely determined by the literal word.", DescribeRole.Theorem),
            Node("p13-p13completions-forcedprefix", "Descending forced prefix", "forcedPrefix",
                "For opening multiplicities t1 through ta, the prefix is U to the power t1 followed by rank a minus one, through U to the power ta followed by rank zero.", DescribeRole.Definition),
            Node("p13-p13completions-forcedprefix-accept", "Legal forced transitions", "forcedPrefix_accept",
                "For b positive, reading this prefix from blocks(a,b) with a equal to the multiplicity list length is equivalent to acceptance of the remaining word from S(b plus the sum of the multiplicities).", DescribeRole.Theorem),
            Node("p13-p13completions-forcedprefix-exhaustive", "Exhaustive forced closure parsing", "forcedPrefix_exhaustive",
                "Every accepted word from blocks(a,b), with b positive, consists of such a prefix with exactly a forced closures, followed by an accepted single block suffix.", DescribeRole.Theorem),
            Node("p13-p13completions-openingmultiplicities", "Weak compositions of openings", "OpeningMultiplicities",
                "A weak composition is a natural valued function on Fin(a) whose sum is t.", DescribeRole.Definition),
            Node("p13-p13completions-forceddata", "Finite prefix and suffix data", "ForcedData",
                "The data consists of t at most d, a weak composition into a opening counts, and a concrete completion from S(b+t) with d-a closures.", DescribeRole.Definition),
            Node("p13-p13completions-forcedcompletionequiv", "Bijection on literal two block completions", "forcedCompletionEquiv",
                "For b positive, the finite prefix data and literal completions from blocks(a,b) are equivalent. The inverse exhausts the forced first block. If d is less than a the data is empty, because its suffix would have a positive base and zero closures.", DescribeRole.Definition),
            Node("p13-p13completions-g-forced-sum", "Finite forced closure count", "g_forced_sum",
                "For b positive, g(a,b,d) is the sum over t from zero to d of choose(a+t-1,t) times c(b+t,d-a). The weak compositions use the symmetric power carrier, and impossible terms vanish by endpoint balance.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
