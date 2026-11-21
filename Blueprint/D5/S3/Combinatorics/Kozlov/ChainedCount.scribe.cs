using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class ChainedCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/ChainedCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For bounded vectors the last member of a chained tuple is recovered by clipping the sum at the coordinate capacities. This gives uniqueness and turns the transfer count into a count of distinct sums.",
        H("Counting distinct proper sums by their unique chained representatives"),
        Blocks(
            Node("cap", "cap", "Coordinate capacities", DescribeRole.Definition,
                "The full layer at a face size has the corresponding binomial coefficient as capacity."),
            Node("cap-pos", "cap_pos", "Capacities are positive throughout the coordinate space", DescribeRole.Theorem,
                "Each index lies at or below n, where the binomial coefficient is positive."),
            Node("firstdegree", "firstDegree", "The singleton coordinate", DescribeRole.Definition,
                "When n is positive the degree-one coordinate belongs to Fin of size n+1."),
            Node("bounded", "Bounded", "Vectors bounded by the full layers", DescribeRole.Definition,
                "Every coordinate is at most the corresponding capacity."),
            Node("fixed", "Fixed", "The first two coordinates are full", DescribeRole.Definition,
                "Use the full capacities in degrees zero and one."),
            Node("skeleton", "skeleton", "The f-vector of a full skeleton", DescribeRole.Definition,
                "Fill all coordinates through the given cutoff and put zero above it."),
            Node("skeleton-mem-snf", "skeleton_mem_SnF", "Positive skeletons are proper f-vectors", DescribeRole.Theorem,
                "Realize the vector by the downset of all subsets up to the given size. A positive cutoff includes every singleton."),
            Node("snf-bounded", "SnF_bounded", "Proper f-vectors are capacity bounded", DescribeRole.Theorem,
                "Every layer lies inside the family of all subsets of that size."),
            Node("snf-fixed", "SnF_fixed", "Proper f-vectors are full in degrees zero and one", DescribeRole.Theorem,
                "Use the absence of missing faces in those two degrees."),
            Node("le-top-of-pos", "le_top_of_pos", "Positive coordinates are bounded above by the top", DescribeRole.Theorem,
                "A positive coordinate belongs to the nonempty finite support over which the top is the maximum."),
            Node("vanish-of-top-lt", "vanish_of_top_lt", "Coordinates above the top vanish", DescribeRole.Theorem,
                "Positive occupancy would contradict the maximum's bound."),
            Node("indeg-le-of-lt-cap", "indeg_le_of_lt_cap", "A deficiency bounds the first missing degree", DescribeRole.Theorem,
                "The deficient coordinate belongs to the set whose minimum defines the first missing degree."),
            Node("full-below-indeg", "full_below_indeg", "Earlier bounded coordinates are full", DescribeRole.Theorem,
                "A below-capacity coordinate would force the minimum to be no higher than that coordinate."),
            Node("lt-indeg-iff", "lt_indeg_iff", "Fullness through a degree characterizes the first deficit", DescribeRole.Theorem,
                "Read the minimum of the deficient degrees or use the sentinel when that set is empty."),
            Node("top-skeleton", "top_skeleton", "The cutoff is the top of a full skeleton", DescribeRole.Theorem,
                "The cutoff is occupied by positivity of the binomial capacity and every later degree is zero."),
            Node("chained-sum-injective", "chained_sum_injective", "Unique representation by bounded chained tuples", DescribeRole.Theorem,
                "At each coordinate the final summand is the lesser of the total and the capacity. A deficit in that summand forces all previous summands to vanish in that coordinate. Peel off the last summand and induct on tuple length."),
            Node("topstate", "topState", "State indexed by the top degree", DescribeRole.Definition,
                "Represent top degrees one through n by states zero through n-1."),
            Node("topstate-val", "topState_val", "Recover the top from its state", DescribeRole.Theorem,
                "The singleton and upper bound on occupied degrees place the top in one through n. The state index is shifted down by one."),
            Node("cond", "cond", "Chaining as a transition condition", DescribeRole.Definition,
                "A candidate successor has first missing degree strictly greater than the top degree of the preceding state."),
            Node("chaing-iff", "chainG_iff", "Transition chains and chained tuples", DescribeRole.Theorem,
                "For fixed vectors the top-state index recovers the top degree, so the adjacent tests coincide."),
            Node("propervectors", "properVectors", "The finite set of actual proper f-vectors", DescribeRole.Definition,
                "Enumerate the images of finite downsets satisfying properness."),
            Node("mem-propervectors", "mem_properVectors", "The finite carrier realizes the literal vector set", DescribeRole.Theorem,
                "The finset image has precisely the f-vectors of the proper families."),
            Node("transfer", "transfer", "The transfer on f-vector top states", DescribeRole.Definition,
                "Count successor vectors by the state and first-missing-degree transition condition."),
            Node("card-of-chained-image", "card_of_chained_image", "Cardinality of an image of chained tuples", DescribeRole.Theorem,
                "Identify the admissible tuples with finite transfer chains and apply injectivity of the coordinate sum on that domain."),
            Node("proper-count-transfer", "proper_count_transfer", "The literal proper-sum count by transfer", DescribeRole.Theorem,
                "The chained subset has the full proper sumset as image by unconditional surjectivity. Its boundedness and fixed coordinates allow the chain cardinality formula."),
            Node("snf-terminal", "SnF_terminal", "The top-degree face forces a full simplex", DescribeRole.Theorem,
                "On an n-element ground set a face of size n is the whole ground set. Downward closure makes every subset a face."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-chained-count-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
