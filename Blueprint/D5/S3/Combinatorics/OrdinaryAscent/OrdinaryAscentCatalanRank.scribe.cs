using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrdinaryAscent;

internal sealed class OrdinaryAscentCatalanRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanRank.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/mazhang2026ordinary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.",
        H("Ordinary ascent CatalanRank"),
        Blocks(
            Node("sites-shape", "sites shape", "sites_shape",
                "For a nonempty actual avoiding word, every admissible site is at most the last value or equals the fresh upper bound. Combined with last_mem_sites and fresh_mem_sites, these are the two largest sites.", DescribeRole.Theorem),
            Node("sites-append", "sites append", "sites_append",
                "On an actual nonempty avoiding prefix and a legal appended value x, the complete new site set consists of the old sites at most x and the new fresh upper bound.", DescribeRole.Theorem),
            Node("rank", "rank", "rank",
                "The zero-based rank of a value is the number of admissible sites strictly below it.", DescribeRole.Definition),
            Node("card-sites-append", "card sites append", "card_sites_append",
                "Appending a legal value of rank i to an actual nonempty avoiding prefix gives exactly i+2 legal sites. Descent, repetition and fresh ascent are all included.", DescribeRole.Theorem),
            Node("rank-lt-card", "rank lt card", "rank_lt_card",
                "The rank of an actual site lies in the finite rank interval.", DescribeRole.Theorem),
            Node("rank-strictMono", "rank strictMono", "rank_strictMono",
                "If x is an actual site and x<y, then the number of sites below x is strictly smaller than the number below y.", DescribeRole.Theorem),
            Node("rankedSites", "rankedSites", "rankedSites",
                "Ranking is a genuine equivalence from actual admissible sites to the finite interval of their ranks. Its inverse un-ranks actual letters.", DescribeRole.Definition),
            Node("unrank", "unrank", "unrank",
                "Inverse ranking on the actual finite rank interval, with a default zero only outside that interval.", DescribeRole.Definition),
            Node("unrank-spec", "unrank spec", "unrank_spec",
                "At every valid rank, unranking returns an actual admissible value with exactly that rank.", DescribeRole.Theorem),
            Node("unrank-rank", "unrank rank", "unrank_rank",
                "Unranking the rank of an actual admissible letter returns the same letter.", DescribeRole.Theorem),
            Node("card-sites-le", "card sites le", "card_sites_le",
                "For a nonempty word, the number of auxiliary sites is at most length plus one.", DescribeRole.Theorem),
            Node("singleton-word", "singleton word", "singleton_word",
                "A singleton word satisfies the actual ordinary Catalan-pair predicate exactly when its value is zero.", DescribeRole.Theorem),
            Node("root-sites", "root sites", "root_sites",
                "The unique nonempty root zero has the two sites zero and one. This initial condition is consumed by the code invariant.", DescribeRole.Theorem),
            Node("eastCode", "eastCode", "eastCode",
                "Read actual letters from left to right. At a letter following a prefix of length m, record m minus that letter's rank in the prefix site set. The initial zero records zero.", DescribeRole.Definition),
            Node("eastCode-append", "eastCode append", "eastCode_append",
                "Appending a letter appends exactly the length-minus-rank code entry.", DescribeRole.Theorem),
            Node("eastCode-length", "eastCode length", "eastCode_length",
                "The rank-complement code has exactly the same length as the original word.", DescribeRole.Theorem),
            Node("eastCode-valid", "eastCode valid", "eastCode_valid",
                "For an actual avoiding word, the code is a nondecreasing inversion sequence. For a nonempty word, its site count plus the last code entry is length plus one. The invariant is proved at every producer.", DescribeRole.Theorem),
            Node("fromEastCode", "fromEastCode", "fromEastCode",
                "Starting from zero, reconstruct each next letter by unranking prefix length minus the new east count in the actual current site set.", DescribeRole.Definition),
            Node("fromEastCode-append", "fromEastCode append", "fromEastCode_append",
                "The inverse construction retains the unique initial zero and appends the unranked value at each later code entry.", DescribeRole.Theorem),
            Node("fromEastCode-eastCode", "fromEastCode eastCode", "fromEastCode_eastCode",
                "Encoding an actual ordinary avoiding word and then reconstructing gives the original word, including the empty word.", DescribeRole.Theorem),
            Node("fromEastCode-valid", "fromEastCode valid", "fromEastCode_valid",
                "For every nondecreasing inversion sequence, reconstruction is an actual ordinary Catalan-pair word of the same length, and encoding recovers the original inversion sequence.", DescribeRole.Theorem),
            Node("mem-catalan-avoiders", "mem catalan avoiders", "mem_catalan_avoiders",
                "The literal two-pattern finite length class is precisely length equality and the CatalanWord predicate.", DescribeRole.Theorem),
            Node("catalanMonoEquiv", "catalanMonoEquiv", "catalanMonoEquiv",
                "Actual ordinary 10-1,20-1 avoiders of length n are equivalent to nondecreasing inversion sequences of length n. Both inverses and all carrier predicates are proved; this intermediate class is not assumed to equal the avoiding words.", DescribeRole.Definition),
            Node("dyckEquiv", "dyckEquiv", "dyckEquiv",
                "Compose the actual-word rank equivalence with the existing monoDyckEquiv on its exact nondecreasing inversion-sequence domain. The result is an equivalence with actual Mathlib Dyck words of semilength n, including n=0.", DescribeRole.Definition),
            Node("dyckEquiv-forward", "dyckEquiv forward", "dyckEquiv_forward",
                "The forward Dyck list is exactly the existing dyckSteps encoding of the proved rank-complement code.", DescribeRole.Theorem),
            Node("dyckEquiv-inverse", "dyckEquiv inverse", "dyckEquiv_inverse",
                "The inverse reads counts of preceding downsteps using the existing eastCounts and reconstructs the actual ordinary word by inverse ranks.", DescribeRole.Theorem),
            Node("card-catalan-avoiders", "card catalan avoiders", "card_catalan_avoiders",
                "For every n including zero, the actual ordinary words avoiding literal 10-1 and 20-1 have cardinality catalan n. This uses the constructed equivalence and the existing Mathlib Catalan cardinality.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(("ordinaryascentcatalanrank-" + id).ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
