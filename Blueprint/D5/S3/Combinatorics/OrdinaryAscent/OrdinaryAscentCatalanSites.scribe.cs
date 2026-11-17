using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrdinaryAscent;

internal sealed class OrdinaryAscentCatalanSitesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanSites.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/mazhang2026ordinary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.",
        H("Ordinary ascent CatalanSites"),
        Blocks(
            Node("CatalanWord", "CatalanWord", "CatalanWord",
                "The ordinary-word predicate together with literal avoidance of 10-1 and 20-1. It is distinct from the pair 02-1,12-0.", DescribeRole.Definition),
            Node("sites", "sites", "sites",
                "The values from zero through one plus the ascent count, with each half-open descent interval (next value,previous value] removed. For empty prefixes this auxiliary set does not encode the unique ordinary first letter.", DescribeRole.Definition),
            Node("mem-sites", "mem sites", "mem_sites",
                "Membership is exactly the ascent upper bound and, at every adjacent pair, either being at most the second value or strictly greater than the first.", DescribeRole.Theorem),
            Node("catalan-append-iff", "catalan append iff", "catalan_append_iff",
                "For a nonempty prefix, the extension is an actual Catalan-pair word precisely when the prefix is such a word and the appended value belongs to its computed sites.", DescribeRole.Theorem),
            Node("fresh-mem-sites", "fresh mem sites", "fresh_mem_sites",
                "For an ordinary word, one plus the ascent count is a legal site and strictly exceeds every already used entry.", DescribeRole.Theorem),
            Node("last-mem-sites", "last mem sites", "last_mem_sites",
                "For a nonempty actual Catalan-pair word, its last value remains an admissible site.", DescribeRole.Theorem),
            Node("mem-sites-append", "mem sites append", "mem_sites_append",
                "For a nonempty prefix, the next site exclusions consist of the old exclusions and exactly the new adjacent-pair exclusion, together with the updated ascent bound.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(("ordinaryascentcatalansites-" + id).ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
