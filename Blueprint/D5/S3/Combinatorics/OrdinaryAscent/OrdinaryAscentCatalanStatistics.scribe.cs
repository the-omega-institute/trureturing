using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrdinaryAscent;

internal sealed class OrdinaryAscentCatalanStatisticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/mazhang2026ordinary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.",
        H("Ordinary ascent CatalanStatistics"),
        Blocks(
            Node("rank-fresh", "rank fresh", "rank_fresh",
                "The fresh upper bound occupies the largest actual rank: its rank plus one is the site count.", DescribeRole.Theorem),
            Node("asc-eastCode", "asc eastCode", "asc_eastCode",
                "For every actual avoiding word, the sum of the strict ascent counts of the word and its east-count code is length minus one.", DescribeRole.Theorem),
            Node("peaks-dyckSteps", "peaks dyckSteps", "peaks_dyckSteps",
                "For the existing east-count step encoding, if every code entry is strictly below the final size, the number of adjacent UD peaks is zero for an empty code and one plus its strict ascent count otherwise.", DescribeRole.Theorem),
            Node("dyckEquiv-peaks", "dyckEquiv peaks", "dyckEquiv_peaks",
                "The actual Dyck image has exactly n minus the ordinary word's ascent count many adjacent UD peaks.", DescribeRole.Theorem),
            Node("ascentPeakEquiv", "ascentPeakEquiv", "ascentPeakEquiv",
                "For r<n, restrict the actual equivalence to words with r ascents and Dyck words with n-r peaks. The inverse recovers the exact ascent statistic.", DescribeRole.Definition),
            Node("narayana-ascents", "narayana ascents", "narayana_ascents",
                "For r<n, n times the actual number of length-n ordinary words avoiding 10-1,20-1 with r ascents equals choose(n,r) choose(n,r+1). The positive-size and positive-peak hypotheses of the licensed supplier are discharged explicitly.", DescribeRole.Theorem),
            Node("dyckEquiv-insert", "Insertion and rightmost-up deletion", "dyckEquiv_insert",
                "For a nonempty actual parent and an actual one-letter child, let i be the appended letter's zero-based admissible rank. The parent path is Q followed by i downsteps, and the child path is Q followed by one upstep and i+1 downsteps. Thus deleting the rightmost upstep and its following downstep recovers the parent.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(("ordinaryascentcatalanstatistics-" + id).ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
