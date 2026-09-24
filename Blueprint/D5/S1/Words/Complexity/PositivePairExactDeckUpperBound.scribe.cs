using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class PositivePairExactDeckUpperBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairExactDeckUpperBound";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Overlap infiltration with alignment multiplicity and indexed shuffle order make actual Lyndon coordinates an unconditional complete coordinate system for bounded scattered counts.",
        H("Unconditional Recovery from Actual Lyndon Coordinates"),
        Blocks(
            Paragraph(Text(
                "The infiltration product and its top-degree shuffle stratum are classical and "
                + "are also used in the cited source. The list-valued definitions retain one "
                + "entry per alignment, so coincident output words remain repeated. The final "
                + "unconditional recovery theorem is the repository bridge used by the exact "
                + "asymptotic upper injection.")),
            D("overlap-infiltrations", "overlapInfiltrations", "Overlap infiltrations with multiplicity",
                "For words left,right over a decidable alphabet, overlapInfiltrations recursively records a left-only, right-only, and, when the leading letters agree, shared-position branch. It is a list, so distinct alignments yielding the same merged word remain distinct entries.", DescribeRole.Definition, true),
            D("ordinary-shuffles", "ordinaryShuffles", "Ordinary shuffles with multiplicity",
                "ordinaryShuffles recursively interleaves the two words using the left-only and right-only branches, retaining one list entry per positional choice.", DescribeRole.Definition, true),
            D("scattered-count-product", "scatteredCount_mul_eq_sum_overlapInfiltrations", "The actual infiltration product identity",
                "For all left,right,source over a decidable alphabet, scatteredCount left source times scatteredCount right source equals the sum of scatteredCount merged source over the full overlapInfiltrations list, including repeated merged words.", literature: true),
            D("top-overlap-is-shuffle", "overlapInfiltrations_filter_top_length", "The top-length stratum is shuffle",
                "Filtering overlapInfiltrations left right to merged words of length left.length+right.length gives literal list equality with ordinaryShuffles left right, preserving every multiplicity.", literature: true),
            D("lyndon-coordinate-recovery", "scatteredCount_eq_of_lyndon_coordinates", "Actual Lyndon coordinates recover every bounded count",
                "For finite linearly ordered A and arbitrary k,left,right, if every actual Lyndon word of length at most k has equal scattered count in left and right, then every word of length at most k has equal scattered count. No common-length premise, exact-deck premise, or guarded recovery hypothesis is required.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/PositivePairExactDeckGrowth")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/LyndonIndexedShuffleOrder")),
        ]));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
