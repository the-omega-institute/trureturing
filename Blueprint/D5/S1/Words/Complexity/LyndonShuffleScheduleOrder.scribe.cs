using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class LyndonShuffleScheduleOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonShuffleScheduleOrder";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occurrence-indexed binary schedules can be promoted to start at the larger fixed source without decreasing their evaluated word.",
        H("Fixed-Source Binary Shuffle Order"),
        Blocks(
            Paragraph(Text(
                "The source paper uses shuffle products and retains their alignment multiplicities. "
                + "This repository module supplies the fixed-source occurrence bookkeeping needed "
                + "later: equal letters and duplicate source factors are never identified.")),
            D("side", "Side", "Two source labels",
                "Side is the two-constructor type first|second, with decidable equality; it records which unchanged source supplies each scheduled position.", DescribeRole.Definition),
            D("annotate-two-from", "annotateTwoFrom", "Occurrence annotation with offsets",
                "Given initial occurrence counters for both sides and a Side list, annotateTwoFrom labels every schedule entry by its zero-based occurrence number within that side and increments only the selected counter.", DescribeRole.Definition),
            D("annotate-two", "annotateTwo", "Zero-based occurrence annotation",
                "annotateTwo starts annotateTwoFrom at counter zero for both sources.", DescribeRole.Definition),
            D("shift-pair-occurrences", "shiftPairOccurrences", "Shift occurrence coordinates",
                "shiftPairOccurrences firstOffset secondOffset adds the matching offset to an annotated first or second occurrence without changing its side.", DescribeRole.Definition),
            D("annotate-two-from-add", "annotateTwoFrom_add", "Offset naturality",
                "For all offsets, schedules, and starting counters, annotation from offset starts equals mapping shiftPairOccurrences over annotation from the unshifted starts.", literature: false),
            D("read-two", "readTwo", "Read an annotated binary occurrence",
                "readTwo first second reads index i from the source selected by Side and returns Option A, preserving the occurrence coordinate.", DescribeRole.Definition),
            D("evaluate-two", "evaluateTwo", "Evaluate a fixed-source schedule",
                "evaluateTwo maps occurrence annotation through readTwo and sequences the options; the source words are never permuted or replaced.", DescribeRole.Definition),
            D("valid-two-schedule", "ValidTwoSchedule", "Consume each source exactly once",
                "A binary schedule is valid for first and second exactly when its counts of Side.first and Side.second equal the respective source lengths.", DescribeRole.Definition),
            D("fixed-source-front-promotion", "fixedSource_frontPromotion", "Promote the larger source to the front",
                "For linearly ordered A, fixed words first>=second, a valid schedule starting with second, and a successful evaluation word, there exist a valid promoted schedule starting with first and an evaluated promotedWord with word<=promotedWord. Both source words and every occurrence are retained.", literature: false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/LyndonStandardBracket"))]));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
