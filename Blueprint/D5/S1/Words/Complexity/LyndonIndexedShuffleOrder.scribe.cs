using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class LyndonIndexedShuffleOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/LyndonIndexedShuffleOrder";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every occurrence-indexed interleaving of nonincreasing Lyndon factors is lexicographically bounded by their ordered concatenation.",
        H("Occurrence-Indexed Lyndon Shuffle Order"),
        Blocks(
            Paragraph(Text(
                "This module iterates the binary fixed-source promotion theorem over a list of "
                + "factors. Schedule labels are source positions, not factor values, so repeated "
                + "equal factors and repeated letters retain distinct identities.")),
            D("indexed-schedule", "IndexedSchedule", "Indexed source schedules",
                "IndexedSchedule abbreviates List Nat; each entry names a position in the factor list and therefore distinguishes duplicate factors.", DescribeRole.Definition),
            D("is-valid-schedule", "IsValidSchedule", "Exact occurrence consumption",
                "For factors : List (List A), a schedule is valid when, for every natural source index i, schedule.count i equals the length of factors.getD i []. This excludes out-of-range labels and consumes every source occurrence exactly once.", DescribeRole.Definition),
            D("annotate-indexed-from", "annotateIndexedFrom", "Annotate indexed occurrences",
                "Starting from a counter function used : Nat->Nat, annotateIndexedFrom replaces each source label i by (i,used i) and increments only the counter at i.", DescribeRole.Definition),
            D("annotate-indexed", "annotateIndexed", "Zero-based indexed annotation",
                "annotateIndexed starts every source counter at zero.", DescribeRole.Definition),
            D("read-indexed", "readIndexed", "Read a fixed indexed occurrence",
                "readIndexed factors (i,j) reads occurrence j from factors.getD i [] and returns Option A.", DescribeRole.Definition),
            D("evaluate-schedule", "evaluateSchedule", "Evaluate a valid indexed schedule",
                "evaluateSchedule returns none unless IsValidSchedule holds; otherwise it maps all annotated occurrences through readIndexed and sequences the result.", DescribeRole.Definition),
            D("mapm-length", "mapM_length", "Successful option traversal preserves length",
                "For any read : B->Option A, entries, and word, entries.mapM read=some word implies word.length=entries.length."),
            D("evaluate-schedule-le-flatten", "evaluateSchedule_le_flatten", "Ordered Lyndon concatenation is maximal",
                "For linearly ordered A, Lyndon factors in pairwise nonincreasing order, a valid indexed schedule, and successful evaluation word, one has word<=factors.flatten. The proof promotes the leading factor occurrence by occurrence and never collapses duplicate factor identities.", literature: false)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/LyndonShuffleScheduleOrder"))]));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
