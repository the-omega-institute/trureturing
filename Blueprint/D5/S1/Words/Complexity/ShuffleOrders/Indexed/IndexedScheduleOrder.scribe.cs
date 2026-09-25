using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ShuffleOrders.Indexed;

internal sealed class ShuffleOrdersIndexedIndexedScheduleOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indexed schedules preserve every occurrence of every fixed source.",
        H("IndexedScheduleOrder"),
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
                "evaluateSchedule returns none unless IsValidSchedule holds; otherwise it maps all annotated occurrences through readIndexed and sequences the result.", DescribeRole.Definition))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "IndexedSchedule" => Equal(F.Id("IndexedSchedule"),
            Call("List", F.Id("Nat"))),
        "IsValidSchedule" => Seq(Forall, Sp, F.Id("factors"), Comma,
            F.Id("schedule"), Comma, Sp,
            Call("IsValidSchedule", F.Id("factors"), F.Id("schedule")), Iff,
            Forall, Sp, F.Id("i"), Comma,
            Equal(Call("count", F.Id("schedule"), F.Id("i")),
                Call("length", Call("getD", F.Id("factors"), F.Id("i"),
                    F.Id("empty"))))),
        "annotateIndexedFrom" => Seq(Forall, Sp, F.Id("used"), Comma,
            F.Id("i"), Comma, F.Id("schedule"), Comma, Sp,
            Equal(Call("annotateIndexedFrom", F.Id("used"), F.Id("empty")),
                F.Id("empty")), Land,
            Equal(Call("annotateIndexedFrom", F.Id("used"),
                    Call("cons", F.Id("i"), F.Id("schedule"))),
                Call("cons", Call("pair", F.Id("i"),
                        Call("apply", F.Id("used"), F.Id("i"))),
                    Call("annotateIndexedFrom", Call("update", F.Id("used"),
                        F.Id("i"), Add(Call("apply", F.Id("used"), F.Id("i")),
                            Num(1))), F.Id("schedule"))))),
        "annotateIndexed" => Seq(Forall, Sp, F.Id("schedule"), Comma,
            Equal(Call("annotateIndexed", F.Id("schedule")),
                Call("annotateIndexedFrom", Call("lambda", F.Id("i"), Num(0)),
                    F.Id("schedule")))),
        "readIndexed" => Seq(Forall, Sp, F.Id("factors"), Comma,
            F.Id("i"), Comma, F.Id("j"), Comma,
            Equal(Call("readIndexed", F.Id("factors"),
                    Call("pair", F.Id("i"), F.Id("j"))),
                Call("getOptional", Call("getD", F.Id("factors"), F.Id("i"),
                    F.Id("empty")), F.Id("j")))),
        "evaluateSchedule" => Seq(Forall, Sp, F.Id("factors"), Comma,
            F.Id("schedule"), Comma, Sp,
            Equal(Call("evaluateSchedule", F.Id("factors"), F.Id("schedule")),
                Call("ifThenElse", Call("IsValidSchedule", F.Id("factors"),
                        F.Id("schedule")),
                    Call("mapM", Call("annotateIndexed", F.Id("schedule")),
                        Call("readIndexed", F.Id("factors"))), F.Id("none")))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
