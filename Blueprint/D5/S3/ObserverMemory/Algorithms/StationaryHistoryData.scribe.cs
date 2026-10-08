using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual history data from original controller histories.",
        H("StationaryHistoryData"),
        Blocks(
            Result("actual_history_data", "actual-history-data", "Derived actual history data",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.Call("HistoryData", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"))),
                "HistoryData derives positive bounded read counts, exact first events, "
                + "event levels, times and colors, nonempty supports, parent levels and "
                + "support inclusion, and disjoint indexed event fibers. Event and history-label "
                + "incidence are equivalent. The exact root and leaf cardinalities are three "
                + "and 3P. Every graph leaf has the fixed original output of each supporting "
                + "input. Root colors, shifts and levels are c, ell and zero, with the exact "
                + "first-digit supports. Same-control phase supports are disjoint, time is "
                + "shift plus level, and every successive read has a positive literal wait "
                + "equal to its shift increase. Singleton continuations have one child. "
                + "All these fields are obtained from C and I; interval propagation and "
                + "binary-node counts are not fields of HistoryData."))));

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryReadHistoryDocument.ResultAt("StationaryHistoryData", declaration, id, title, statement, explanation);
}
