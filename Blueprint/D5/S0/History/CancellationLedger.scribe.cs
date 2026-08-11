using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class CancellationLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/History/CancellationLedger",
            "Recording a referenced cancellation preserves the prior ledger and appends one new entry."),
        H("Append-Only Cancellation Ledgers"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("recording-a-cancellation-is-append-only"),
                H("Recording a cancellation is append-only"),
                LeanTheorem(
                    "D5/S0/History/CancellationLedger.record_cancellation_is_append_only"),
                AppendOnlyFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "A cancellation entry contains a typed index into the existing event "
                        + "history together with the compensating event to record. The index "
                        + "cannot name an absent earlier event. Recording the cancellation "
                        + "retains the complete prior ledger as a prefix, keeps the referenced "
                        + "event present, and increases the ledger length by exactly one. Thus "
                        + "a cancellation changes the running balance through a new audit entry "
                        + "without deleting or rewriting the event it addresses.")),
                    Paragraph(Text(
                        "Pinned mathlib was searched before proving. Its declarations "
                        + "FreeMonoid.mem_mul, FreeMonoid.length_mul, FreeMonoid.length_of, "
                        + "and List.get_mem supply the complete ledger-theoretic core. No "
                        + "upstream declaration packages a referenced cancellation with all "
                        + "three ledger invariants, so the Lean theorem is a declared thin "
                        + "honest wrapper that combines those laws over the repository's event "
                        + "history carrier. The source atom contains no numerical certificate.")))
            )),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/History/HistoryCarrier")),
        ]));

    private static Formula AppendOnlyFormula() => Disp(Seq(
        Forall, Sp, F.Id("h"), Comma, F.Id("c"), Comma, Esc,
        Operatorname, Grp(F.Id("prefix")), Open,
        F.Id("h"), Comma, F.Id("record"), Open, F.Id("h"), Comma, F.Id("c"), Close, Close,
        Sp, Land, Sp,
        Operatorname, Grp(F.Id("target")), Open, F.Id("c"), Close,
        Sp, InMacro, Sp, F.Id("record"), Open, F.Id("h"), Comma, F.Id("c"), Close,
        Sp, Land, Sp,
        Vert, Sp, F.Id("record"), Open, F.Id("h"), Comma, F.Id("c"), Close, Sp, Vert,
        Sp, Eq, Sp, Vert, Sp, F.Id("h"), Sp, Vert, Plus, D(1), Dot));
}
