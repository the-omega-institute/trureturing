using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indexed history separation and literal continuing-row execution derive binary forest counts.",
        H("StationaryHistoryContinuation"),
        Blocks(
            Result("root_support", "root-support", "Original first-read fibers",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("c", StationaryReadHistoryDocument.Call("Fin", D(3)), StationaryReadHistoryDocument.All("x", StationaryReadHistoryDocument.Label,
                    Seq(StationaryReadHistoryDocument.Member(StationaryReadHistoryDocument.V("x"), StationaryReadHistoryDocument.Call("support", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"),
                            StationaryReadHistoryDocument.Call("root", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("c")))), Iff,
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("digit", StationaryReadHistoryDocument.V("hP"), Seq(StationaryReadHistoryDocument.V("x"), Plus, StationaryReadHistoryDocument.V("ell"))), StationaryReadHistoryDocument.V("c")))))),
                "The root support is exactly the original digit block after the common "
                + "literal translation ell. No source-dependent preparation is introduced."),
            Result("same_control_phase_disjoint", "same-control-phase-disjoint", "Phase separation at one control",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("n", StationaryReadHistoryDocument.Hist, StationaryReadHistoryDocument.All("m", StationaryReadHistoryDocument.Hist,
                    StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.And(Seq(StationaryReadHistoryDocument.V("n"), Neq, Sp, StationaryReadHistoryDocument.V("m")), StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.At("readControl", "n"), StationaryReadHistoryDocument.At("readControl", "m"))),
                        StationaryReadHistoryDocument.Call("Disjoint", StationaryReadHistoryDocument.At("phaseSupport", "n"), StationaryReadHistoryDocument.At("phaseSupport", "m")))))),
                "A common physical phase and read control would give equal initialized "
                + "configurations. Finite correctness then forces the same original label "
                + "and time, and hence the same indexed read and full history. This also "
                + "applies to histories at different levels and to terminating control cycles."),
            Result("singleton_continuation", "singleton-continuation", "Singleton continuation stays unary",
                StationaryReadHistoryDocument.InitializedScope(StationaryReadHistoryDocument.All("n", StationaryReadHistoryDocument.Hist,
                    StationaryReadHistoryDocument.Imp(StationaryReadHistoryDocument.And(StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("card", StationaryReadHistoryDocument.At("support", "n")), D(1)),
                            Seq(Neg, Sp, StationaryReadHistoryDocument.Call("IsLeaf", StationaryReadHistoryDocument.V("C"), StationaryReadHistoryDocument.V("hP"), StationaryReadHistoryDocument.V("I"), StationaryReadHistoryDocument.V("n")))),
                        StationaryReadHistoryDocument.EqF(StationaryReadHistoryDocument.Call("card", StationaryReadHistoryDocument.At("children", "n")), D(1))))),
                "Every child's support is nonempty and lies in its parent's support. "
                + "When that support is one label, child level and input-index uniqueness "
                + "force one child. The continuation is kept rather than erased."))));

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryReadHistoryDocument.ResultAt("StationaryHistoryContinuation", declaration, id, title, statement, explanation);
}
