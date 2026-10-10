using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedForestPhysicalExecutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The total stationary unit table follows every original physical history exactly.",
        H("Physical execution of the stationary table"),
        Blocks(
            Paragraph(Text("For each original label, induction follows its finite sequence of history events. "
                + "The control graph may have cycles. Literal waits count actual unit actions, including complete wraps. "
                + "The table depends only on the charged nominal control state.")),
            Result("eventIncidenceEquiv", "event-incidence-equiv", "Lossless original event incidences",
                ForestScope(Call("equivalence",
                    Call("boundedLabelledEvents", V("F"), V("h")),
                    Call("supportedHistoryIncidences", V("F")))),
                "The first carrier consists of pairs (x,i) with x in ZMod(3P), i in Fin h and i<reads(x). "
                + "The second consists of pairs (x,n) with x in support(n). The forward map keeps x "
                + "and sends i to event(x,i); the inverse read index is level(n). Event support, "
                + "support completeness and event levels prove both maps lossless. This equivalence "
                + "is used to reach each history in the constructed initialized execution. "
                + "It concerns the existing PhysicalForest event carrier and does not assert an equivalence "
                + "with an independently formalized source domain.", DescribeRole.Definition),
            Result("physical_event_run", "physical-event-run", "Exact original indexed reads",
                Assigned(All("x", Call("Label", V("P")), All("i", N,
                    Imp(Seq(V("i"), Lt, Call("reads", V("F"), V("x"))),
                        EqF(Call("runAtOriginalEvent", V("F"), V("R"), V("alpha"), V("x"), V("i")),
                            Call("originalPhaseAndPlacedRead", V("F"), V("R"), V("alpha"), V("x"), V("i"))))))),
                "Induction is on the finite path of each original x. The actual next digit chooses its original "
                + "placed child at exactly shift+level. Equal physical phase residues do not shorten literal waits."),
            Result("physical_wait_run", "physical-wait-run", "Every literal unit position",
                Assigned(Call("exactLiteralWaitRun", V("F"), V("R"), V("alpha"))),
                "For every nonfinal event and every k below its positive literal delay, execution at eventTime+1+k "
                + "has phase x+shift+k and the tagged tail with delay-1-k remaining index. "
                + "The next read has the preserved absolute child digit and deadline."),
            Result("physical_terminal_run", "physical-terminal-run", "Immediate original fixed output",
                Assigned(All("x", Call("Label", V("P")), EqF(
                    Call("runAtStopTime", V("F"), V("R"), V("alpha"), V("x")),
                    Call("lastPhaseAndOriginalTerminal", V("F"), V("R"), V("alpha"), V("x"))))),
                "The final original read immediately selects H_x; the stop time adds one read action and no halt action."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, type, Comma, Grp(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula AllN(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (b, n) => All(n, N, b));
    private static Formula ForestScope(Formula body) => AllN(["P", "h", "ell"],
        All("Node", V("Type"), All("finiteNode", Call("Fintype", V("Node")),
        All("eqNode", Call("DecidableEq", V("Node")), All("hP", Seq(D(1), Lt, V("P")),
        All("F", Call("PhysicalForest", V("P"), V("h"), V("ell"), V("Node"), V("hP")), body))))));
    private static Formula Scope(Formula body) => ForestScope(All("e", N,
        All("R", Call("Prescribed", V("F")), body)));
    private static Formula Assigned(Formula body) => Scope(
        All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
            Imp(Call("Compatible", V("F"), V("R"), V("e")), body)));
    private static DocumentBlock Result(string declaration, string id, string heading,
        Formula statement, string explanation, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution." + declaration),
            H(heading), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);
}
