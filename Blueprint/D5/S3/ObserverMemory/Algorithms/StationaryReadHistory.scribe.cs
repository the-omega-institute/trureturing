using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryReadHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual interval geometry constructs the physical forest and separates binary source rows.",
        H("StationaryReadHistory"),
        Blocks(
            Result("history_phase_convex", "history-phase-convex", "Convex physical fibers",
                InitializedScope(AllH(["n"], All("x", Label, All("y", Label, All("z", Label,
                    Imp(And(And(Member(V("x"), At("support", "n")), Member(V("z"), At("support", "n"))),
                        And(EqF(Call("digit", V("hP"), Phase("y", "n")), At("color", "n")),
                            And(LE(Val(Phase("x", "n")), Val(Phase("y", "n"))),
                                LE(Val(Phase("y", "n")), Val(Phase("z", "n")))))),
                        Member(V("y"), At("support", "n")))))))),
                "Within the current absolute digit block, every phase between two "
                + "supporting phases supports the same complete history. Induction follows "
                + "the actual parent; inverse translation preserves order between endpoints "
                + "in one previous digit block because neither block can span a modular wrap."),
            Result("history_interval_exists", "history-interval-exists", "Nonempty actual physical intervals",
                InitializedScope(AllH(["n"], Seq(Exists, Sp, V("ab"), Colon,
                    Seq(N, Times, N), Comma, And(LT(Call("fst", V("ab")), Call("snd", V("ab"))),
                        And(LE(Call("snd", V("ab")), V("P")), All("x", Label,
                            Seq(Member(V("x"), At("support", "n")), Iff,
                                IntervalMember("n", "x", Call("fst", V("ab")), Call("snd", V("ab")))))))))),
                "The minimum and maximum actual phase values yield lower and upper "
                + "endpoints with lower<upper<=P. Convexity proves the exact half-open interval; "
                + "intervalEndpoints chooses that witness, and lower/upper are its projections."),
            Result("physicalForest", "physical-forest", "PhysicalForest derived from the original controller",
                InitializedScope(Call("PhysicalForest", V("P"), V("h"), V("ell"), Hist, V("hP"))),
                "physicalForest constructs every field from the actual full words and "
                + "indexed reads: parent, roots, color, literal shift/delay, level, original "
                + "leaf labels, supports, interval endpoints, read counts and events; exact "
                + "root/first/event/support laws; interval bounds; child shift/level/answer "
                + "injectivity; indexed successor and immediate last-read stopping; original "
                + "leaf outputs; positive internal delays; branching<=2 and binary_count=3(P-1). "
                + "Its roots and leaves remain exactly three and 3P. forestEvent totalizes "
                + "the natural index only outside the actual read range. No forest, count "
                + "or injection is supplied as a hypothesis, and no J,s,Xi restriction is used."),
            Result("binary_crosses_cut", "binary-crosses-cut", "Binary intervals cross one modular cut",
                InitializedScope(AllH(["p"], Imp(EqF(Card("children", "p"), D(2)),
                    And(LT(At("lower", "p"), At("modularCut", "p")),
                        LT(At("modularCut", "p"), At("upper", "p")))))),
                "modularCut(p)=P-(delay(p) mod P). Distinct child digits require supporting "
                + "parent phases on both sides of this cut. Each binary interval contains "
                + "the cut phase, while a unary interval can remain on either side."),
            Result("binary_row_unique", "binary-row-unique", "One binary history per actual row",
                InitializedScope(AllH(["n", "m"], Imp(
                    And(And(EqF(Card("children", "n"), D(2)), EqF(Card("children", "m"), D(2))),
                        RowEq("n", "m")), EqF(V("n"), V("m"))))),
                "Shared continuing rows have equal literal delays and one modular cut. "
                + "Two binary intervals on that row would contain the same cut phase. "
                + "Same-control phase separation rules this out. These results supply "
                + "the actual forest and row geometry; core selection, weighted overlap "
                + "and the final original83.21 inequality require additional results."))));

    internal static Formula V(string name) => F.Id(name);
    internal static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    internal static Formula Label => Call("ZMod", Seq(D(3), Times, Sp, V("P")));
    internal static Formula Hist => Call("History", V("C"), V("hP"), V("I"));
    internal static Formula Trace(string x, Formula t) => Call("trace", V("C"), V("hP"), V(x), t);
    internal static Formula At(string name, string n) => Call(name, V("C"), V("hP"), V("I"), V(n));
    internal static Formula Event(string x, Formula i) => Call("event", V("C"), V("hP"), V("I"), Pair(V(x), i));
    internal static Formula EqF(Formula x, Formula y) => Seq(x, Eq, y);
    internal static Formula LT(Formula x, Formula y) => Seq(x, Lt, y);
    internal static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    internal static Formula Member(Formula x, Formula s) => Seq(x, InMacro, Sp, s);
    internal static Formula LE(Formula x, Formula y) => Seq(x, Le, Sp, y);
    internal static Formula Val(Formula x) => Call("val", x);
    internal static Formula Card(string name, string n) => Call("card", At(name, n));
    internal static Formula Phase(string x, string n) => Seq(V(x), Plus, At("historyShift", n));
    internal static Formula Gap(string n, string p) =>
        Seq(At("time", n), Minus, Grp(Seq(At("time", p), Plus, D(1))));
    internal static Formula ParentEdge(string n, string p) => EqF(At("parent", n), Call("some", V(p)));
    internal static Formula RowEq(string n, string m) =>
        And(EqF(At("readControl", n), At("readControl", m)), EqF(At("color", n), At("color", m)));
    internal static Formula ReadTime(string x, Formula i) => Call("readTime", V("C"), V("hP"), V("I"), V(x), i);
    internal static Formula AllH(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (current, name) => All(name, Hist, current));
    internal static Formula IntervalMember(string n, string x, Formula lower, Formula upper) =>
        And(LE(Seq(Val(At("color", n)), Times, Sp, V("P"), Plus, lower), Val(Phase(x, n))),
            LT(Val(Phase(x, n)), Seq(Val(At("color", n)), Times, Sp, V("P"), Plus, upper)));
    internal static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    internal static Formula Imp(Formula premise, Formula body) => Seq(Grp(premise), Implies, Grp(body));
    internal static Formula And(Formula a, Formula b) => Seq(Grp(a), Land, Grp(b));
    internal static Formula Call(string name, params Formula[] args)
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
    internal static Formula Scope(Formula body) => All("P", N,
        All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        All("C", Call("Controller", V("P"), V("Q")), All("hP", LT(D(1), V("P")), body))));
    internal static Formula InitializedScope(Formula body) => Scope(All("ell", N, All("h", N,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")), body))));
    internal static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => StationaryReadHistoryDocument.ResultAt("StationaryReadHistory", declaration, id, title, statement, explanation);
}
