using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indexed history separation, first-read fibers and positive literal continuation gaps.",
        H("StationaryHistoryContinuation"),
        Blocks(
            Result("root_support", "root-support", "Original first-read fibers",
                InitializedScope(All("c", Call("Fin", D(3)), All("x", Label,
                    Seq(Member(V("x"), Call("support", V("C"), V("hP"), V("I"),
                            Call("root", V("C"), V("hP"), V("I"), V("c")))), Iff,
                        EqF(Call("digit", V("hP"), Seq(V("x"), Plus, V("ell"))), V("c")))))),
                "The root support is exactly the original digit block after the common "
                + "literal translation ell. No source-dependent preparation is introduced."),
            Result("same_control_phase_disjoint", "same-control-phase-disjoint", "Phase separation at one control",
                InitializedScope(All("n", Hist, All("m", Hist,
                    Imp(And(Seq(V("n"), Neq, Sp, V("m")), EqF(At("readControl", "n"), At("readControl", "m"))),
                        Call("Disjoint", At("phaseSupport", "n"), At("phaseSupport", "m")))))),
                "A common physical phase and read control would give equal initialized "
                + "configurations. Finite correctness then forces the same original label "
                + "and time, and hence the same indexed read and full history. This also "
                + "applies to histories at different levels and to terminating control cycles."),
            Result("literal_shift_gap", "literal-shift-gap", "Literal read gaps are physical shift increases",
                InitializedScope(All("x", Label, All("i", N, Imp(
                    LT(Seq(V("i"), Plus, D(1)), Call("reads", V("C"), V("hP"), V("I"), V("x"))),
                    And(LT(D(0), LiteralGap), EqF(
                        Call("historyShift", V("C"), V("hP"), V("I"), Event("x", Seq(V("i"), Plus, D(1)))),
                        Seq(Call("historyShift", V("C"), V("hP"), V("I"), Event("x", V("i"))),
                            Plus, LiteralGap))))))),
                "The action immediately after a nonfinal read is a wait. Consecutive read times "
                + "therefore have a positive intervening literal gap. Time equals shift plus read "
                + "level, so the shift increases by that entire gap."),
            Result("singleton_continuation", "singleton-continuation", "Singleton continuation stays unary",
                InitializedScope(All("n", Hist,
                    Imp(And(EqF(Call("card", At("support", "n")), D(1)),
                            Seq(Neg, Sp, Call("IsLeaf", V("C"), V("hP"), V("I"), V("n")))),
                        EqF(Call("card", At("children", "n")), D(1))))),
                "Every child's support is nonempty and lies in its parent's support. "
                + "When that support is one label, child level and input-index uniqueness "
                + "force one child. The continuation is kept rather than erased."))));

    private static Formula LiteralGap => Seq(ReadTime("x", Seq(V("i"), Plus, D(1))), Minus,
        Grp(Seq(ReadTime("x", V("i")), Plus, D(1))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Label => Call("ZMod", Seq(D(3), Times, Sp, V("P")));
    private static Formula Hist => Call("History", V("C"), V("hP"), V("I"));
    private static Formula At(string name, string n) => Call(name, V("C"), V("hP"), V("I"), V(n));
    private static Formula Event(string x, Formula i) => Call("event", V("C"), V("hP"), V("I"), Pair(V(x), i));
    private static Formula EqF(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula LT(Formula x, Formula y) => Seq(x, Lt, y);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Member(Formula x, Formula s) => Seq(x, InMacro, Sp, s);
    private static Formula ReadTime(string x, Formula i) => Call("readTime", V("C"), V("hP"), V("I"), V(x), i);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula Imp(Formula premise, Formula body) => Seq(Grp(premise), Implies, Grp(body));
    private static Formula And(Formula a, Formula b) => Seq(Grp(a), Land, Grp(b));
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
    private static Formula Scope(Formula body) => All("P", N,
        All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        All("C", Call("Controller", V("P"), V("Q")), All("hP", LT(D(1), V("P")), body))));
    private static Formula InitializedScope(Formula body) => Scope(All("ell", N, All("h", N,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")),
            Seq(OpenBracket, Call("NeZero", Seq(D(3), Times, Sp, V("P"))), CloseBracket, body)))));
    private static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => ResultAt("StationaryHistoryContinuation", declaration, id, title, statement, explanation);
}
