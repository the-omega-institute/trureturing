using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class CausalRepairEnvelopesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Prediction/CausalRepairEnvelopes.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common causal envelopes give an optimal repair of a finite response table.",
        H("Exact Causal Repair Error"),
        Blocks(
            Entry("feedback-distance", "feedbackDistance", "Feedback event distance", DistanceFormula(),
                DescribeRole.Definition,
                "The maximum ranges over every deterministic causal strategy and every event of complete output words. The response after feedback need not be normalized, so the quantity compares event masses."),
            Entry("feedback-defect", "feedbackDefect", "Feedback normalization defect", DefectFormula(),
                DescribeRole.Definition,
                "The defect is the largest absolute difference between a fed-back total mass and one."),
            Entry("optimal-causal-repair", "result", "Attained optimal causal repair", ResultFormula(),
                DescribeRole.Theorem,
                "Every nonnegative finite response table normalized at each fixed action word admits a causal probability table with event distance exactly equal to its feedback normalization defect. Every other causal probability table has at least that distance.",
                "Backward recursion takes the maximum and minimum, over the next action, of the sums of branch continuation masses. Tail strategies chosen independently on different output branches join into one causal strategy.",
                "The forward upper construction pads the maximizing branch envelopes with nonnegative mass on a fixed output word. The lower construction scales the minimizing branch envelopes by the parent-to-child total-mass ratio; a zero denominator has zero parent mass.",
                "A convex combination of these common envelopes has total mass one under every strategy. The feedback normalization criterion then gives prefix causality. Event discrepancies are bounded by the upper mass minus one and by one minus the lower mass; the complete output event supplies the matching universal lower bound."))));

    private static DocumentBlock Entry(string id, string selector, string title, Formula formula,
        DescribeRole role, params string[] paragraphs) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Owner + selector), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula ty) => Seq(x, Colon, Sp, ty);
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, b);
    private static Formula All(string x, Formula ty, Formula body) =>
        Seq(Forall, Sp, Typed(V(x), ty), Comma, Sp, body);
    private static Formula Ex(string x, Formula ty, Formula body) =>
        Seq(Exists, Sp, Typed(V(x), ty), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Rightarrow, Sp, Par(b));
    private static Formula And(params Formula[] xs)
    {
        var items = new List<Formula>();
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(Par(xs[i]));
        }
        return Seq(items.ToArray());
    }
    private static Formula Rel(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula Fin => Call("Fin", V("T"));
    private static Formula Val(Formula t) => Seq(t, Dot, V("val"));
    private static Formula Word(string family) => Arrow(Typed(V("t"), Fin), At(V(family), V("t")));
    private static Formula Prefix(string family, Formula n) => Call("Prefix", V(family), n);
    private static Formula Table => Arrow(Word("Y"), Arrow(Word("A"), R));
    private static Formula Strategy => Arrow(Typed(V("t"), Fin),
        Arrow(Prefix("Y", Val(V("t"))), At(V("A"), V("t"))));
    private static Formula Mass(Formula p, Formula f) => Call("feedbackMass", p, f);
    private static Formula Value(Formula p, Formula y, Formula a) => At(At(p, y), a);
    private static Formula Sum(Formula x, Formula body) => Seq(F.Sum, Sp, Underscore, Grp(x), Sp, body);
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Rvert);
    private static Formula Instance(string cls, string family) => Seq(OpenBracket,
        All("t", Fin, Call(cls, At(V(family), V("t")))), CloseBracket);
    private static Formula Scope(Formula body, bool nonemptyY, bool equalityY)
    {
        var items = new List<Formula> {
            Instance("Fintype", "A"), Comma, Sp, Instance("Nonempty", "A"), Comma, Sp,
            Instance("Fintype", "Y"), Comma, Sp };
        if (nonemptyY) items.AddRange([Instance("Nonempty", "Y"), Comma, Sp]);
        if (equalityY) items.AddRange([Instance("DecidableEq", "Y"), Comma, Sp]);
        items.Add(body);
        return All("T", N, All("A", Arrow(Fin, Call("Type")),
            All("Y", Arrow(Fin, Call("Type")), Seq(items.ToArray()))));
    }
    private static Formula Nonnegative(Formula p) => All("y", Word("Y"), All("a", Word("A"),
        Rel(D(0), Leq, Value(p, V("y"), V("a")))));
    private static Formula Normalized(Formula p) => All("a", Word("A"),
        Rel(Sum(Typed(V("y"), Word("Y")), Value(p, V("y"), V("a"))), Eq, D(1)));
    private static Formula Causal(Formula p)
    {
        var agrees = All("i", Fin, Imp(Rel(Val(V("i")), Lt, V("n")),
            Rel(At(V("a"), V("i")), Eq, At(V("b"), V("i")))));
        var marginals = Rel(Call("prefixMarginal", p, V("n"), V("x"), V("a")), Eq,
            Call("prefixMarginal", p, V("n"), V("x"), V("b")));
        return All("n", N, Imp(Rel(V("n"), Leq, V("T")),
            All("x", Prefix("Y", V("n")), All("a", Word("A"), All("b", Word("A"),
                Imp(agrees, marginals))))));
    }
    private static Formula DistanceFormula()
    {
        var act = Call("feedbackActions", V("f"), V("y"));
        var diff = Rel(Value(V("P"), V("y"), act), Minus, Value(V("Q"), V("y"), act));
        var eventSum = Sum(Seq(Typed(V("y"), Word("Y")), Comma, Sp,
            V("y"), Sp, InMacro, Sp, V("E")), Par(diff));
        var maximum = Seq(Max, Sp, Underscore,
            Grp(Seq(Typed(V("f"), Strategy), Comma, Sp, Typed(V("E"), Call("Set", Word("Y"))))),
            Sp, Abs(eventSum));
        return Disp(Scope(All("P", Table, All("Q", Table,
            Rel(Call("feedbackDistance", V("P"), V("Q")), Eq, maximum))), false, false));
    }
    private static Formula DefectFormula()
    {
        var maximum = Seq(Max, Sp, Underscore, Grp(Typed(V("f"), Strategy)), Sp,
            Abs(Rel(Mass(V("P"), V("f")), Minus, D(1))));
        return Disp(Scope(All("P", Table,
            Rel(Call("feedbackDefect", V("P")), Eq, maximum)), false, false));
    }
    private static Formula ResultFormula()
    {
        var optimality = All("R", Table, Imp(Nonnegative(V("R")), Imp(Normalized(V("R")),
            Imp(Causal(V("R")), Rel(Call("feedbackDefect", V("P")), Leq,
                Call("feedbackDistance", V("P"), V("R")))))));
        var repaired = Ex("Q", Table, And(Nonnegative(V("Q")), Normalized(V("Q")), Causal(V("Q")),
            Rel(Call("feedbackDistance", V("P"), V("Q")), Eq, Call("feedbackDefect", V("P"))), optimality));
        return Disp(Scope(Imp(Rel(D(1), Leq, V("T")), All("P", Table,
            Imp(Nonnegative(V("P")), Imp(Normalized(V("P")), repaired)))), true, true));
    }
}
