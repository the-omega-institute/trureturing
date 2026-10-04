using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class SaturatedControlRegionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An attained maximal cumulative cost produces an actual silent successor region covering every current source.",
        H("Saturated Control Region"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("saturated-silent-source-region"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/SaturatedControlRegion."
                        + "saturated_silent_source_region"),
                H("A source-covering silent region without finite state assumptions"),
                StatementSource.FromAuthor(RegionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix the original data and control source, a complementary pair of "
                            + "positive-dimensional original submodules, and a compliant "
                            + "endpoint controller with arbitrary persistent local and root "
                            + "types. Assume one natural cumulative-cost bound for every "
                            + "locally initialized original input and every finite action word.")),
                    Paragraph(Text(
                        "There is an initialized reachable state whose entire finite-word "
                            + "successor region is closed under all original actions. Every "
                            + "edge in that same region has zero communication cost, and its "
                            + "current readouts cover the entire original source.")),
                    Paragraph(Text(
                        "Some original rewrite has positive initial cost. Its public roots "
                            + "are internal on the full local initialization product and leaves "
                            + "throughout that very silent region. Root agreement transfers "
                            + "these properties to either endpoint's local root selector.")),
                    Paragraph(Text(
                        "A bounded nonempty set of attained natural costs has a greatest "
                            + "attained value. A positive-cost successor appended to its "
                            + "attaining word contradicts maximality. Total original basis "
                            + "translations generate a finite word reaching every desired "
                            + "current source from the attained state. Both arguments use "
                            + "actual protocol-realized states rather than a finite-state "
                            + "cycle criterion or an assumed product of later endpoints.")),
                    Paragraph(Text(
                        "This supplier supports persistent-state separation and the "
                            + "arbitrary-carrier memory lower bounds. It does not supply the "
                            + "restricted attaining controller, the memory embeddings, the "
                            + "exact first-rewrite cost on all words, or the storage minima."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula body) => Seq(Open, body, Close);
    private static Formula C(string name, params Formula[] args)
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
    private static Formula A(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.Add(Land);
            items.Add(P(clause));
        }
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, P(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, type, Comma, P(body));
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(P(premise), Implies, Sp, P(body));
    private static Formula E(Formula left, Formula right) => Seq(left, Eq, right);
    private static Formula NE(Formula left, Formula right) => Seq(left, Neq, Sp, right);
    private static Formula LE(Formula left, Formula right) => Seq(left, Le, Sp, right);
    private static Formula LT(Formula left, Formula right) => Seq(left, Lt, right);
    private static Formula Ty(string level) => Seq(V("Type"), Underscore, Grp(V(level)));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Bit => C("ZMod", D(2));
    private static Formula List(Formula type) => C("List", type);

    private static Formula RegionFormula()
    {
        Formula d = V("d"), a = V("A"), b = V("B"), h = V("h"), c = V("C");
        Formula m = V("mstar"), i = V("i"), word = V("word"), f = V("f");
        Formula actions = C("Action", d), words = List(actions);
        Formula successor = C("runWord", C("step", c), word, m);
        Formula rewrite = C("rewrite", i);
        Formula initialNode = C("node", C("protocol", c, rewrite,
            C("rootA", c, rewrite, C("initA", c, V("a")))), C("nil"));
        Formula regionNode = C("node", C("protocol", c, rewrite,
            C("rootA", c, rewrite, C("fst", C("val", successor)))), C("nil"));
        Formula result = Ex("mstar", C("State", c), Ex("i", C("Fin", d), A(
            Ex("a", a, Ex("b", b, Ex("initialWord", words,
                E(C("runWord", C("step", c), V("initialWord"),
                    C("initial", c, V("a"), V("b"))), m)))),
            LT(D(0), C("splitCost", h, i)),
            All("word", words, All("f", actions, E(C("cost", c, successor, f), D(0)))),
            All("word", words, All("f", actions, Ex("nextWord", words,
                E(C("step", c, f, successor), C("runWord", C("step", c), V("nextWord"), m))))),
            All("z", C("Source", d), Ex("word", words, E(C("readout", c, successor), V("z")))),
            All("a", a, All("b", b, NE(initialNode, C("inr", C("unit"))))),
            All("word", words, E(regionNode, C("inr", C("unit")))))));
        return Disp(All("d", N, Imp(LE(D(2), d),
            All("A", C("Submodule", Bit, C("Source", d)),
            All("B", C("Submodule", Bit, C("Source", d)), All("h", C("IsCompl", a, b),
            Imp(A(LT(D(0), C("finrank", Bit, a)), LT(D(0), C("finrank", Bit, b))),
            All("MA", Ty("u"), All("MB", Ty("v"), All("Root", Ty("w"),
            All("C", C("Controller", h, V("MA"), V("MB"), V("Root")), All("K", N,
                Imp(C("UniformCumulativeBudget", c, V("K")), result)))))))))))));
    }

}
