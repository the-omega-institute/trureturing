using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ProductMetricCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula X => Seq(Nat, Sp, To, Sp, Nat);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula Hyp(Formula a) => Seq(a, Sp, Rightarrow);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Conj(Formula f) => Seq(Open, f, Close, Sp, Land);
    private static Formula DistanceFormula => Seq(
        All("x", X), All("y", X), Call("dist", Id("x"), Id("y")), Sp, Eq, Sp,
        Call("if", Seq(Id("x"), Sp, Eq, Sp, Id("y")), D(0),
            Call("if", Seq(Call("apply", Id("x"), D(0)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
                Call("apply", Id("y"), D(0)), Sp, Eq, Sp, D(1)),
                Call("a", Call("firstDiff", Id("x"), Id("y"))),
                Call("b", Call("firstDiff", Id("x"), Id("y"))))));
    private static DocumentBlock.Describe Theorem(string key, string decl, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(key), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/goncalvessilva2026shadowing")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform equivalence preserves ordinary shadowing of the natural full product shift while a concrete head-dependent metric loses every Lipschitz tracing constant.",
        H("A Negative Product-Metric Stability Answer"), Blocks(
        Paragraph(Text("Let X be the entire product N^N and sigma(x)(j)=x(j+1). For unequal sequences let n=firstDiff(x,y), "
            + "a(n)=(1/2)^n and b(n)=(1/2)^(n*n). Give equal sequences distance zero. Give unequal sequences distance a(n) if both heads are one, "
            + "and b(n) otherwise. When heads differ, n=0 and both weights are one. This metric depends on the common head and lies outside the "
            + "globally symbol-independent prefix class of Definition 3.3 in Goncalves and Silva, arXiv:2603.03200v1. "
            + "The unrestricted Section 3 question on printed/PDF p.6 permits it. The statements below are deductions answering that question, not conclusions attributed to the paper.")),
        Theorem("literal-distance", "distance_formula", "The exact displayed distance", St(DistanceFormula),
            "The HeadWeights constructor agrees with both branches, including pairs whose heads differ and the zero diagonal. "
            + "Its positive antitone weights make an actual MetricSpace, with the strong triangle inequality."),
        Theorem("full-product-uniformity", "product_uniformity", "The exact discrete product uniformity", St(
            Seq(Call("uniformSpace", Id("metric")), Sp, Eq, Sp, Call("PiUniformSpace", Nat))),
            "For every unequal pair b(n)<=d(x,y)<=a(n); equal pairs have zero distance. Strict distance<b(N) forces agreement through N. "
            + "The raw weighted metric and PiNat.metricSpaceNatNat have both uniformly continuous identity maps on all symbols and all sequences. "
            + "The aligned metric has precisely the standard product uniform structure and topology, not just a continuous identity on a binary subset."),
        Theorem("ordinary-shadowing", "hasShadowing", "Full infinite ordinary shadowing", St(Call("MetricHasShadowing", Id("sigma"))),
            "Choose a(N)<epsilon and delta=b(N)>0. Errors below delta force overlap through coordinate N. The infinite diagonal splice "
            + "y(k)=z(k)(0) agrees with z(i) through N+1 at every time i, and its weighted tail distance is below epsilon. "
            + "The metric entourage bridge also identifies this with the existing UniformHasShadowing contract; compact finite-cover shadowing is not used."),
        Theorem("arbitrary-constants-obstruction", "bad_pseudoOrbit", "Every proposed pair of constants fails", St(
            All("L", Real), All("c", Real), Hyp(Seq(D(0), Sp, Lt, Sp, Id("L"))), Hyp(Seq(D(0), Sp, Lt, Sp, Id("c"))),
            Seq(Exists, Sp, Id("d"), Comma, Sp, D(0), Sp, Lt, Sp, Id("d"), Sp, Land, Sp, Id("d"), Sp, Le, Sp, Id("c"), Sp, Land, Sp,
                Exists, Sp, Id("z"), Colon, Sp, Nat, Sp, To, Sp, X, Comma,
                Call("MetricPseudoOrbit", Id("sigma"), Id("d"), Id("z")), Sp, Land, Sp,
                All("y", X), Neg, Sp, Call("MetricTraces", Id("sigma"), Seq(Id("L"), Id("d")), Id("z"), Id("y")))),
            "Choose N>=4 with a(N)<min(c/2,1/(2L)). The inequality (N-1)^2>=2N gives b(N-1)<=a(N)^2, "
            + "so delta=2b(N-1)>0 satisfies delta<=c and L delta<a(N). Use head one at time zero and a sole one at coordinate N-1 at time one, "
            + "then follow the exact infinite orbit. The only nonzero error is b(N-1)<delta. Time zero forces y(N)=0; "
            + "time N has observed head one and tracer head zero, hence distance one. This contradicts every full strict L delta tracer."),
        Theorem("literal-question-refuted", "result", "Uniform metric stability is false", St(Seq(Neg, Sp, Seq(Operatorname, Grp(Id("productmetricstability"))))),
            "product_metric_stability quantifies over every actual MetricSpace m on N^N: if both identities between m and the standard product metric "
            + "are uniformly continuous, ordinary strict metric shadowing would imply Lipschitz shadowing. The concrete metric supplies both identities and ordinary shadowing, "
            + "but bad_pseudoOrbit disproves Lipschitz shadowing with the full positive-L, positive-cutoff, infinite-sequence and all-time quantifiers."),
        Theorem("metric-change", "metric_change_counterexample", "What changes with the metric", St(
            Conj(DistanceFormula),
            Conj(Seq(All("x", X), All("y", X), Hyp(Seq(Id("x"), Sp, Neq, Sp, Id("y"))),
                Call("b", Call("firstDiff", Id("x"), Id("y"))), Sp, Le, Sp,
                Call("dist", Id("x"), Id("y")), Sp, Land, Sp,
                Call("dist", Id("x"), Id("y")), Sp, Le, Sp,
                Call("a", Call("firstDiff", Id("x"), Id("y"))))),
            Conj(Seq(All("x", X), All("y", X), All("z", X),
                Call("dist", Id("x"), Id("z")), Sp, Le, Sp,
                Call("max", Call("dist", Id("x"), Id("y")), Call("dist", Id("y"), Id("z"))))),
            Conj(Seq(Call("UniformContinuous", Id("metric"), Id("metricSpaceNatNat"), Id("id")),
                Sp, Land, Sp, Call("UniformContinuous", Id("metricSpaceNatNat"), Id("metric"), Id("id")))),
            Conj(Seq(Call("uniformSpace", Id("metric")), Sp, Eq, Sp, Call("PiUniformSpace", Nat))),
            Conj(Seq(Call("topology", Id("metric")), Sp, Eq, Sp, Call("PiTopology", Nat))),
            Seq(Call("Continuous", Id("sigma")), Sp, Land, Sp, Call("UniformHasShadowing", Id("sigma")), Sp, Land),
            Seq(Call("MetricHasShadowing", Id("metricSpaceNatNat"), Id("sigma")), Sp, Land, Sp,
                Call("HasLipschitzShadowing", Id("metricSpaceNatNat"), Id("sigma")), Sp, Land, Sp,
                Call("MetricHasShadowing", Id("metric"), Id("sigma")), Sp, Land, Sp,
                Neg, Sp, Call("HasLipschitzShadowing", Id("metric"), Id("sigma")))),
            "The certificate includes the exact displayed distance, sandwich bounds, strong triangle inequality, both uniform identity maps, "
            + "the exact discrete product uniformity and topology, shift continuity and uniform shadowing. "
            + "The standard product metric has Lipschitz shadowing with L=1, using the diagonal mismatch telescope and the half-error bound. "
            + "Both metrics have ordinary shadowing; the new metric loses Lipschitz shadowing despite the identical uniform structure. "
            + "N^N is not locally compact, whereas Definition 2.1 uses local compactness in preliminary Deaconu--Renault terminology. "
            + "This conclusion concerns the literal unrestricted Section 3 question. It does not assert the separately scoped locally compact variant, "
            + "a general ratio classification, official acceptance, or global uniqueness from the bounded literature search."))));
}
