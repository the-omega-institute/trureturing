using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class HeadWeightedMetricDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/HeadWeightedMetric.";
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
    private static DocumentBlock.Describe Theorem(string key, string decl, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(key), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Head-dependent ultrametrics with uniform cylinder control shadow infinite pseudo-orbits; a single defect obstructs quantitative tracing.",
        H("Head-Weighted Product Metrics"), Blocks(
        Paragraph(Text("A HeadWeights object w consists of w(s,n)>0, nonincreasing in n, with w(s,0)=1 for every natural symbol s. "
            + "For unequal x,y set d(x,y)=w(x(0),firstDiff(x,y)); on equality set d=0. Differing heads have first difference zero and distance one, "
            + "so symmetry holds even though the definition uses the first argument's head. Mathlib PiNat supplies firstDiff, its minimum inequality and the standard product metric.")),
        Theorem("weighted-ultrametric", "distance_ultra", "The strong triangle inequality", St(
            All("w", Id("HeadWeights")), All("x", X), All("y", X), All("z", X),
            Seq(Call("distance", Id("w"), Id("x"), Id("z")), Sp, Le, Sp,
                Call("max", Call("distance", Id("w"), Id("x"), Id("y")), Call("distance", Id("w"), Id("y"), Id("z"))))),
            "Equal points are handled separately. With a common head, the first difference of x,z is at least the minimum of those on x,y and y,z; antitonicity gives the maximum bound. "
            + "With mixed heads one comparison edge is one, while every distance is at most one. Positive weights separate distinct points and give the actual rawMetric MetricSpace."),
        Theorem("uniform-product", "uniformSpace_eq_product", "Uniform equivalence over every symbol", St(
            All("w", Id("HeadWeights")), All("b", Call("UniformBounds", Id("w"))),
            Seq(Call("uniformSpace", Call("rawMetric", Id("w"))), Sp, Eq, Sp, Call("uniformSpace", Id("metricSpaceNatNat")))),
            "UniformBounds has a positive lower(n) valid for every head and an upper(n) valid for every head, with arbitrarily small upper tails. "
            + "Distance<lower(N) forces agreement through coordinate N. A prefix of length N gives distance<=upper(N). These two controls prove both uniform identity maps "
            + "against PiNat.metricSpaceNatNat on all of N^N. Replacing the raw uniformity by this proved equality gives a metric with the actual discrete product uniformity and topology."),
        Theorem("weighted-infinite-shadowing", "metric_hasShadowing", "Ordinary shadowing for uniform head weights", St(
            All("w", Id("HeadWeights")), All("b", Call("UniformBounds", Id("w"))),
            Call("MetricHasShadowing", Call("metric", Id("b")), Call("shift", D(1)))),
            "For epsilon>0 choose upper(N)<epsilon and delta=lower(N)>0. Each strict error forces overlap through N. "
            + "The diagonal splice agrees through N+1 at every natural time, and the uniform tail bound gives strict epsilon tracing. "
            + "There is no finite horizon or restriction of the carrier to a compact subset."),
        Theorem("single-defect-error", "defect_initial_error", "The exact size of the only nonzero error", St(
            All("w", Id("HeadWeights")), All("p", Nat), All("q", Nat), All("N", Nat),
            Hyp(Seq(Id("p"), Sp, Neq, Sp, Id("q"))),
            Seq(Call("distance", Id("w"), Call("shift", D(1), Call("defectOrbit", Id("p"), Id("q"), Id("N"), D(0))),
                Call("defectOrbit", Id("p"), Id("q"), Id("N"), D(1))), Sp, Eq, Sp,
                Call("weight", Id("w"), Id("q"), Seq(Id("N"), Minus, D(1))))),
            "The time-zero sequence has p at coordinate zero and q elsewhere. The time-one sequence has p only at N-1. "
            + "Every later sequence is the exact shift of its predecessor. The initial error has background head q and first difference N-1, "
            + "hence exactly w(q,N-1); all later errors are zero."),
        Theorem("single-defect-obstruction", "defect_no_tracer", "No full tracer below the preferred-head weight", St(
            All("w", Id("HeadWeights")), All("p", Nat), All("q", Nat), All("N", Nat),
            Hyp(Seq(Id("p"), Sp, Neq, Sp, Id("q"))), Hyp(Seq(D(2), Sp, Le, Sp, Id("N"))), All("r", Real),
            Hyp(Seq(Id("r"), Sp, Le, Sp, Call("weight", Id("w"), Id("p"), Id("N")))), All("y", X),
            Seq(Neg, Sp, Call("MetricTraces", Call("rawMetric", Id("w")), Call("shift", D(1)), Id("r"),
                Call("defectOrbit", Id("p"), Id("q"), Id("N")), Id("y")))),
            "Time zero first forces the tracer head to p, since a head mismatch has distance one. Antitonicity and the strict tracing bound then force y(N)=q. "
            + "At time N the observed head is p and the tracer head is q, giving distance exactly one. Since r<=w(p,N)<=1, the strict tracing inequality is impossible."),
        Theorem("standard-half-error", "standard_product_diagonal_traces", "The standard diagonal has a half-error bound", St(
            All("d", Real), Hyp(Seq(D(0), Sp, Lt, Sp, Id("d"))),
            All("z", Seq(Nat, Sp, To, Sp, X)),
            Hyp(Call("MetricPseudoOrbit", Id("metricSpaceNatNat"), Call("shift", D(1)), Id("d"), Id("z"))),
            Call("MetricTraces", Id("metricSpaceNatNat"), Call("shift", D(1)), Seq(Frac, Grp(Id("d")), Grp(D(2))), Id("z"), Call("diagonalSplice", Id("z")))),
            "A first tracing mismatch j telescopes to an edge mismatch k<j. That edge's first difference m is at most k, so 2*(1/2)^j<=(1/2)^m<delta. "
            + "Zero tracing errors are also strictly below delta/2. The same diagonal therefore supplies Lipschitz shadowing with L=1 for the entire standard product shift."))));
}
