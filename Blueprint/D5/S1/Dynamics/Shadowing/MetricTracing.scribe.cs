using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class MetricTracingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/MetricTracing.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Map(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
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
        "Strict infinite metric tracing agrees with uniform tracing without compactness; symbolic overlaps propagate along a diagonal.",
        H("Metric Tracing and Infinite Diagonal Splices"), Blocks(
        Paragraph(Text("A metric pseudo-orbit z satisfies dist(f(z(i)),z(i+1))<delta at every natural i. "
            + "MetricTraces(f,epsilon,z,y) means dist(f^i(y),z(i))<epsilon for all i, including zero. "
            + "MetricHasShadowing chooses a positive delta for each positive epsilon before the sequence. "
            + "HasLipschitzShadowing chooses positive L and cutoff before every positive delta at most the cutoff, and traces with strict bound L delta.")),
        Theorem("metric-uniform", "metric_shadowing_iff_uniform", "The noncompact metric entourage bridge", St(
            All("X", Id("Type")), Seq(Grp(), OpenBracket, Call("PseudoMetricSpace", Id("X")), CloseBracket, Comma),
            All("f", Map(Id("X"), Id("X"))),
            Seq(Call("MetricHasShadowing", Id("f")), Sp, Iff, Sp, Call("UniformHasShadowing", Id("f")))),
            "Every entourage contains a strict distance ball around the diagonal. Apply metric shadowing to its radius and use a strict control ball as the uniform entourage. "
            + "Conversely, apply uniform shadowing to the prescribed strict metric entourage and choose a control radius inside the returned entourage. "
            + "This uses Metric.mem_uniformity_dist and Metric.dist_mem_uniformity, without finite covers, local compactness, compactness or surjectivity."),
        Theorem("lipschitz-ordinary", "metricHasShadowing", "Quantitative tracing implies ordinary tracing", St(
            All("X", Id("Type")), Seq(Grp(), OpenBracket, Call("PseudoMetricSpace", Id("X")), CloseBracket, Comma),
            All("f", Map(Id("X"), Id("X"))), Hyp(Call("HasLipschitzShadowing", Id("f"))),
            Call("MetricHasShadowing", Id("f"))),
            "For accuracy epsilon use delta=min(cutoff,epsilon/(2L)). Positivity and L delta at most epsilon/2 preserve strict tracing."),
        Theorem("natural-shift-iterates", "shift_one_iterate_apply", "Natural iterates of the existing shift", St(
            All("A", Id("Type")), All("x", Map(Nat, Id("A"))), All("i", Nat), All("j", Nat),
            Seq(Call("iterate", Call("shift", D(1)), Id("i"), Id("x"), Id("j")), Sp, Eq, Sp,
                Call("apply", Id("x"), Seq(Id("i"), Plus, Id("j"))))),
            "SymbolicDynamics.FullShift.shift(1) sends x(j) to x(j+1); its i-th iterate reads x(i+j)."),
        Theorem("infinite-overlap", "diagonal_splice_overlap", "An extra coordinate from diagonal overlap", St(
            All("A", Id("Type")), All("z", Map(Nat, Map(Nat, Id("A")))), All("N", Nat),
            Hyp(Seq(Open, All("i", Nat), All("j", Nat), Id("j"), Sp, Le, Sp, Id("N"), Sp, Rightarrow, Sp,
                Call("apply", Id("z"), Id("i"), Seq(Id("j"), Plus, D(1))), Sp, Eq, Sp,
                Call("apply", Id("z"), Seq(Id("i"), Plus, D(1)), Id("j")), Close)),
            All("i", Nat), All("j", Nat), Hyp(Seq(Id("j"), Sp, Le, Sp, Id("N"), Plus, D(1))),
            Seq(Call("apply", Call("diagonalSplice", Id("z")), Seq(Id("i"), Plus, Id("j"))), Sp, Eq, Sp,
                Call("apply", Id("z"), Id("i"), Id("j")))),
            "The splice is y(k)=z(k)(0), an element of the full product. Induction on j transports z(i+j)(0) backwards along overlap identities. "
            + "Every edge agrees through N, so each shifted splice agrees through N+1 with z(i), simultaneously for every natural time."),
        Theorem("mismatch-telescope", "diagonal_mismatch_edge", "A mismatch must cross an earlier edge", St(
            All("A", Id("Type")), All("z", Map(Nat, Map(Nat, Id("A")))), All("i", Nat), All("j", Nat),
            Hyp(Seq(Call("apply", Call("diagonalSplice", Id("z")), Seq(Id("i"), Plus, Id("j"))), Sp, Neq, Sp,
                Call("apply", Id("z"), Id("i"), Id("j")))),
            Seq(Exists, Sp, Id("t"), Comma, Sp, Exists, Sp, Id("k"), Comma,
                Id("i"), Sp, Le, Sp, Id("t"), Sp, Land, Sp, Id("t"), Sp, Lt, Sp, Id("i"), Plus, Id("j"), Sp, Land, Sp,
                Id("k"), Sp, Lt, Sp, Id("j"), Sp, Land, Sp,
                Call("apply", Id("z"), Id("t"), Seq(Id("k"), Plus, D(1))), Sp, Neq, Sp,
                Call("apply", Id("z"), Seq(Id("t"), Plus, D(1)), Id("k")))),
            "A mismatch at coordinate j of time i either occurs on the current edge at j-1 or survives at time i+1 with coordinate j-1. "
            + "Iteration terminates before time i+j, since diagonal coordinates at j=0 agree by definition. Thus i<=t<i+j and k<j for an actual mismatching edge."))));
}
