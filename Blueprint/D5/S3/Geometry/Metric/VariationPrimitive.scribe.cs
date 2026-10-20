using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Metric;

internal sealed class VariationPrimitiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute continuity of accumulated metric variation and its exact interval increments.",
        H("Absolute continuity and accumulated metric variation"),
        Blocks(
            Paragraph(Text(
                "Let X be an arbitrary metric space, let T be positive, and let z from the real line to X "
                + "be absolutely continuous on [0,T]. Define A(t) as variationOnFromTo z (Icc 0 T) 0 t. "
                + "Then A is absolutely continuous on [0,T], and A(b)-A(a) is the real value of the "
                + "extended metric variation of z on [a,b] for every 0 ≤ a ≤ b ≤ T.")),
            Describe.Lean(
                DescribeId.Create("metric-ac-bounded-variation-on"),
                DeclarationHandle.Create("D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_boundedVariationOn"),
                H("Absolute continuity gives bounded metric variation"),
                StatementSource.FromAuthor(Disp(HelperStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any pseudometric space Y, any real endpoints a and b, and any f from the real line "
                    + "to Y, absolute continuity on the unordered interval implies bounded variation there. "
                    + "This auxiliary proof reuses the partition argument of Mathlib's "
                    + "AbsolutelyContinuousOnInterval.boundedVariationOn at revision "
                    + "56a005855ea17e0b0958f73ec801ae140b0a1679. It subdivides the interval into finitely "
                    + "many pieces shorter than an absolute-continuity modulus, bounds every partition sum "
                    + "on each piece, and adds the finite variations. The auxiliary result is used in both "
                    + "the increment identity and the proof of absolute continuity of A."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("metric-ac-variation-exact-increments"),
                DeclarationHandle.Create("D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_variation_exact_increments"),
                H("Exact increments of accumulated variation"),
                StatementSource.FromAuthor(Disp(MetricStatement(ExactIncrementStatement()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Bounded variation supplies the finiteness required by variationOnFromTo.sub_right. "
                    + "Subtracting A(a) from A(b) gives variationOnFromTo z (Icc 0 T) a b; "
                    + "variationOnFromTo.eq_of_le identifies this with the real variation on "
                    + "Icc 0 T intersect Icc a b. Since 0 ≤ a ≤ b ≤ T, this intersection is Icc a b. "
                    + "This identity is consumed in the proof that A is absolutely continuous."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("metric-ac-implies-ac-variation-primitive"),
                DeclarationHandle.Create("D5/S3/Geometry/Metric/VariationPrimitive.metric_AC_implies_AC_variation_primitive"),
                H("The variation primitive is absolutely continuous"),
                StatementSource.FromAuthor(Disp(MetricStatement(PrimitiveStatement()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a positive epsilon and choose the absolute-continuity modulus of z at epsilon/2. "
                    + "For a finite disjoint family of intervals of total length below that modulus, choose "
                    + "an arbitrary monotone partition inside each interval. Index all partition segments by "
                    + "the dependent finite sum of their segment indices. Within one interval, monotonicity "
                    + "makes the half-open segments disjoint; across different intervals, containment in the "
                    + "original disjoint family gives disjointness. Their lengths telescope in each interval, "
                    + "so the flattened family's total length is bounded by the original total length. "
                    + "The finite-family absolute-continuity estimate therefore bounds the sum of all image "
                    + "segment distances by epsilon/2. The private refinement_bound constructs this family; "
                    + "ac_finite_family reindexes it through a finite enumeration. Taking the finitely many "
                    + "partition suprema with finite_sup_bound bounds the sum of interval variations. "
                    + "Their finiteness permits passage to real values. The exact increment identity turns "
                    + "these real variations into the endpoint distances of A, whose sum is less than epsilon. "
                    + "Thus the argument estimates the actual accumulated variation, for every such "
                    + "disjoint family, throughout the original metric-space telescope."))),
                DescribeRole.Theorem)),
        []));

    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(F.Forall, F.Sp, V(name), F.Colon, F.Sp, type, F.Comma, F.Sp, body);
    private static Formula Implies(Formula p, Formula q) => Call("Implies", p, q);
    private static Formula Icc(Formula a, Formula b) => Call("Icc", a, b);
    private static Formula Accumulated() =>
        Call("variationOnFromTo", V("z"), Icc(Num(0), V("T")), Num(0));
    private static Formula At(Formula t) => Call("Apply", Accumulated(), t);

    private static Formula HelperStatement() =>
        All("Y", V("Type"), All("metric", Call("PseudoMetricSpace", V("Y")),
        All("f", Call("RealTo", V("Y")), All("a", V("Real"), All("b", V("Real"),
            Implies(Call("AbsolutelyContinuousOnInterval", V("f"), V("a"), V("b")),
                Call("BoundedVariationOn", V("f"), Call("uIcc", V("a"), V("b")))))))));

    private static Formula MetricStatement(Formula conclusion) =>
        All("X", V("Type"), All("metric", Call("MetricSpace", V("X")),
        All("z", Call("RealTo", V("X")), All("T", V("Real"),
            Implies(Call("LT", Num(0), V("T")),
                Implies(Call("AbsolutelyContinuousOnInterval", V("z"), Num(0), V("T")), conclusion))))));

    private static Formula ExactIncrementStatement() =>
        All("a", V("Real"), All("b", V("Real"),
            Implies(Call("And", Call("Mem", V("a"), Icc(Num(0), V("T"))),
                Call("And", Call("Mem", V("b"), Icc(Num(0), V("T"))), Call("LE", V("a"), V("b")))),
                Call("Eq", Call("Sub", At(V("b")), At(V("a"))),
                    Call("ToReal", Call("eVariationOn", V("z"), Icc(V("a"), V("b"))))))));

    private static Formula PrimitiveStatement() =>
        Call("AbsolutelyContinuousOnInterval", Accumulated(), Num(0), V("T"));
}
