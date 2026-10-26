using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class ActualCycleLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual nonempty shapes determine a normalized marked-cycle law and a common realization of every finite cycle prefix.",
        H("Actual Countable Cycle Law"),
        Blocks(
            Paragraph(Text(
                "A marked cycle records its initial direct or skew sign, every actual right "
                + "removal shape, and its final actual indecomposable left shape. Each shape "
                + "has positive length. Right removals flip the sign; the terminal shape "
                + "uses the resulting sign. A cycle may have no right removals. The mark "
                + "retains the entire permutation shape at every step.")),
            Paragraph(Text(
                "Let t=sqrt(2)-1, rho=t squared and c=(1-t)/2. Fixed(s,r), denoted F(s,r), "
                + "contains exactly r right removals before the terminal shape. Its recursive "
                + "decoder is a bijection from the disjoint union over natural r to the "
                + "existing unbounded actual cycles of sign s, and preserves total length. "
                + "Thus the marked cycle space C is countable. Write W(x)=ofReal(rho raised "
                + "to size(x)), an extended nonnegative weight, on either cycle representation. "
                + "The probability mass function p on C has exactly these weights.")),
            Paragraph(Text(
                "Omega is C to the natural power, with its product measurable space, and "
                + "mu is the countable product of the probability measure of p. A tuple "
                + "gamma in UnboundedTuple(k) retains its ordered k actual marked cycles; "
                + "nth(k) sends such a tuple to its function on Fin(k), and is bijective. "
                + "its cylinder [gamma] fixes precisely the first k stream coordinates. "
                + "For k=0 this cylinder is the whole space. The map res(I) restricts a "
                + "stream to a finite set I of natural indices. Product(I,p) denotes the "
                + "finite product measure with coordinate law p.toMeasure.")),
            Describe.Lean(
                DescribeId.Create("actual-countable-cycle-law"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/ActualCycleLaw.actual_countable_cycle_law"),
                H("Normalization and actual finite-prefix limits"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here s ranges over both Boolean cut signs, r and k over natural "
                        + "numbers, gamma over all unbounded k-tuples, and I over finite "
                        + "sets of natural indices. The mass of F(s,r) is ofReal(c*t^r), "
                        + "and the mass of all marked cycles is one. Every prefix cylinder "
                        + "is measurable and has mass W(gamma), using its total size. For "
                        + "every gamma there are finite K,H and a bounded actual tuple d "
                        + "whose erasure is gamma and whose actual uniform-permutation "
                        + "probability converges to the real mass of [gamma]. The function "
                        + "p(d,n) in the formula is Tuple.probability: it is the actual "
                        + "EventFor mass when n exceeds its original threshold and zero "
                        + "otherwise. The limit is along all natural source sizes.")),
                    Paragraph(Text(
                        "The coordinate cycles on this one stream are independent and "
                        + "every finite restriction has its corresponding product law. "
                        + "This asserts independence between complete cycles. Within one "
                        + "cycle all shapes and the alternating signs belong to the same "
                        + "mark; no independence between its terminal type and its number "
                        + "of low-value removals is used or asserted.")),
                    Paragraph(Text(
                        "The actual critical shape counts give total right-shape weight t "
                        + "and total terminal-shape weight c for either sign. A recursive "
                        + "bijection preserves both these actual shape carriers and every "
                        + "length. Therefore exactly r removals have weight c*t^r for each "
                        + "initial sign. Summing the geometric series gives "
                        + "2*c/(1-t)=1. This proves normalization before forming the "
                        + "probability mass function. The product-measure cylinder formula "
                        + "then multiplies the actual weights, and length additivity gives "
                        + "W(gamma). The existing actual finite-tuple count-ratio limit "
                        + "identifies each such cylinder mass with a finite-permutation limit.")),
                    Paragraph(Text(
                        "A common marked-cycle stream is not yet a reconstructed infinite "
                        + "permutation. This result does not prove equality of actual "
                        + "history events across different caps, all position or label "
                        + "cutoff observations, the low-removal and terminal-type joint "
                        + "distribution, or the conditional predictable hazard. Literal "
                        + "position and label transport, the precycle filtration and the "
                        + "occupation and marginal discrepancy hypotheses remain separate "
                        + "mathematical requirements."))),
                DescribeRole.Theorem))));

    private static StrataLint.Scribe.Formula V(string name) => F.Id(name);
    private static StrataLint.Scribe.Formula P(StrataLint.Scribe.Formula body) =>
        Seq(Open, body, Close);
    private static StrataLint.Scribe.Formula All(
        StrataLint.Scribe.Formula variables, StrataLint.Scribe.Formula body) =>
        P(Seq(Forall, Sp, variables, Comma, Sp, body));
    private static StrataLint.Scribe.Formula W(StrataLint.Scribe.Formula value) => Call("W", value);
    private static StrataLint.Scribe.Formula Cylinder() => Call("cyl", V("gamma"));
    private static StrataLint.Scribe.Formula Mass() => Call("mu", Cylinder());
    private static StrataLint.Scribe.Formula Statement() => Seq(
        Call("Countable", V("C")), Sp, Land, Sp,
        Call("IsProbabilityMeasure", V("mu")), Sp, Land, Sp,
        All(V("k"), Call("Bijective", Call("nth", V("k")))), Sp, Land, Sp,
        All(Seq(V("s"), Comma, V("r")), Seq(
            Sum, Underscore, Grp(V("x"), InMacro, Sp, Call("F", V("s"), V("r"))), W(V("x")),
            Eq, Call("ofReal", Seq(V("c"), Cdot, Sp, V("t"), Caret, Grp(V("r")))))),
        Sp, Land, Sp,
        P(Seq(Sum, Underscore, Grp(V("x"), InMacro, Sp, V("C")), W(V("x")), Eq, D(1))),
        Sp, Land, Sp,
        All(Seq(V("k"), Comma, V("gamma"), InMacro, Sp, Call("UnboundedTuple", V("k"))), Seq(
            Call("MeasurableSet", Cylinder()), Sp, Land, Sp, Mass(), Eq, W(V("gamma")))),
        Sp, Land, Sp,
        All(Seq(V("k"), Comma, V("gamma"), InMacro, Sp, Call("UnboundedTuple", V("k"))), Seq(
            Exists, Sp, V("K"), Comma, V("H"), Comma, V("d"), InMacro, Sp,
            Call("Tuple", V("K"), V("H"), V("k")), Comma, Sp,
            Call("erase", V("d")), Eq, V("gamma"), Sp, Land, Sp,
            Lim, Underscore, Grp(V("n"), To, Infty), Call("p", V("d"), V("n")),
            Eq, Call("toReal", Mass()))),
        Sp, Land, Sp, Call("iIndepFun", V("coordinates"), V("mu")),
        Sp, Land, Sp,
        All(Seq(V("I"), InMacro, Sp, Call("Finset", V("N"))), Seq(
            Call("map", V("mu"), Call("res", V("I"))), Eq,
            Call("Product", V("I"), V("p")))));
}
