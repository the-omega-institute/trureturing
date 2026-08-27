using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class ObserverUltrametricThresholdClosureDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supremum distance over a bounded ultrametric readout family is an "
            + "ultrapseudometric whose nonnegative threshold kernels are equivalence relations.",
        H("Observer Ultrametric Threshold Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-ultrametric-threshold-closure"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometryLaws/"
                        + "ObserverUltrametricThresholdClosure."
                        + "observer_ultrametric_threshold_closure"),
                H("Observer suprema preserve ultrametric threshold closure"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public statement constructs d_Q as the real supremum of the "
                            + "coordinate distances over the selected observer set Q. The "
                            + "boundedness premise makes every such supremum well defined.")),
                    Paragraph(Text(
                        "A coordinate strong triangle inequality passes through the supremum. "
                            + "Self-distance, symmetry, and nonnegativity pass through as well, "
                            + "including the empty observer set where the real supremum is zero.")),
                    Paragraph(Text(
                        "The threshold carrier is NNReal, so every admitted threshold is "
                            + "nonnegative without an additional premise. Reflexivity, symmetry, "
                            + "and transitivity then follow from the three corresponding distance "
                            + "laws."))),
                DescribeRole.Theorem))));

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Dist(Formula left, Formula right) =>
        Call("dist", left, right);

    private static Formula Readout(Formula q, Formula p, Formula x) =>
        Apply(Apply(q, p), x);

    private static Formula Dq(Formula dQ, Formula x, Formula y) =>
        Seq(dQ, Open, x, Comma, Sp, y, Close);

    private static Formula Kernel(Formula kernel, Formula epsilon, Formula x, Formula y) =>
        Seq(kernel, Open, epsilon, Comma, Sp, x, Comma, Sp, y, Close);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nnreal = Seq(Operatorname, Grp(F.Id("NNReal")));
        Formula pType = F.Id("P");
        Formula xType = F.Id("X");
        Formula lambda = F.Id("Lambda");
        Formula observerSet = F.Id("Q");
        Formula readout = F.Id("q");
        Formula dQ = new Formula.Subscript(F.Id("d"), observerSet);
        Formula kernel = new Formula.Subscript(F.Id("K"), observerSet);
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula epsilon = F.Id("epsilon");
        Formula readoutPx = Readout(readout, p, x);
        Formula readoutPy = Readout(readout, p, y);
        Formula supremumValues = new Formula.SetBuilder(
            Dist(readoutPx, readoutPy), p, observerSet);
        Formula distanceDefinition = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, xType, Comma, Sp,
            Dq(dQ, x, y), Sp, Eq, Sp, Call("sSup", supremumValues));
        Formula kernelDefinition = Seq(
            Forall, Sp, epsilon, Colon, Sp, nnreal, Comma, Sp,
            x, Comma, Sp, y, Colon, Sp, xType, Comma, Sp,
            Kernel(kernel, epsilon, x, y), Sp, Iff, Sp,
            Dq(dQ, x, y), Sp, Leq, Sp, epsilon);
        Formula bounded = Seq(
            Forall, Sp, a, Comma, Sp, b, Colon, Sp, lambda, Comma, Sp,
            Dist(a, b), Sp, Leq, Sp, D(1));
        Formula strongTriangle = Seq(
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, c, Colon, Sp, lambda,
            Comma, Sp, Dist(a, c), Sp, Leq, Sp,
            Max, Open, Dist(a, b), Comma, Sp, Dist(b, c), Close);
        Formula nonnegative = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, xType, Comma, Sp,
            D(0), Sp, Leq, Sp, Dq(dQ, x, y));
        Formula self = Seq(
            Forall, Sp, x, Colon, Sp, xType, Comma, Sp,
            Dq(dQ, x, x), Sp, Eq, Sp, D(0));
        Formula symmetric = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, xType, Comma, Sp,
            Dq(dQ, x, y), Sp, Eq, Sp, Dq(dQ, y, x));
        Formula observerTriangle = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp, z, Colon, Sp, xType,
            Comma, Sp, Dq(dQ, x, z), Sp, Leq, Sp,
            Max, Open, Dq(dQ, x, y), Comma, Sp, Dq(dQ, y, z), Close);
        Formula equivalence = Seq(
            Forall, Sp, epsilon, Colon, Sp, nnreal, Comma, Sp,
            Call("Equivalence", Seq(kernel, Open, epsilon, Close)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, pType, Comma, Sp, xType, Comma, Sp,
            lambda, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typeclass("PseudoMetricSpace", lambda), Comma, RowBreak, Grp(),
            observerSet, Colon, Sp, Call("Set", pType), Comma, Sp,
            readout, Colon, Sp,
            Arrow(pType, Arrow(xType, lambda)), Comma, RowBreak, Grp(),
            bounded, Comma, RowBreak, Grp(),
            strongTriangle, Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            dQ, Colon, Sp, Arrow(xType, Arrow(xType, real)), Comma, Sp,
            distanceDefinition, Comma, RowBreak, Grp(),
            kernel, Colon, Sp,
            Arrow(nnreal, Arrow(xType, Arrow(xType, prop))), Comma, Sp,
            kernelDefinition, Close, SemiSpace, RowBreak, Grp(),
            Open, nonnegative, Close, Sp, Land, RowBreak, Grp(),
            Open, self, Close, Sp, Land, RowBreak, Grp(),
            Open, symmetric, Close, Sp, Land, RowBreak, Grp(),
            Open, observerTriangle, Close, Sp, Land, RowBreak, Grp(),
            equivalence, Dot,
            End, Grp(F.Id("gathered"))));
    }

}
