using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class CauchyMeasureEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The relative entropy of positive-scale Cauchy measures at a common center has its "
            + "closed form and obeys strict scale-flow laws.",
        H("Cauchy Measure Relative Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cauchy-measure-relative-entropy"),
                Handle("cauchy_measure_relative_entropy"),
                H("Cauchy measure relative entropy and its analytic prerequisites"),
                StatementSource.FromAuthor(Evaluation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "NNReal denotes the nonnegative real numbers. Both scales are nonzero. "
                            + "The measures, log-likelihood ratio llr, and ENNReal-valued klDiv "
                            + "are Mathlib's existing objects. cauchyKL is the imported real "
                            + "closed form, with nonnegative scales coerced to real numbers.")),
                    Paragraph(Text(
                        "Positive densities establish absolute continuity and identify the "
                            + "Radon--Nikodym density ratio. A uniform bound on that ratio and "
                            + "its reciprocal proves logarithmic integrability. Differentiation "
                            + "under the integral, a mixed rational-kernel evaluation, and the "
                            + "mean value theorem compute the logarithmic expectation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cauchy-poisson-coarse-graining"),
                Handle("cauchy_poisson_coarse_graining"),
                H("Positive smoothing, admissible reverse shifts, and boundary divergence"),
                StatementSource.FromAuthor(ScaleFlow()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A common time shift h replaces the two scales delta minus omega "
                            + "and delta plus omega by delta plus h minus omega and delta plus h "
                            + "plus omega. The source domain is zero less than omega less than "
                            + "delta. A negative shift must also preserve omega less than delta "
                            + "plus h, so both scales remain positive.")),
                    Paragraph(Text(
                        "toNNReal is the canonical real-to-nonnegative-real conversion; every "
                            + "scale in the strict inequalities is positive. nhdsLT(delta) is "
                            + "the left neighborhood filter. The final conjunct is a limit in "
                            + "ENNReal to infinity, with the real variable w explicitly bound. "
                            + "It does not substitute the zero-scale Dirac branch into the "
                            + "positive-scale evaluation."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create("D5/S3/Divergence/CauchyMeasureEntropy." + name);

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Nonzero(Formula value) =>
        new Formula.Relation(value, FormulaRelationOperator.NotEqual, D(0));

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Measure(Formula gamma, Formula scale) =>
        Call("cauchyMeasure", gamma, scale);

    private static Formula ShiftValue(Formula gamma, Formula centerScale, Formula offset) =>
        Call("klDiv",
            Measure(gamma, Call("toNNReal", Subtract(centerScale, offset))),
            Measure(gamma, Call("toNNReal", Add(centerScale, offset))));

    private static Formula Evaluation()
    {
        var gamma = F.Id("gamma");
        var a = F.Id("a");
        var b = F.Id("b");
        var first = Measure(gamma, a);
        var second = Measure(gamma, b);
        var value = Equal(Call("klDiv", first, second),
            Call("ofReal", Call("cauchyKL", gamma, Call("toReal", a), gamma, Call("toReal", b))));
        var conclusion = And(Call("AbsolutelyContinuous", first, second),
            And(Call("Integrable", Call("llr", first, second), first), value));
        return Disp(All(
            [Bound("gamma", RealNumbers()), Bound("a", F.Id("NNReal")), Bound("b", F.Id("NNReal"))],
            Implies(And(Nonzero(a), Nonzero(b)), conclusion)));
    }

    private static Formula ScaleFlow()
    {
        var gamma = F.Id("gamma");
        var delta = F.Id("delta");
        var omega = F.Id("omega");
        var h = F.Id("h");
        var w = F.Id("w");
        var original = ShiftValue(gamma, delta, omega);
        var shifted = ShiftValue(gamma, Add(delta, h), omega);
        var forward = All([Bound("h", RealNumbers())],
            Implies(Less(D(0), h), Less(shifted, original)));
        var reverse = All([Bound("h", RealNumbers())],
            Implies(And(Less(h, D(0)), Less(omega, Add(delta, h))), Less(original, shifted)));
        var boundaryFunction = Seq(Open, w, Sp, InMacro, Sp, RealNumbers(), Sp,
            Mapsto, Sp, ShiftValue(gamma, delta, w), Close);
        var boundary = Call("Tendsto", boundaryFunction, Call("nhdsLT", delta), Call("nhds", Infty));
        return Disp(All(
            [Bound("gamma", RealNumbers()), Bound("delta", RealNumbers()), Bound("omega", RealNumbers())],
            Implies(And(Less(D(0), omega), Less(omega, delta)),
                And(forward, And(reverse, boundary)))));
    }
}
