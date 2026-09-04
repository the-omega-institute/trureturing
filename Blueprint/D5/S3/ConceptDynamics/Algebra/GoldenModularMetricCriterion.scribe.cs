using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Algebra;

internal sealed class GoldenModularMetricCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Algebra/GoldenModularMetricCriterion."
            + "golden_modular_metric_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden modular flow reaches its positive-metric unitary boundary exactly "
            + "at zero horizontal drift.",
        H("Golden Modular Metric Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-modular-metric-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Positive metric realization is equivalent to zero modular drift"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The source matrix is constructed in its two-dimensional eigenbasis "
                        + "from arbitrary real drift and phase and the fixed golden "
                        + "logarithmic period.")),
                Paragraph(Text(
                    "Zero drift, unit norm of every spectral value, preservation of a "
                        + "positive definite Hermitian metric, and vanishing normalized "
                        + "trace defect are equivalent.")),
                Paragraph(Text(
                    "At nonzero drift, a zero of the completed reading retains its "
                        + "canonical same-height reflected zero, while no positive "
                        + "definite invariant metric exists."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula delta = DeltaLower;
        Formula gamma = GammaLower;
        Formula period = F.Id("P");
        Formula exponent = F.Id("a");
        Formula forward = F.Id("u");
        Formula backward = F.Id("v");
        Formula monodromy = F.Id("M");
        Formula rho = Rho;
        Formula defect = F.Id("U");
        Formula lambda = LambdaLower;
        Formula metric = F.Id("H");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), complex);
        Formula half = Seq(Frac, Grp(D(1)), Grp(D(2)));

        Formula periodValue = Seq(
            D(2), Sp, Cdot, Sp, Call("log", Varphi));
        Formula exponentValue = Seq(
            Open, delta, Sp, Plus, Sp, F.Id("i"), gamma, Close,
            Sp, Cdot, Sp, period);
        Formula forwardValue = Call("exp", exponent);
        Formula backwardValue = Call("exp", Seq(Minus, Open, exponent, Close));
        Formula modeVector = Grp(
            OpenBracket, forward, Comma, Sp, backward, CloseBracket);
        Formula rhoValue = Seq(
            half, Sp, Plus, Sp, delta, Sp, Plus, Sp, F.Id("i"), gamma);
        Formula adjoint = Seq(monodromy, Caret, Grp(Star));
        Formula traceProduct = Call(
            "trace", Seq(adjoint, Sp, Cdot, Sp, monodromy));
        Formula defectValue = Seq(
            half, Sp, Cdot, Sp, Call("Re", traceProduct), Sp, Minus, Sp, D(1));

        Formula periodDefinition = Let(period, real, periodValue);
        Formula exponentDefinition = Let(exponent, complex, exponentValue);
        Formula forwardDefinition = Let(forward, complex, forwardValue);
        Formula backwardDefinition = Let(backward, complex, backwardValue);
        Formula matrixDefinition = Let(monodromy, matrix, Call("diagonal", modeVector));
        Formula rhoDefinition = Let(rho, complex, rhoValue);
        Formula defectDefinition = Let(defect, real, defectValue);

        Formula zeroDrift = Seq(delta, Sp, Eq, Sp, D(0));
        Formula unitSpectrum = Seq(
            Forall, Sp, Typed(lambda, complex), Comma, Sp,
            lambda, Sp, InMacro, Sp, Call("spectrum", complex, monodromy), Comma, Sp,
            new Formula.Norm(lambda), Sp, Eq, Sp, D(1));
        Formula invariantMetric = Seq(
            Exists, Sp, Typed(metric, matrix), Comma, Sp,
            Call("PosDef", metric), Sp, Land, Sp,
            adjoint, Sp, Cdot, Sp, metric, Sp, Cdot, Sp,
            monodromy, Sp, Eq, Sp, metric);
        Formula zeroDefect = Seq(defect, Sp, Eq, Sp, D(0));
        Formula conditions = Grp(
            OpenBracket,
            zeroDrift, Comma, RowBreak, Grp(),
            unitSpectrum, Comma, RowBreak, Grp(),
            invariantMetric, Comma, RowBreak, Grp(),
            zeroDefect,
            CloseBracket);

        Formula sourceZero = Seq(Call("xiReading", rho), Sp, Eq, Sp, D(0));
        Formula reflectedZero = Seq(
            Call("xiReading", Call("criticalLineMirror", rho)),
            Sp, Eq, Sp, D(0));
        Formula reflectionClause = Grp(
            sourceZero, Sp, Rightarrow, Sp, reflectedZero);
        Formula noInvariantMetric = Seq(Neg, Sp, invariantMetric);
        Formula offLineConsequence = Grp(
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Grp(reflectionClause, Sp, Land, Sp, noInvariantMetric));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, delta, Comma, Sp, gamma, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            periodDefinition, exponentDefinition,
            RowBreak, Grp(),
            forwardDefinition, backwardDefinition,
            RowBreak, Grp(),
            matrixDefinition, rhoDefinition,
            RowBreak, Grp(),
            defectDefinition,
            RowBreak, Grp(),
            Call("ListTFAE", conditions), Sp, Land,
            RowBreak, Grp(),
            offLineConsequence, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Let(Formula value, Formula type, Formula definition) => Seq(
        Operatorname, Grp(F.Id("let")), Sp,
        Typed(value, type), Sp, Eq, Sp, definition, Semi, Sp);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
