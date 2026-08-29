using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class PositiveTorusCarrierCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative weighted torus period whose nontrivial zeros are critical and whose "
            + "auxiliary factor is regular forces all nontrivial zeta zeros onto the midline.",
        H("Positive Torus Carrier Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-torus-carrier-condition"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/PositiveTorusCarrierCriterion."
                        + "positive_torus_carrier_condition"),
                H("A regular positive torus carrier implies the critical-line criterion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The measure mu is the literal Measure.sum of the supplied period "
                            + "measures scaled by NNReal weights. The period Fmu is the Bochner "
                            + "integral of the supplied Eisenstein family against mu. The "
                            + "auxiliary factor Gmu is the literal weighted tsum of the local and "
                            + "twisted-completion factors.")),
                    Paragraph(Text(
                        "The Hecke factorization is required whenever Gmu is analytic and nonzero "
                            + "at the evaluation point. The two source regularity clauses provide "
                            + "exactly those facts on the open right half-plane, so every right-half "
                            + "completed-zeta zero becomes a zero of Fmu and hence lies on the "
                            + "midline by the period-zero premise.")),
                    Paragraph(Text(
                        "The frozen completed-zeta zero theorem supplies the canonical nontrivial "
                            + "zeta carrier. Frozen conjugate reflection transports any left-half "
                            + "zero to the right half and completes the global conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula LessThan(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula complex = Call("Complex");
        Formula nnreal = Call("NNReal");
        Formula indexType = F.Id("Index");
        Formula torus = F.Id("Torus");
        Formula weights = F.Id("a");
        Formula periodMeasures = F.Id("muD");
        Formula eisenstein = F.Id("EStar");
        Formula localFactor = F.Id("e");
        Formula twistedCompleted = F.Id("twistedCompleted");
        Formula index = F.Id("i");
        Formula point = F.Id("s");
        Formula torusPoint = F.Id("z");
        Formula mu = F.Id("mu");
        Formula period = F.Id("Fmu");
        Formula auxiliary = F.Id("Gmu");
        Formula rightHalf = F.Id("Hplus");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula realPart = Call("re", point);
        Formula complexFamily = Arrow(indexType, Arrow(complex, complex));

        Formula weightAt = Apply(weights, index);
        Formula measureAt = Apply(periodMeasures, index);
        Formula scaledMeasure = Seq(
            Call("toENNReal", weightAt), Sp, Cdot, Sp, measureAt);
        Formula measureSum = Call("measureSum", Lambda(index, scaledMeasure));
        Formula eisensteinAt = Apply(Apply(eisenstein, torusPoint), point);
        Formula periodIntegral = Call(
            "integral", Lambda(torusPoint, eisensteinAt), mu);
        Formula localTerm = Seq(
            Call("toComplex", weightAt), Sp, Times, Sp,
            Apply(Apply(localFactor, index), point), Sp, Times, Sp,
            Apply(Apply(twistedCompleted, index), point));
        Formula auxiliarySum = Call("tsum", Lambda(index, localTerm));
        Formula rightHalfSet = new Formula.SetBuilder(
            LessThan(half, realPart), point, complex);
        Formula analyticAndNonzero = And(
            Call("AnalyticAt", complex, auxiliary, point),
            Seq(Apply(auxiliary, point), Sp, Neq, Sp, D(0)));
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                analyticAndNonzero,
                EqualTo(
                    Apply(period, point),
                    Seq(
                        Call("completedRiemannZeta", point), Sp, Times, Sp,
                        Apply(auxiliary, point)))));
        Formula periodZeroInStrip = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                And(
                    EqualTo(Apply(period, point), D(0)),
                    And(
                        LessThan(D(0), realPart),
                        LessThan(realPart, D(1)))),
                EqualTo(realPart, half)));
        Formula auxiliaryAnalytic =
            Call("AnalyticOnNhd", complex, auxiliary, rightHalf);
        Formula auxiliaryNonzero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Call("mem", point, rightHalf),
                Seq(Apply(auxiliary, point), Sp, Neq, Sp, D(0))));
        Formula hypotheses = Seq(
            Open, factorization, Close, Sp, Land, Sp,
            Open, periodZeroInStrip, Close, Sp, Land, Sp,
            auxiliaryAnalytic, Sp, Land, Sp,
            Open, auxiliaryNonzero, Close);
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", complex)],
            Implies(
                Call("IsNontrivialZero", F.Id("rho")),
                EqualTo(Call("re", F.Id("rho")), half)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, torus, Sp, InMacro, Sp, type, Comma, Sp,
                Call("MeasurableSpace", torus)),
            Seq(
                weights, Colon, Sp, Arrow(indexType, nnreal), Comma, Sp,
                periodMeasures, Colon, Sp,
                Arrow(indexType, Call("Measure", torus))),
            Seq(
                eisenstein, Colon, Sp, Arrow(torus, Arrow(complex, complex)), Comma, Sp,
                localFactor, Comma, Sp, twistedCompleted, Colon, Sp, complexFamily),
            Seq(mu, Sp, Colon, Eq, Sp, measureSum),
            Seq(period, Sp, Colon, Eq, Sp, Lambda(point, periodIntegral)),
            Seq(auxiliary, Sp, Colon, Eq, Sp, Lambda(point, auxiliarySum)),
            Seq(rightHalf, Sp, Colon, Eq, Sp, rightHalfSet),
            Seq(
                Open, hypotheses, Close, Sp, Rightarrow, Sp, conclusion, Dot),
        ]));
    }
}
