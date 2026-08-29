using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class OneScaleInformationalCompletenessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All integer moments of one weighted Cayley pushforward determine the real spectrum.",
        H("One-Scale Informational Completeness"),
        Blocks(Describe.Lean(
            DescribeId.Create("one-scale-cayley-moments-determine-real-spectrum"),
            DeclarationHandle.Create(
                "D5/S3/Observer/MeasureSeparation/OneScaleInformationalCompleteness."
                    + "one_scale_informational_completeness"),
            H("One complete Cayley scale determines the spectrum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The proposition constructs the source resolvent density, the scaled "
                        + "Cayley point, its additive-circle coordinate, and the resulting "
                        + "pushforward measure from each real spectrum.")),
                Paragraph(Text(
                    "Finite resolvent budgets make both circle measures finite. Equality of "
                        + "every integer Fourier moment identifies them through the separating "
                        + "Fourier star algebra.")),
                Paragraph(Text(
                    "The Cayley coordinate is a measurable embedding. Pulling the measure "
                        + "equality back and cancelling the everywhere positive finite density "
                        + "recovers equality of the original real measures."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula ennreal = Call("ENNReal");
        Formula a = F.Id("a");
        Formula xi = F.Id("xi");
        Formula theta = F.Id("theta");
        Formula n = F.Id("n");
        Formula nu1 = F.Id("nu1");
        Formula nu2 = F.Id("nu2");
        Formula density = F.Id("density");
        Formula cayleyPoint = F.Id("cayleyPoint");
        Formula cayleyCoordinate = F.Id("cayleyCoordinate");
        Formula circleMeasure = F.Id("circleMeasure");
        Formula realMeasure = Call("Measure", real);
        Formula additiveCircle = Call("AddCircle", Seq(D(2), Sp, Cdot, Sp, Pi));
        Formula xiSquared = new Formula.Power(xi, D(2));
        Formula aSquared = new Formula.Power(a, D(2));
        Formula resolvent = new Formula.Fraction(
            D(1), Seq(xiSquared, Sp, Plus, Sp, aSquared));
        Formula integrand = Seq(xi, Sp, Mapsto, Sp, resolvent);
        Formula cayleyValue = new Formula.Fraction(
            Seq(xi, Sp, Plus, Sp, F.Id("i"), Cdot, Sp, a),
            Seq(xi, Sp, Minus, Sp, F.Id("i"), Cdot, Sp, a));
        Formula circleAtNu1 = Apply(circleMeasure, nu1);
        Formula circleAtNu2 = Apply(circleMeasure, nu2);
        Formula fourierAtTheta = Apply(F.Id("fourier"), n, theta);
        Formula moment1 = Call(
            "integral", circleAtNu1, Seq(theta, Sp, Mapsto, Sp, fourierAtTheta));
        Formula moment2 = Call(
            "integral", circleAtNu2, Seq(theta, Sp, Mapsto, Sp, fourierAtTheta));
        Formula finiteBudget1 = Call("HasFiniteIntegral", integrand, nu1);
        Formula finiteBudget2 = Call("HasFiniteIntegral", integrand, nu2);

        Formula densityDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            density, Colon, Sp, Arrow(real, ennreal), Sp, Colon, Eq, Sp,
            xi, Sp, Mapsto, Sp, Call("ofReal", resolvent), Comma);
        Formula cayleyDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            cayleyPoint, Colon, Sp, Arrow(real, F.Id("Circle")), Sp, Colon, Eq, Sp,
            xi, Sp, Mapsto, Sp, Call("circlePoint", cayleyValue), Comma);
        Formula coordinateDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            cayleyCoordinate, Colon, Sp, Arrow(real, additiveCircle), Sp, Colon, Eq, Sp,
            xi, Sp, Mapsto, Sp,
            Call("symm", Seq(Operatorname, Grp(F.Id("homeomorphCircle")), Apos),
                Apply(cayleyPoint, xi)), Comma);
        Formula circleMeasureDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            circleMeasure, Colon, Sp,
            Arrow(realMeasure, Call("Measure", additiveCircle)), Sp, Colon, Eq, Sp,
            F.Id("nu"), Sp, Mapsto, Sp,
            Call("map", cayleyCoordinate,
                Call("withDensity", F.Id("nu"), density)), Comma);
        Formula allMoments = Seq(
            Forall, Sp, n, Colon, Sp, integers, Comma, Sp,
            moment1, Sp, Eq, Sp, moment2);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, a, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            nu1, Comma, Sp, nu2, Colon, Sp, realMeasure, Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, a, Sp, Land,
            RowBreak, Grp(),
            finiteBudget1, Sp, Land,
            RowBreak, Grp(),
            finiteBudget2, Sp, Rightarrow,
            RowBreak, Grp(),
            densityDefinition,
            RowBreak, Grp(),
            cayleyDefinition,
            RowBreak, Grp(),
            coordinateDefinition,
            RowBreak, Grp(),
            circleMeasureDefinition,
            RowBreak, Grp(),
            Open, allMoments, Close, Sp, Rightarrow, Sp,
            nu1, Sp, Eq, Sp, nu2, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

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
