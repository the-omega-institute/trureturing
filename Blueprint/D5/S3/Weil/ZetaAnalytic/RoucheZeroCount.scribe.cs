using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaAnalytic;

internal sealed class RoucheZeroCountDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaAnalytic/RoucheZeroCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict boundary perturbation preserves the rectangle zero count with analytic "
            + "multiplicity.",
        H("Rouche Zero-Count Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("homotopy-boundary-nonvanishing"),
                DeclarationHandle.Create(
                    Prefix + "homotopy_nonvanishing_on_rectangleBorder"),
                H("The straight-line homotopy is nonvanishing on the boundary"),
                StatementSource.FromAuthor(HomotopyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The strict boundary estimate and the interval bound on the homotopy "
                        + "parameter force the perturbation term to have norm strictly below "
                        + "the base value, so their sum cannot vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuous-rectangle-log-derivative-integral"),
                DeclarationHandle.Create(
                    Prefix + "continuousOn_rectangleIntegral_logDeriv_straightLine"),
                H("The normalized logarithmic-derivative contour integral is continuous"),
                StatementSource.FromAuthor(ContinuityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Projection to the closed parameter interval extends the boundary "
                        + "integrand continuously. Mathlib's parametric interval-integral "
                        + "continuity theorem applies to each of the four rectangle sides, "
                        + "and the normalized contour combination remains continuous."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rectangle-rouche-zero-count"),
                DeclarationHandle.Create(
                    Prefix + "rectangle_zero_count_eq_of_norm_sub_lt"),
                H("Rectangle Rouche zero-count stability"),
                StatementSource.FromAuthor(ZeroCountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Boundary nonvanishing and contour-integral continuity put the normalized "
                        + "logarithmic-derivative integral in the discrete range of integer "
                        + "casts throughout the connected parameter interval. It is therefore "
                        + "constant, and the rectangle argument principle identifies its two "
                        + "endpoint values with the stated multiplicity sums."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Subset(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(Open, F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Rectangle(Formula z, Formula w) =>
        Call("Rectangle", z, w);

    private static Formula RectangleBorder(Formula z, Formula w) =>
        Call("RectangleBorder", z, w);

    private static Formula BoundaryEstimate(
        Formula complex,
        Formula f,
        Formula g,
        Formula z,
        Formula w)
    {
        Formula s = F.Id("s");
        return ForAll(
            [Bound("s", complex)],
            Implies(
                Member(s, RectangleBorder(z, w)),
                Less(
                    new Formula.Norm(Subtract(Apply(f, s), Apply(g, s))),
                    new Formula.Norm(Apply(g, s)))));
    }

    private static Formula AnalyticPremises(
        Formula complex,
        Formula f,
        Formula g,
        Formula z,
        Formula w)
    {
        Formula rectangle = Rectangle(z, w);
        return All(
            Less(Call("re", z), Call("re", w)),
            Less(Call("im", z), Call("im", w)),
            Call("AnalyticOnNhd", complex, f, rectangle),
            Call("AnalyticOnNhd", complex, g, rectangle),
            BoundaryEstimate(complex, f, g, z, w));
    }

    private static Formula HomotopyValue(
        Formula f,
        Formula g,
        Formula t,
        Formula s) =>
        Add(
            Apply(g, s),
            Multiply(
                Call("ofReal", t),
                Subtract(Apply(f, s), Apply(g, s))));

    private static Formula HomotopyFormula()
    {
        Formula real = Call("Real"), complex = Call("Complex");
        Formula f = F.Id("f"), g = F.Id("g"), z = F.Id("z"), w = F.Id("w");
        Formula t = F.Id("t"), s = F.Id("s");
        Formula functionType = Arrow(complex, complex);
        Formula interval = Call("Icc", D(0), D(1));
        Formula conclusion = ForAll(
            [Bound("t", real)],
            Implies(
                Member(t, interval),
                ForAll(
                    [Bound("s", complex)],
                    Implies(
                        Member(s, RectangleBorder(z, w)),
                        NotEqual(HomotopyValue(f, g, t, s), D(0))))));

        return F.Disp(ForAll(
            [
                Bound("f", functionType),
                Bound("g", functionType),
                Bound("z", complex),
                Bound("w", complex),
            ],
            Implies(BoundaryEstimate(complex, f, g, z, w), conclusion)));
    }

    private static Formula ContinuityFormula()
    {
        Formula real = Call("Real"), complex = Call("Complex");
        Formula f = F.Id("f"), g = F.Id("g"), z = F.Id("z"), w = F.Id("w");
        Formula t = F.Id("t"), s = F.Id("s"), u = F.Id("u");
        Formula functionType = Arrow(complex, complex);
        Formula homotopy = Lambda("u", complex, HomotopyValue(f, g, t, u));
        Formula logDerivative = Lambda("s", complex, Call("logDeriv", homotopy, s));
        Formula rectangleIntegral = Seq(
            Operatorname, Grp(F.Id("RectangleIntegral")), Apos);
        Formula parameterValue = Apply(rectangleIntegral, logDerivative, z, w);
        Formula conclusion = Call(
            "ContinuousOn",
            Lambda("t", real, parameterValue),
            Call("Icc", D(0), D(1)));

        return F.Disp(ForAll(
            [
                Bound("f", functionType),
                Bound("g", functionType),
                Bound("z", complex),
                Bound("w", complex),
            ],
            Implies(AnalyticPremises(complex, f, g, z, w), conclusion)));
    }

    private static Formula ZeroSetSpecification(
        Formula complex,
        Formula function,
        Formula zeros,
        Formula z,
        Formula w)
    {
        Formula s = F.Id("s");
        return ForAll(
            [Bound("s", complex)],
            Implies(
                Member(s, Rectangle(z, w)),
                Iff(Equal(Apply(function, s), D(0)), Member(s, zeros))));
    }

    private static Formula FiniteMultiplicitySum(
        Formula function,
        Formula zeros)
    {
        Formula rho = F.Id("rho");
        return Seq(
            Sum, Underscore, Grp(rho, Sp, InMacro, Sp, zeros), Sp,
            Call("analyticOrderNatAt", function, rho));
    }

    private static Formula ZeroCountFormula()
    {
        Formula complex = Call("Complex");
        Formula f = F.Id("f"), g = F.Id("g"), z = F.Id("z"), w = F.Id("w");
        Formula zf = F.Id("Zf"), zg = F.Id("Zg");
        Formula functionType = Arrow(complex, complex);
        Formula finset = Call("Finset", complex);
        Formula rectangle = Rectangle(z, w);
        Formula zeroSetPremises = All(
            ZeroSetSpecification(complex, f, zf, z, w),
            Subset(Call("toSet", zf), rectangle),
            ZeroSetSpecification(complex, g, zg, z, w),
            Subset(Call("toSet", zg), rectangle));
        Formula conclusion = Equal(
            FiniteMultiplicitySum(f, zf),
            FiniteMultiplicitySum(g, zg));

        return F.Disp(ForAll(
            [
                Bound("f", functionType),
                Bound("g", functionType),
                Bound("z", complex),
                Bound("w", complex),
                Bound("Zf", finset),
                Bound("Zg", finset),
            ],
            Implies(
                All(
                    AnalyticPremises(complex, f, g, z, w),
                    zeroSetPremises),
                conclusion)));
    }
}
