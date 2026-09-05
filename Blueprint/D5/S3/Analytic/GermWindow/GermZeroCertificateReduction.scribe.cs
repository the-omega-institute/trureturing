using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GermWindow;

internal sealed class GermZeroCertificateReductionDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first layer of the golden G-c certificate turns three finite center-jet "
            + "inequalities into a prime-two local-factor zero inside the candidate window.",
        H("Golden Germ Zero Certificate Reduction"),
        Blocks(
            Entry(
                "candidate-center",
                "c",
                CenterFormula(),
                "Candidate center",
                "The complex center is the frozen numerical candidate used by the G-c certificate.",
                DescribeRole.Definition),
            Entry(
                "candidate-half-width",
                "h",
                HalfWidthFormula(),
                "Candidate half-width",
                "The half-width is five times ten to the minus ninth.",
                DescribeRole.Definition),
            Entry(
                "candidate-square",
                "Q",
                SquareFormula(),
                "Candidate square",
                "The axis-parallel square has center c and coordinate half-width h.",
                DescribeRole.Definition),
            Entry(
                "finite-local-truncation",
                "g",
                TruncationDefinitionFormula(),
                "Finite local truncation",
                "The function g(V,s) is the first V+1 terms of the p = 2 golden local factor.",
                DescribeRole.Definition),
            Entry(
                "candidate-square-inside-ball",
                "Q_subset_ball",
                SquareSubsetBallFormula(),
                "The candidate square lies in the target ball",
                "Coordinate control puts every point of Q strictly within distance 10^{-8} of c.",
                DescribeRole.Theorem),
            Entry(
                "candidate-square-positive-real-part",
                "Q_subset_re_pos",
                SquarePositiveFormula(),
                "The candidate square stays in the analytic half-plane",
                "Every point of Q has positive real part, so the frozen local analyticity theorem applies.",
                DescribeRole.Theorem),
            Entry(
                "candidate-center-golden-window",
                "c_in_golden_window",
                CenterWindowFormula(),
                "The center lies in the golden window",
                "The real coordinate of c lies strictly between the two displayed golden thresholds.",
                DescribeRole.Theorem),
            Entry(
                "candidate-center-in-square",
                "c_mem_Q",
                CenterInSquareFormula(),
                "The square contains its center",
                "The candidate square is inhabited by c.",
                DescribeRole.Theorem),
            Entry(
                "local-factor-truncation-identity",
                "germLocalFactor_eq_trunc_add_tail",
                TruncationIdentityFormula(),
                "The local factor splits into a finite head and shifted tail",
                "Absolute summability on the positive half-plane justifies the exact head-tail identity.",
                DescribeRole.Theorem),
            Entry(
                "explicit-geometric-tail-bound",
                "germLocalFactor_two_tail_le",
                TailBoundFormula(),
                "The prime-two local tail obeys an explicit geometric bound",
                "The frozen lower growth bound for o5Beta majorizes the shifted tail by a geometric series with the displayed exponent and denominator.",
                DescribeRole.Theorem),
            Entry(
                "candidate-square-tail-v60",
                "germLocalFactor_two_tail_Q_V60",
                TailV60Formula(),
                "The 61-term tail is below 5.8 times 10 to the minus ten",
                "Explicit logarithm and exponential inequalities specialize the geometric estimate uniformly on Q.",
                DescribeRole.Theorem),
            Entry(
                "rouche-existence-wrapper",
                "rouche_exists_zero_rectangle_of_unique_simple",
                RoucheWrapperFormula(),
                "A unique simple comparison zero transfers existence",
                "The rectangle Rouché theorem is another driver's frozen node, bound here by the name rectangle_zero_count_eq_of_norm_sub_lt; equal multiplicity counts force the target zero set to be nonempty.",
                DescribeRole.Theorem),
            Entry(
                "truncation-taylor-remainder",
                "truncation_taylor_remainder_of_curv",
                TaylorRemainderFormula(),
                "Curvature controls the truncation remainder",
                "A uniform second-derivative bound on Q gives the displayed affine Taylor remainder bound for the 61-term truncation.",
                DescribeRole.Theorem),
            Entry(
                "germ-zero-from-center-jet",
                "germ_zero_of_center_jet",
                CenterJetReductionFormula(),
                "Three center-jet inequalities imply a nearby local-factor zero",
                "This is the first layer of the G-c certificate in 增订十/三十三: it reduces the candidate zero of the p = 2 golden local factor to three finite numerical inequalities about the 61-term truncation at the center. The convention is β(1) = φ², correcting the panel brief. This theorem does not claim that the three jet inequalities hold; proving them is layer 2, so this module makes no unconditional claim that a zero exists yet. It makes no claim about RH.",
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaAnalytic/RoucheZeroCount")),
        ]));

    private static DocumentBlock.Describe Entry(
        string id,
        string declaration,
        Formula statement,
        string title,
        string prose,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula CenterFormula() =>
        Disp(Equal(
            F.Id("c"),
            F.Seq(
                F.Langle,
                Fraction(F.D(2, 3, 8, 1, 5, 3, 2, 9, 9, 4, 6, 2, 1, 1, 9, 0, 8), Pow10(17)),
                F.Comma,
                F.Sp,
                Fraction(F.D(5, 2, 5, 6, 7, 1, 2, 2, 9, 2, 9, 0, 1, 9, 2, 6), Pow10(15)),
                F.Rangle)));

    private static Formula HalfWidthFormula() =>
        Disp(Equal(F.Id("h"), Fraction(F.D(1), Multiply(F.D(2), Pow10(8)))));

    private static Formula SquareFormula() =>
        Disp(Equal(
            F.Id("Q"),
            Call(
                "Rectangle",
                Subtract(Subtract(F.Id("c"), F.Id("h")), Multiply(F.Id("h"), F.Id("i"))),
                Add(Add(F.Id("c"), F.Id("h")), Multiply(F.Id("h"), F.Id("i"))))));

    private static Formula TruncationDefinitionFormula()
    {
        Formula v = F.Id("v");
        Formula V = F.Id("V");
        Formula s = F.Id("s");
        return Disp(Equal(Call("g", V, s), FiniteTruncation(V, s, v)));
    }

    private static Formula SquareSubsetBallFormula() =>
        Disp(Subset(
            F.Id("Q"),
            Call("ball", F.Id("c"), Fraction(F.D(1), Pow10(8)))));

    private static Formula SquarePositiveFormula()
    {
        Formula s = F.Id("s");
        return Disp(Subset(
            F.Id("Q"),
            new Formula.SetBuilder(
                Less(F.D(0), RealPart(s)),
                s,
                ComplexNumbers())));
    }

    private static Formula CenterWindowFormula() =>
        Disp(And(
            Less(
                Fraction(F.D(1), Multiply(F.D(2), Power(F.Varphi, F.D(3)))),
                RealPart(F.Id("c"))),
            Less(
                RealPart(F.Id("c")),
                Fraction(F.D(1), Power(F.Varphi, F.D(2))))));

    private static Formula CenterInSquareFormula() =>
        Disp(Member(F.Id("c"), F.Id("Q")));

    private static Formula TruncationIdentityFormula()
    {
        Formula s = F.Id("s");
        Formula N = F.Id("N");
        Formula v = F.Id("v");
        Formula k = F.Id("k");
        Formula finiteHead = F.Seq(
            F.Sum,
            F.Underscore,
            F.Grp(F.Seq(v, F.Eq, F.D(0))),
            F.Caret,
            F.Grp(F.Seq(N, F.Minus, F.D(1))),
            LocalMode(s, v));
        Formula shiftedTail = F.Seq(
            F.Sum,
            F.Underscore,
            F.Grp(F.Seq(k, F.Eq, F.D(0))),
            F.Caret,
            F.Grp(F.Infty),
            LocalMode(s, Add(k, N)));
        Formula conclusion = Equal(
            LocalFactor(s),
            Add(finiteHead, shiftedTail));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers()), Bound("N", NaturalNumbers())],
            Implies(Less(F.D(0), RealPart(s)), conclusion)));
    }

    private static Formula TailBoundFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula s = F.Id("s");
        Formula V = F.Id("V");
        Formula v = F.Id("v");
        Formula Vplus = Add(V, F.D(1));
        Formula exponent = Negate(Multiply(
            sigma,
            Subtract(
                Add(
                    Multiply(SqrtFive(), Vplus),
                    Fraction(F.D(1), F.Varphi)),
                F.D(1))));
        Formula ratioExponent = Negate(Multiply(sigma, SqrtFive()));
        Formula right = Fraction(
            Power(F.Seq(F.D(2)), exponent),
            Subtract(F.D(1), Power(F.Seq(F.D(2)), ratioExponent)));
        Formula left = LessOrEqual(
            new Formula.Norm(Subtract(LocalFactor(s), FiniteTruncation(V, s, v))),
            right);
        Formula hypotheses = And(
            Less(F.D(0), sigma),
            LessOrEqual(sigma, RealPart(s)));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("sigma", RealNumbers()),
                Bound("s", ComplexNumbers()),
                Bound("V", NaturalNumbers()),
            ],
            Implies(hypotheses, left)));
    }

    private static Formula TailV60Formula()
    {
        Formula s = F.Id("s");
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(
                Member(s, F.Id("Q")),
                Less(
                    new Formula.Norm(Subtract(LocalFactor(s), Call("g", F.D(6, 0), s))),
                    Fraction(F.D(5, 8), Pow10(11))))));
    }

    private static Formula RoucheWrapperFormula()
    {
        Formula f = F.Id("f");
        Formula a = F.Id("a");
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula rectangle = Call("Rectangle", z, w);
        Formula boundary = Call("RectangleBorder", z, w);
        Formula boundaryGap = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(
                Member(s, boundary),
                Less(
                    new Formula.Norm(Subtract(Apply(f, s), Apply(a, s))),
                    new Formula.Norm(Apply(a, s)))));
        Formula uniqueZero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(
                Member(s, rectangle),
                Iff(Equal(Apply(a, s), F.D(0)), Equal(s, r))));
        Formula hypotheses = AndAll(
            Less(RealPart(z), RealPart(w)),
            Less(ImagPart(z), ImagPart(w)),
            Call("AnalyticOnNhd", ComplexNumbers(), f, rectangle),
            Call("AnalyticOnNhd", ComplexNumbers(), a, rectangle),
            boundaryGap,
            Member(r, rectangle),
            uniqueZero,
            Equal(Call("analyticOrderNatAt", a, r), F.D(1)));
        Formula exists = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("s", ComplexNumbers())],
            And(Member(s, rectangle), Equal(Apply(f, s), F.D(0))));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("f", new Formula.TypeArrow(ComplexNumbers(), ComplexNumbers())),
                Bound("a", new Formula.TypeArrow(ComplexNumbers(), ComplexNumbers())),
                Bound("z", ComplexNumbers()),
                Bound("w", ComplexNumbers()),
                Bound("r", ComplexNumbers()),
            ],
            Implies(hypotheses, exists)));
    }

    private static Formula TaylorRemainderFormula()
    {
        Formula s = F.Id("s");
        Formula g60s = Call("g", F.D(6, 0), s);
        Formula g60c = Call("g", F.D(6, 0), F.Id("c"));
        Formula derivative = Call("deriv", Call("g", F.D(6, 0)), F.Id("c"));
        Formula affine = Add(
            g60c,
            Multiply(derivative, Subtract(s, F.Id("c"))));
        Formula curvature = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(
                Member(s, F.Id("Q")),
                LessOrEqual(
                    new Formula.Norm(Call(
                        "deriv",
                        Call("deriv", Call("g", F.D(6, 0))),
                        s)),
                    F.D(4, 0, 0))));
        Formula remainder = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(
                Member(s, F.Id("Q")),
                LessOrEqual(
                    new Formula.Norm(Subtract(g60s, affine)),
                    Fraction(F.D(4), Pow10(14)))));
        return Disp(Implies(curvature, remainder));
    }

    private static Formula CenterJetReductionFormula()
    {
        Formula c = F.Id("c");
        Formula g60c = Call("g", F.D(6, 0), c);
        Formula derivative = Call("deriv", Call("g", F.D(6, 0)), c);
        Formula s = F.Id("s");
        Formula z = F.Id("z");
        Formula valueBound = Less(
            new Formula.Norm(g60c),
            Fraction(F.D(4), Pow10(10)));
        Formula derivativeBound = Less(
            Fraction(F.D(1, 8, 7), F.D(1, 0, 0)),
            RealPart(derivative));
        Formula curvatureBound = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(
                Member(s, F.Id("Q")),
                LessOrEqual(
                    new Formula.Norm(Call(
                        "deriv",
                        Call("deriv", Call("g", F.D(6, 0))),
                        s)),
                    F.D(4, 0, 0))));
        Formula zero = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("z", ComplexNumbers())],
            And(
                Member(z, Call("ball", c, Fraction(F.D(1), Pow10(8)))),
                Equal(LocalFactor(z), F.D(0))));
        return Disp(Implies(
            AndAll(valueBound, derivativeBound, curvatureBound),
            zero));
    }

    private static Formula FiniteTruncation(Formula V, Formula s, Formula v) =>
        F.Seq(
            F.Sum,
            F.Underscore,
            F.Grp(F.Seq(v, F.Eq, F.D(0))),
            F.Caret,
            F.Grp(V),
            LocalMode(s, v));

    private static Formula LocalMode(Formula s, Formula index) =>
        Power(
            F.Seq(F.D(2)),
            Negate(Multiply(s, Call("o5Beta", index))));

    private static Formula LocalFactor(Formula s) =>
        Call("germLocalFactor", s, F.D(2));

    private static Formula Pow10(byte exponent) =>
        Power(
            F.Seq(F.D(1, 0)),
            exponent switch
            {
                8 => F.D(8),
                10 => F.D(1, 0),
                11 => F.D(1, 1),
                14 => F.D(1, 4),
                15 => F.D(1, 5),
                17 => F.D(1, 7),
                _ => throw new ArgumentOutOfRangeException(nameof(exponent)),
            });

    private static Formula SqrtFive() =>
        F.Seq(F.Sqrt, F.Grp(F.D(5)));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Negate(Formula value) =>
        F.Seq(F.Minus, value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Subset(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula AndAll(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (var index = formulas.Length - 2; index >= 0; index--)
        {
            result = And(formulas[index], result);
        }

        return result;
    }

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Grp(value));

    private static Formula ImagPart(Formula value) =>
        Call("Im", value);

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));
}
