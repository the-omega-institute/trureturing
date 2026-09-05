using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Certified;

internal sealed class TrigEnvelopePhaseReductionDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reusable certified-numerics infrastructure for the L2b layer of the G-c "
            + "certificate: sharp trigonometric envelopes, exact golden floors, phase "
            + "reduction, and coordinatewise finite-sum bounds.",
        H("Certified Trigonometric Envelopes and Phase Reduction"),
        Blocks(
            Paragraph(Text(
                "This is the L2b infrastructure layer preregistered in addendum thirty-four. "
                    + "It proves no numerical assertion about the candidate zero, and it makes "
                    + "no claim about the Riemann hypothesis.")),
            Describe.Lean(
                DescribeId.Create("sharp-any-order-cosine-envelope"),
                DeclarationHandle.Create(Module + "abs_cos_sub_partial_le"),
                H("Sharp any-order cosine envelope"),
                StatementSource.FromAuthor(CosineEnvelopeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every order n and every real x with absolute value at most one, "
                        + "the cosine Taylor error is bounded by the absolute value of the "
                        + "next term. This is the sharp alternating-series remainder, obtained "
                        + "from coefficient antitonicity and Mathlib's alternating-series "
                        + "error theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-any-order-sine-envelope"),
                DeclarationHandle.Create(Module + "abs_sin_sub_partial_le"),
                H("Sharp any-order sine envelope"),
                StatementSource.FromAuthor(SineEnvelopeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The analogous bound holds at every order for sine. The proof first "
                        + "handles nonnegative x by the alternating series and then transports "
                        + "the result across the odd symmetry of sine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("certified-reduced-phase"),
                DeclarationHandle.Create(Module + "exists_reduced_phase"),
                H("An enclosed phase has a unit residual representative"),
                StatementSource.FromAuthor(ReducedPhaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If theta lies in the certified interval from a to b and the chosen "
                        + "integer multiple of two pi leaves the whole interval inside a unit "
                        + "residual window, then r = theta - 2 pi k has absolute value at most "
                        + "one. Integer periodicity gives exact cosine and sine identities. "
                        + "Rational endpoint certificates can discharge the interval premise "
                        + "using Mathlib's pinned decimal bounds for pi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-coordinate-interval-accumulation"),
                DeclarationHandle.Create(Module + "sum_re_le_of_bounds"),
                H("Real-coordinate interval accumulation"),
                StatementSource.FromAuthor(RealAccumulationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lower and upper bounds are accumulated term by term with "
                        + "Finset.sum_le_sum. No positivity assumption on the summands is "
                        + "needed, so mixed-sign certified sums are supported."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("imaginary-coordinate-interval-accumulation"),
                DeclarationHandle.Create(Module + "sum_im_le_of_bounds"),
                H("Imaginary-coordinate interval accumulation"),
                StatementSource.FromAuthor(ImaginaryAccumulationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same mixed-sign finite-sum enclosure is available independently in "
                        + "the imaginary coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-bounds-imply-complex-norm-bound"),
                DeclarationHandle.Create(Module + "norm_le_of_re_im_bounds"),
                H("Coordinate bounds imply an additive complex norm bound"),
                StatementSource.FromAuthor(NormBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This named companion binds Mathlib's complex norm inequality to the "
                        + "coordinate intervals. Its directed consumer is the L2c theorem "
                        + "g60_center_norm_lt."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-golden-floor-table-through-sixty"),
                DeclarationHandle.Create(Module + "o5Beta_floor_table"),
                H("The first sixty-one golden floors are exact"),
                StatementSource.FromAuthor(FloorTableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed table is exactly floor((v+1) phi) for every v from zero "
                        + "through sixty. Each of its sixty-one entries is proved from the "
                        + "rational enclosure 1.618033 < phi < 1.618034, itself derived from "
                        + "the defining square root of five."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-beta-affine-form-through-sixty"),
                DeclarationHandle.Create(Module + "o5Beta_eq_affine"),
                H("The golden exponent has its table-driven affine form"),
                StatementSource.FromAuthor(BetaAffineFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the certified range, the exact floor table converts the frozen "
                        + "golden exponent into an affine expression. The proof connects to "
                        + "the independently frozen closed form through floor plus fractional "
                        + "part, so the table definition is not a tautological carrier."))),
                DescribeRole.Theorem))));

    private static Formula CosineEnvelopeFormula() =>
        TrigEnvelopeFormula(Name("cos"), odd: false);

    private static Formula SineEnvelopeFormula() =>
        TrigEnvelopeFormula(Name("sin"), odd: true);

    private static Formula TrigEnvelopeFormula(FormulaIdentifier function, bool odd)
    {
        Formula x = F.Id("x"), n = F.Id("n"), k = F.Id("k");
        Formula exponent = odd
            ? Add(Multiply(Number(2), k), Number(1))
            : Multiply(Number(2), k);
        Formula remainderExponent = odd
            ? Add(Multiply(Number(2), n), Number(1))
            : Multiply(Number(2), n);
        Formula sign = Power(Parenthesize(Negate(Number(1))), k);
        Formula term = Fraction(
            Multiply(sign, Power(x, exponent)),
            Factorial(exponent));
        Formula partial = RangeSum(k, n, term);
        Formula error = Absolute(Subtract(Call(function, x), partial));
        Formula remainder = Fraction(
            Power(Absolute(x), remainderExponent),
            Factorial(remainderExponent));
        Formula conclusion = LessOrEqual(error, remainder);
        Formula domain = LessOrEqual(Absolute(x), Number(1));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", Reals()), Bound("n", Naturals())],
            Implies(domain, conclusion)));
    }

    private static Formula ReducedPhaseFormula()
    {
        Formula theta = F.Id("theta"), a = F.Id("a"), b = F.Id("b");
        Formula k = F.Id("k"), r = F.Id("r");
        Formula period = Multiply(k, Parenthesize(Multiply(Number(2), F.Pi)));
        Formula hypotheses = And(
            LessOrEqual(a, theta),
            And(
                LessOrEqual(theta, b),
                LessOrEqual(
                    Add(Absolute(Subtract(a, period)), Subtract(b, a)),
                    Number(1))));
        Formula conclusions = And(
            Equal(theta, Add(r, period)),
            And(
                LessOrEqual(Absolute(r), Number(1)),
                And(
                    Equal(Call(Name("cos"), theta), Call(Name("cos"), r)),
                    Equal(Call(Name("sin"), theta), Call(Name("sin"), r)))));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("r", Reals())],
            conclusions);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("theta", Reals()),
                Bound("a", Reals()),
                Bound("b", Reals()),
                Bound("k", Integers()),
            ],
            Implies(hypotheses, witness)));
    }

    private static Formula RealAccumulationFormula() =>
        AccumulationFormula(Name("Re"));

    private static Formula ImaginaryAccumulationFormula() =>
        AccumulationFormula(Name("Im"));

    private static Formula AccumulationFormula(FormulaIdentifier coordinate)
    {
        Formula indexType = F.Id("I"), i = F.Id("i"), s = F.Id("s");
        Formula z = F.Id("z"), lo = F.Id("lo"), hi = F.Id("hi");
        Formula zi = Apply(z, i);
        Formula coordinateZi = Call(coordinate, zi);
        Formula pointwise = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", s)],
            And(
                LessOrEqual(Apply(lo, i), coordinateZi),
                LessOrEqual(coordinateZi, Apply(hi, i))));
        Formula summedCoordinate = Call(coordinate, FiniteSum(i, s, zi));
        Formula conclusion = And(
            LessOrEqual(FiniteSum(i, s, Apply(lo, i)), summedCoordinate),
            LessOrEqual(summedCoordinate, FiniteSum(i, s, Apply(hi, i))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", F.Id("Type")),
                Bound("s", Call(Name("Finset"), indexType)),
                Bound("z", new Formula.TypeArrow(indexType, ComplexNumbers())),
                Bound("lo", new Formula.TypeArrow(indexType, Reals())),
                Bound("hi", new Formula.TypeArrow(indexType, Reals())),
            ],
            Implies(pointwise, conclusion)));
    }

    private static Formula NormBoundFormula()
    {
        Formula z = F.Id("z"), a = F.Id("a"), b = F.Id("b");
        Formula hypotheses = And(
            LessOrEqual(Absolute(Call(Name("Re"), z)), a),
            LessOrEqual(Absolute(Call(Name("Im"), z)), b));
        Formula conclusion = LessOrEqual(
            new Formula.Norm(z),
            Add(a, b));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", ComplexNumbers()), Bound("a", Reals()), Bound("b", Reals())],
            Implies(hypotheses, conclusion)));
    }

    private static Formula FloorTableFormula()
    {
        Formula v = F.Id("v");
        Formula floorValue = new Formula.Floor(
            Multiply(Add(v, Number(1)), F.Varphi));
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("v", Naturals())],
            Implies(
                LessOrEqual(v, Number(60)),
                Equal(floorValue, Call(Name("o5FloorTable"), v))));
        Formula table = F.Seq(
            F.Id("o5FloorTable"), F.Sp, F.Eq, F.Sp,
            F.Open,
            Number(1), F.Comma, F.Sp, Number(3), F.Comma, F.Sp, Number(4), F.Comma, F.Sp,
            Number(6), F.Comma, F.Sp, Number(8), F.Comma, F.Sp, Number(9), F.Comma, F.Sp,
            Number(11), F.Comma, F.Sp, Number(12), F.Comma, F.Sp, Number(14), F.Comma, F.Sp,
            Number(16), F.Comma, F.Sp, Number(17), F.Comma, F.Sp, Number(19), F.Comma, F.Sp,
            Number(21), F.Comma, F.Sp, Number(22), F.Comma, F.Sp, Number(24), F.Comma, F.Sp,
            Number(25), F.Comma, F.Sp, Number(27), F.Comma, F.Sp, Number(29), F.Comma, F.Sp,
            Number(30), F.Comma, F.Sp, Number(32), F.Comma, F.Sp, Number(33), F.Comma, F.Sp,
            Number(35), F.Comma, F.Sp, Number(37), F.Comma, F.Sp, Number(38), F.Comma, F.Sp,
            Number(40), F.Comma, F.Sp, Number(42), F.Comma, F.Sp, Number(43), F.Comma, F.Sp,
            Number(45), F.Comma, F.Sp, Number(46), F.Comma, F.Sp, Number(48), F.Comma, F.Sp,
            Number(50), F.Comma, F.Sp, Number(51), F.Comma, F.Sp, Number(53), F.Comma, F.Sp,
            Number(55), F.Comma, F.Sp, Number(56), F.Comma, F.Sp, Number(58), F.Comma, F.Sp,
            Number(59), F.Comma, F.Sp, Number(61), F.Comma, F.Sp, Number(63), F.Comma, F.Sp,
            Number(64), F.Comma, F.Sp, Number(66), F.Comma, F.Sp, Number(67), F.Comma, F.Sp,
            Number(69), F.Comma, F.Sp, Number(71), F.Comma, F.Sp, Number(72), F.Comma, F.Sp,
            Number(74), F.Comma, F.Sp, Number(76), F.Comma, F.Sp, Number(77), F.Comma, F.Sp,
            Number(79), F.Comma, F.Sp, Number(80), F.Comma, F.Sp, Number(82), F.Comma, F.Sp,
            Number(84), F.Comma, F.Sp, Number(85), F.Comma, F.Sp, Number(87), F.Comma, F.Sp,
            Number(88), F.Comma, F.Sp, Number(90), F.Comma, F.Sp, Number(92), F.Comma, F.Sp,
            Number(93), F.Comma, F.Sp, Number(95), F.Comma, F.Sp, Number(97), F.Comma, F.Sp,
            Number(98), F.Close);

        return Disp(new Formula.Aligned([table, theorem]));
    }

    private static Formula BetaAffineFormula()
    {
        Formula v = F.Id("v");
        Formula right = Add(
            Subtract(
                Subtract(Call(Name("o5FloorTable"), v), Number(1)),
                v),
            Multiply(v, F.Varphi));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("v", Naturals())],
            Implies(
                LessOrEqual(v, Number(60)),
                Equal(Call(Name("o5Beta"), v), right))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Number(long value) => new Formula.Number(value);

    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Integers() => F.Seq(F.Mathbb, F.Grp(F.Id("Z")));

    private static Formula ComplexNumbers() => F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula Parenthesize(Formula value) =>
        F.Seq(F.Open, value, F.Close);

    private static Formula Negate(Formula value) => new Formula.Negate(value);

    private static Formula Absolute(Formula value) => new Formula.Absolute(value);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Factorial(Formula value) =>
        F.Seq(Parenthesize(value), F.Bang);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static FormulaIdentifier Name(string name) =>
        FormulaIdentifier.Create(name);

    private static Formula Call(FormulaIdentifier name, params Formula[] arguments) =>
        new Formula.FunctionCall(name, [.. arguments]);

    private static Formula RangeSum(Formula index, Formula bound, Formula body) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(Number(0), F.Sp, F.Leq, F.Sp, index, F.Sp, F.Lt, F.Sp, bound),
            F.Sp, body);

    private static Formula FiniteSum(Formula index, Formula set, Formula body) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(index, F.Sp, F.InMacro, F.Sp, set),
            F.Sp, body);
}
