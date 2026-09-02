using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class LocalFactorZeroDivisorDocument
    : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized golden germ correction product has exactly the union of its local "
            + "zero sets, while each local factor is analytic on the positive half-plane "
            + "and a strict boundary norm gap gives a zero certificate.",
        H("Golden Germ Local-Factor Zero Divisor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("g3-local-factor-zero-divisor"),
                DeclarationHandle.Create(
                    Module + "G3_eq_zero_iff_exists_local_factor_zero"),
                H("The normalized product vanishes exactly at a local-factor zero"),
                StatementSource.FromAuthor(G3ZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The normalized factor is the literal correction factor in the "
                            + "frozen second-order factorization. Its two elementary "
                            + "multipliers are nonzero on the stated half-plane, and the "
                            + "frozen summable deviation makes the infinite product "
                            + "nonzero whenever every local factor is nonzero.")),
                    Paragraph(Text(
                        "This equivalence does not assert that any local factor vanishes. "
                            + "The numerical evidence for prime-two zeros in the target "
                            + "window remains recorded in the theory volume."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-factor-analytic-positive-half-plane"),
                DeclarationHandle.Create(
                    Module + "germLocalFactor_analyticOnNhd_pos"),
                H("Every prime-local factor is analytic when the real part is positive"),
                StatementSource.FromAuthor(LocalAnalyticFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The local series is normally summable on every smaller positive "
                            + "half-plane. Pinned Mathlib's locally uniform series theorem "
                            + "therefore supplies complex differentiability and analyticity.")),
                    Paragraph(Text(
                        "Analyticity does not assert a local-factor zero. The numerical "
                            + "prime-two evidence remains in the theory volume."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boundary-minimum-modulus-zero-criterion"),
                DeclarationHandle.Create(
                    Module + "exists_zero_in_ball_of_boundary_norm_gt_center"),
                H("A strict boundary norm gap forces an interior zero"),
                StatementSource.FromAuthor(BoundaryZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the function had no zero in the closed ball, its reciprocal "
                            + "would be analytic there. The maximum-modulus theorem for the "
                            + "reciprocal would then contradict the strict boundary gap.")),
                    Paragraph(Text(
                        "The criterion does not establish the numerical gap for a golden "
                            + "local factor and therefore asserts no local-factor zero."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization")),
        ]));

    private static Formula G3ZeroFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula primes = Call("Primes", NaturalNumbers());
        Formula threshold = Fraction(F.D(1), Power(F.Varphi, F.D(4)));
        Formula hypothesis = LessThan(threshold, RealPart(s));
        Formula normalized = NormalizedFactor(s, p);
        Formula productZero = Equal(PrimeProduct(normalized), F.D(0));
        Formula localZero = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("p", primes)],
            Equal(LocalFactor(s, p), F.D(0)));
        Formula conclusion = new Formula.Logic(
            productZero, FormulaLogicOperator.Iff, localZero);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", ComplexNumbers())],
            Implies(hypothesis, conclusion)));
    }

    private static Formula LocalAnalyticFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula complex = ComplexNumbers();
        Formula positiveHalfPlane = new Formula.SetBuilder(
            LessThan(F.D(0), RealPart(s)), s, complex);
        Formula analytic = Call(
            "AnalyticOnNhd",
            complex,
            Lambda(s, complex, LocalFactor(s, p)),
            positiveHalfPlane);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", NaturalNumbers())],
            Implies(Call("Prime", p), analytic)));
    }

    private static Formula BoundaryZeroFormula()
    {
        Formula f = F.Id("f");
        Formula c = F.Id("c");
        Formula r = F.Id("r");
        Formula z = F.Id("z");
        Formula complex = ComplexNumbers();
        Formula real = RealNumbers();
        Formula functionType = new Formula.TypeArrow(complex, complex);
        Formula closedBall = Call("closedBall", c, r);
        Formula sphere = Call("sphere", c, r);
        Formula ball = Call("ball", c, r);
        Formula analytic = Call("AnalyticOnNhd", complex, f, closedBall);
        Formula boundaryGap = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("z", complex)],
            Implies(
                Member(z, sphere),
                LessThan(
                    new Formula.Norm(Apply(f, c)),
                    new Formula.Norm(Apply(f, z)))));
        Formula hypotheses = And(
            LessThan(F.D(0), r),
            And(analytic, boundaryGap));
        Formula zero = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("z", complex)],
            And(Member(z, ball), Equal(Apply(f, z), F.D(0))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("f", functionType), Bound("c", complex), Bound("r", real)],
            Implies(hypotheses, zero)));
    }

    private static Formula NormalizedFactor(Formula s, Formula p)
    {
        Formula cubedMode = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, Power(F.Varphi, F.D(3))));
        Formula squaredMode = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, Power(F.Varphi, F.D(2))));
        Formula reciprocal = Power(
            F.Seq(F.Open, F.D(1), F.Sp, F.Plus, F.Sp, squaredMode, F.Close),
            F.Seq(F.Minus, F.D(1)));

        return F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, cubedMode, F.Close,
            F.Sp, F.Times, F.Sp, reciprocal,
            F.Sp, F.Times, F.Sp, LocalFactor(s, p));
    }

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            body);

    private static Formula LocalFactor(Formula s, Formula p) =>
        Call("germLocalFactor", s, p);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        F.Seq(F.Open, name, F.InMacro, F.Sp, type,
            F.Sp, F.Mapsto, F.Sp, body, F.Close);

    private static Formula Member(Formula value, Formula set) =>
        F.Seq(value, F.Sp, F.InMacro, F.Sp, set);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
