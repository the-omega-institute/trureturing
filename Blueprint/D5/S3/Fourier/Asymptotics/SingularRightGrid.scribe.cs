using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class SingularRightGridDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A singular right-grid sum approximates its integral uniformly with a square-root mesh error.",
        H("Singular Quadrature for Complex Sobolev Representatives"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-singular-right-grid"),
            DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/SingularRightGrid.result"),
            H("A uniform estimate including both endpoints"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                    Paragraph(Text(
                        "Let A be positive and let f be a complex-valued absolutely continuous "
                            + "function on the closed interval from zero to A, with square-integrable "
                            + "actual derivative. Set g(v) equal to the squared norm of f(v) minus the "
                            + "squared norm of f(0). For every positive mesh h and endpoint b satisfying "
                            + "h <= b <= A, sum g(((k:ℝ)+1)h)/((k:ℝ)+1) over "
                            + "k in range(Nat.floor(b/h)) and compare it with the improper integral of "
                            + "g(v)/v, interpreted as the limit of the integral from epsilon to b as "
                            + "epsilon decreases to zero. The absolute error is bounded "
                    + "by 14 times (1/sqrt(A) + sqrt(A)), times sqrt(h), times the integral of "
                    + "the squared norm of f plus the squared norm of its derivative.")),
                Paragraph(Text(
                    "The constant depends only on A. In particular it works simultaneously "
                    + "for every b in any fixed interval [A0,A] whenever 0 < h <= A0. "
                    + "The proof includes the singular first cell and the final partial cell "
                    + "created by the floor. Absolute continuity, rather than continuous "
                    + "differentiability, is the regularity assumption.")),
                Paragraph(Text(
                    "For a real absolutely continuous function vanishing at zero, the proof "
                    + "first obtains the error bound 7 sqrt(h) times the L2 norm of its "
                    + "derivative. The remaining full cells are controlled by the integrable "
                    + "derivative of g(v)/v away from zero. The Sobolev energy controls the "
                    + "derivative of the squared norm. This is a deterministic quadrature "
                    + "estimate; harmonic counterterms and stochastic spectral convergence "
                    + "are separate conclusions."))),
            DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(variable, Sp, Mapsto, Sp, body);

    private static Formula NormSquared(Formula value) =>
        new Formula.Power(new Formula.Norm(value), D(2));

    private static Formula FunctionValue(Formula f, Formula x) => Apply(f, x);

    private static Formula Derivative(Formula f, Formula x) => Call("deriv", f, x);

    private static Formula Integral(Formula lower, Formula upper, Formula integrand, Formula variable) =>
        Seq(Int, Underscore, Grp(lower), Caret, Grp(upper), Sp, integrand, Sp, F.Id("d"), variable);

    private static Formula H1Energy(Formula f, Formula A) =>
        Integral(
            D(0),
            A,
            Seq(
                Open,
                Add(
                    NormSquared(FunctionValue(f, F.Id("x"))),
                    NormSquared(Derivative(f, F.Id("x")))),
                Close),
            F.Id("x"));

    private static Formula TheoremFormula()
    {
        Formula A = F.Id("A");
        Formula f = F.Id("f");
        Formula h = F.Id("h");
        Formula b = F.Id("b");
        Formula x = F.Id("x");
        Formula k = F.Id("k");
        Formula reals = Reals();
        Formula complexes = Complexes();
        Formula fType = Arrow(reals, complexes);

        Formula kReal = Seq(Open, k, Colon, Sp, reals, Close);
        Formula kPlusOne = Add(kReal, D(1));
        Formula sample = Multiply(kPlusOne, h);
        Formula summand = Divide(
            Subtract(
                NormSquared(FunctionValue(f, sample)),
                NormSquared(FunctionValue(f, D(0)))),
            kPlusOne);
        Formula floor = new Formula.Floor(Divide(b, h));
        Formula sumIndex = Seq(k, Sp, InMacro, Sp, Call("range", floor));
        Formula sum = Seq(Sum, Underscore, Grp(sumIndex), Sp, summand);

        Formula integrand = Divide(
            Subtract(
                NormSquared(FunctionValue(f, x)),
                NormSquared(FunctionValue(f, D(0)))),
            x);
        Formula eps = Varepsilon;
        Formula improperIntegral = Seq(
            Lim,
            Underscore,
            Grp(Seq(eps, To, D(0), Plus)),
            Sp,
            Integral(eps, b, integrand, x));
        Formula error = new Formula.Absolute(Subtract(sum, improperIntegral));

        Formula derivativeEnergy = Call(
            "IntervalIntegrable",
            Lambda(x, NormSquared(Derivative(f, x))),
            F.Id("volume"),
            D(0),
            A);
        Formula regularity = And(
            Call("AbsolutelyContinuousOnInterval", f, D(0), A),
            derivativeEnergy);
        Formula hypotheses = And(
            Less(D(0), A),
            And(
                regularity,
                And(
                    Less(D(0), h),
                    And(Leq(h, b), Leq(b, A)))));

        Formula constant = Multiply(
            Multiply(
                D(1, 4),
                Add(
                    Divide(D(1), Seq(Sqrt, Grp(A))),
                    Seq(Sqrt, Grp(A)))),
            Multiply(Seq(Sqrt, Grp(h)), H1Energy(f, A)));

        return Disp(Seq(
            All(
                [
                    Bound("A", reals),
                    Bound("f", fType),
                    Bound("h", reals),
                    Bound("b", reals)
                ],
                Implies(hypotheses, Leq(error, constant))),
            Dot));
    }
}
