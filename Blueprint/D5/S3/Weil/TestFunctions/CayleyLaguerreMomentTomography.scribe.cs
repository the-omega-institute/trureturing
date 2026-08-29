using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class CayleyLaguerreMomentTomographyDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scaled Laguerre kernels recover even Cayley moments and control finite windows.",
        H("Cayley-Laguerre Moment Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayley-laguerre-identity"),
                DeclarationHandle.Create(Handle + "cayley_laguerre_identity"),
                H("Cayley-Laguerre identity"),
                StatementSource.FromAuthor(CayleyIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive scale and positive natural order, the all-pass Cayley "
                        + "power is one minus the negative-sign Fourier transform of the "
                        + "causal scaled Laguerre kernel. The kernel is constructed from the "
                        + "repository's canonical generalized Laguerre finite sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laguerre-moment-tomography"),
                DeclarationHandle.Create(Handle + "laguerre_moment_tomography"),
                H("Laguerre moment tomography"),
                StatementSource.FromAuthor(TomographyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let rho be a finite even positive measure on the real line. Both source "
                        + "equalities are public: first in named kernel form and then with the "
                        + "factor 2a and the generalized Laguerre polynomial displayed. "
                        + "Evenness identifies the negative-sign Fourier integral with the "
                        + "positive-sign resolvent correlation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-window-moment-tube"),
                DeclarationHandle.Create(Handle + "finite_window_moment_tube"),
                H("Finite-window moment tube"),
                StatementSource.FromAuthor(WindowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonnegative window length, subtracting the truncated estimator "
                        + "leaves exactly the kernel-correlation tail. The norm of every "
                        + "correlation value is bounded by the total spectral mass, giving the "
                        + "displayed mass-times-tail estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moment-affine-budget-law"),
                DeclarationHandle.Create(Handle + "moment_affine_budget_law"),
                H("Moment affine budget law"),
                StatementSource.FromAuthor(AffineFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The particular correlation H0 is real-valued and continuous on the finite "
                        + "window, as supplied by the local second-order equation in the source. "
                        + "The estimator is constructed from H0 plus R cosh(at). The displayed "
                        + "definitions of A and B are literal finite-window integrals, and "
                        + "integral linearity proves the affine equality."))),
                DescribeRole.Theorem))));

    private static Formula CayleyIdentityFormula()
    {
        Formula natural = Call("Natural");
        Formula real = Call("Real");
        Formula n = F.Id("n"), a = F.Id("a"), xi = F.Id("xi"), t = F.Id("t");
        Formula assumptions = All(
            LessEqual(D(1), n),
            Less(D(0), a));
        Formula kernelTransform = Integral(
            t,
            real,
            Mul(
                Call("complex", Call("laguerreKernel", n, a, t)),
                Call("exp", Neg(Mul(Mul(Call("I"), xi), t)))),
            Call("restrict", Call("volume"), Call("Ioi", D(0))));
        Formula conclusion = Equal(
            Pow(Call("cayleyCharacter", a, xi), n),
            Sub(D(1), kernelTransform));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", natural), Bound("a", real), Bound("xi", real)],
            Implies(assumptions, conclusion)));
    }

    private static Formula TomographyFormula()
    {
        Formula natural = Call("Natural"), real = Call("Real"), complex = Call("Complex");
        Formula rho = F.Id("rho"), n = F.Id("n"), a = F.Id("a"), t = F.Id("t");
        Formula measure = Call("Measure", real);
        Formula assumptions = All(
            Call("IsFiniteMeasure", rho),
            Equal(Call("map", Lambda(F.Id("xi"), Neg(F.Id("xi"))), rho), rho),
            LessEqual(D(1), n),
            Less(D(0), a));
        Formula correlation = Call("resolventCorrelation", rho, t);
        Formula kernelIntegral = Integral(
            t,
            real,
            Mul(Call("complex", Call("laguerreKernel", n, a, t)), correlation),
            Call("restrict", Call("volume"), Call("Ioi", D(0))));
        Formula explicitIntegral = Integral(
            t,
            real,
            Mul(
                Call("complex", Mul(
                    Call("exp", Neg(Mul(a, t))),
                    Call("laguerreOne", Sub(n, D(1)), Mul(Mul(D(2), a), t)))),
                correlation),
            Call("restrict", Call("volume"), Call("Ioi", D(0))));
        Formula moment = Call("cayleyMoment", rho, n, a);
        Formula mass = Call("complex", Call("spectralMass", rho));
        Formula conclusion = And(
            Equal(moment, Sub(mass, kernelIntegral)),
            Equal(moment, Sub(mass, Mul(Call("complex", Mul(D(2), a)), explicitIntegral))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", measure), Bound("n", natural), Bound("a", real)],
            Implies(assumptions, conclusion)));
    }

    private static Formula WindowFormula()
    {
        Formula natural = Call("Natural"), real = Call("Real");
        Formula rho = F.Id("rho"), n = F.Id("n"), a = F.Id("a"), L = F.Id("L");
        Formula assumptions = All(
            Call("IsFiniteMeasure", rho),
            Equal(Call("map", Lambda(F.Id("xi"), Neg(F.Id("xi"))), rho), rho),
            LessEqual(D(1), n),
            Less(D(0), a),
            LessEqual(D(0), L));
        Formula difference = Sub(
            Call("cayleyMoment", rho, n, a),
            Call("windowMoment", rho, n, a, L));
        Formula bound = Mul(
            Call("spectralMass", rho),
            Call("laguerreTail", n, a, L));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", Call("Measure", real)), Bound("n", natural),
             Bound("a", real), Bound("L", real)],
            Implies(assumptions, LessEqual(Call("norm", difference), bound))));
    }

    private static Formula AffineFormula()
    {
        Formula natural = Call("Natural"), real = Call("Real");
        Formula n = F.Id("n"), a = F.Id("a"), L = F.Id("L");
        Formula H0 = F.Id("H0"), R = F.Id("R"), t = F.Id("t");
        Formula A = F.Id("A"), B = F.Id("B");
        Formula window = Call("Ioc", D(0), Mul(D(2), L));
        Formula compactWindow = Call("Icc", D(0), Mul(D(2), L));
        Formula particularIntegral = Integral(
            t,
            real,
            Mul(Call("laguerreKernel", n, a, t), Apply(H0, t)),
            Call("restrict", Call("volume"), window));
        Formula homogeneousIntegral = Integral(
            t,
            real,
            Mul(
                Call("laguerreKernel", n, a, t),
                Call("cosh", Mul(a, t))),
            Call("restrict", Call("volume"), window));
        Formula definitions = Seq(
            F.Id("let"), Sp, Typed(A, real), Sp, Eq, Sp, Neg(particularIntegral), Semi, Sp,
            F.Id("let"), Sp, Typed(B, real), Sp, Eq, Sp,
            Sub(D(1), homogeneousIntegral), Semi, Sp,
            Equal(
                Call("budgetWindowMoment", n, a, L, H0, R),
                Add(A, Mul(B, R))));
        Formula assumptions = All(
            Less(D(0), a),
            Call("ContinuousOn", H0, compactWindow));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", natural), Bound("a", real), Bound("L", real),
             Bound("H0", Arrow(real, real)), Bound("R", real)],
            Implies(assumptions, definitions)));
    }

    private static Formula Integral(
        Formula variable, Formula domain, Formula integrand, Formula measure) =>
        Call("integral", variable, domain, integrand, measure);

    private static Formula Lambda(Formula variable, Formula body) =>
        Call("lambda", variable, body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        Call("pow", value, exponent);

    private static Formula Neg(Formula value) => Call("neg", value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }
}
