using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ObserverModeCriticalKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaGamma/ObserverModeCriticalKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric completed-zeta digamma difference has its cosine kernel and is "
            + "strictly positive on the zero-frequency axis for every nonzero shift.",
        H("Observer-Mode Critical Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-mode-critical-kernel"),
            DeclarationHandle.Create(Prefix + "observer_mode_critical_kernel"),
            H("The polarized digamma kernel and its axis positivity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The multiplier a is displayed on its concrete real digamma carrier. "
                        + "The public premise is its positive-scale Levy representation, "
                        + "including integrability for every real frequency.")),
                Paragraph(Text(
                    "Polarization gives the cosine-modulated symmetric-difference kernel. "
                        + "At zero frequency, the imported Archimedean jump density and the "
                        + "nonzero shift produce a strictly positive integral."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula t = F.Id("t"), tau = F.Id("tau");
        Formula u = F.Id("u"), x = F.Id("x"), a = F.Id("a");
        Formula positiveReals = Call("Ioi", D(0));
        Formula volume = Call("volume");

        Formula DigammaMultiplier(Formula frequency) => Sub(
            Call("re", Call("digamma", Add(
                new Formula.Fraction(D(1), D(4)),
                Mul(Call("I"), new Formula.Fraction(frequency, D(2)))))),
            Call("log", Call("pi")));
        Formula A(Formula frequency) => Apply(a, frequency);
        Formula Integrand(Formula frequency) => Mul(
            Call("archimedeanJumpDensity", x),
            Sub(D(1), Call("cos", Mul(frequency, x))));
        Formula KernelIntegrand() => Mul(
            Mul(
                Call("archimedeanJumpDensity", x),
                Call("cos", Mul(t, x))),
            Sub(D(1), Call("cos", Mul(tau, x))));
        Formula SetIntegral(Formula integrand) =>
            Call("setIntegral", x, real, positiveReals, integrand, volume);

        Formula levyPremise = ForAll(
            [Bound("u", real)],
            And(
                Call("IntegrableOn", Lambda(x, real, Integrand(u)), positiveReals, volume),
                Equal(
                    Sub(A(u), A(D(0))),
                    Mul(D(2), SetIntegral(Integrand(u))))));
        Formula criticalKernel = Equal(
            SymmetricDifference(a, t, tau),
            Mul(D(2), SetIntegral(KernelIntegrand())));
        Formula axisPositivity = Implies(
            NotEqual(tau, D(0)),
            Less(D(0), SymmetricDifference(a, D(0), tau)));
        Formula letMultiplier = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            a, Colon, Sp, Arrow(real, real), Sp, Eq, Sp,
            Lambda(u, real, DigammaMultiplier(u)), Comma, Sp);

        return F.Disp(ForAll(
            [Bound("t", real), Bound("tau", real)],
            Seq(
                letMultiplier,
                Implies(levyPremise, And(criticalKernel, axisPositivity)))));
    }

    private static Formula SymmetricDifference(
        Formula function,
        Formula center,
        Formula shift) => Sub(
            Mul(
                new Formula.Fraction(D(1), D(2)),
                Add(
                    Apply(function, Add(center, shift)),
                    Apply(function, Sub(center, shift)))),
            Apply(function, center));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Lambda(Formula name, Formula domain, Formula body) =>
        Seq(name, Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
