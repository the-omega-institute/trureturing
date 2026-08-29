using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class LaguerreLiBridgeDocument : IScribeDocumentDefinition
{
    private const string Handle = "D5/S3/Weil/TestFunctions/LaguerreLiBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The natural half-scale Cayley moments give the Laguerre formula for Li curvature.",
        H("Laguerre-Li Bridge"),
        Blocks(Describe.Lean(
            DescribeId.Create("laguerre-li-bridge"),
            DeclarationHandle.Create(Handle + "laguerre_li_bridge"),
            H("Laguerre-Li bridge"),
            StatementSource.FromAuthor(BridgeFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For a finite even real-line spectral measure, assume the natural half-scale "
                    + "Cayley moments are the discrete curvatures of the supplied Li sequence "
                    + "and the total mass is twice its first coefficient. Specializing the "
                    + "canonical Cayley-Laguerre tomography identity gives the displayed "
                    + "real resolvent-correlation integral."))),
            DescribeRole.Theorem))));

    private static Formula BridgeFormula()
    {
        Formula natural = Call("Natural"), real = Call("Real");
        Formula rho = F.Id("rho"), coefficient = F.Id("liCoefficient");
        Formula n = F.Id("n"), k = F.Id("k"), t = F.Id("t");
        Formula measure = Call("Measure", real);
        Formula sequence = Arrow(natural, real);
        Formula half = Div(D(1), D(2));

        Formula Curvature(Formula index) => Add(
            Sub(
                Apply(coefficient, Add(index, D(1))),
                Mul(D(2), Apply(coefficient, index))),
            Apply(coefficient, Sub(index, D(1))));

        Formula momentIdentity = ForAll(
            [Bound("k", natural)],
            Implies(
                LessEqual(D(1), k),
                Equal(
                    Call("realPart", Call("cayleyMoment", rho, k, half)),
                    Curvature(k))));
        Formula assumptions = All(
            Call("IsFiniteMeasure", rho),
            Equal(Call("map", Lambda(F.Id("xi"), Neg(F.Id("xi"))), rho), rho),
            Equal(
                Call("spectralMass", rho),
                Mul(D(2), Apply(coefficient, D(1)))),
            momentIdentity);
        Formula laguerreIntegral = Integral(
            t,
            real,
            Mul(
                Mul(
                    Call("exp", Neg(Div(t, D(2)))),
                    Call("laguerreOne", Sub(n, D(1)), t)),
                Call("realPart", Call("resolventCorrelation", rho, t))),
            Call("restrict", Call("volume"), Call("Ioi", D(0))));
        Formula conclusion = ForAll(
            [Bound("n", natural)],
            Implies(
                LessEqual(D(1), n),
                Equal(
                    Curvature(n),
                    Sub(Mul(D(2), Apply(coefficient, D(1))), laguerreIntegral))));

        return Disp(ForAll(
            [Bound("rho", measure), Bound("liCoefficient", sequence)],
            Implies(assumptions, conclusion)));
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

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Neg(Formula value) => Call("neg", value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
