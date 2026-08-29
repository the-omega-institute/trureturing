using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaAnalytic;

internal sealed class RiemannPoissonDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shifted-xi phase density is the Poisson smoothing of its zero-counting measure.",
        H("Riemann Poisson Density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("riemann-poisson-density"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaAnalytic/RiemannPoissonDensity.riemann_poisson_density"),
                H("Riemann Poisson-density theorem"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The phase density is constructed from the logarithmic derivative of "
                            + "the canonical entire xi reading. The counting measure is built "
                            + "independently from a duplicate-free exhaustive zero enumeration.")),
                    Paragraph(Text(
                        "Under the critical-line hypothesis and the preceding logarithmic-"
                            + "derivative zero expansion, integration against the weighted sum "
                            + "of Dirac masses is exactly the sum of translated Poisson kernels."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula zeroData = Call("ZeroData");
        Formula z = F.Id("Z");
        Formula omega = F.Id("omega");
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula positiveScale = LessThan(D(0), omega);
        Formula rh = Call("RiemannHypothesis");
        Formula phaseAt = Call("phaseDensity", omega, x);
        Formula zeroOrdinate = Call("im", Call("zero", z, n));
        Formula summand = Multiply(
            Call("multiplicity", z, n),
            Call("poissonKernel", omega, Subtract(x, zeroOrdinate)));
        Formula zeroSum = Seq(
            Sum, Underscore, Grp(n, InMacro, naturals), Sp, summand);
        Formula phaseExpansion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", reals)],
            Implies(positiveScale, Implies(rh, Equal(phaseAt, zeroSum))));
        Formula assumptions = And(
            positiveScale,
            And(rh, phaseExpansion));
        Formula conclusion = Equal(
            Lambda(x, phaseAt),
            Lambda(x, Call(
                "poissonSmooth",
                omega,
                Call("zeroCountingMeasure", z),
                x)));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("Z", zeroData), Bound("omega", reals)],
            Implies(assumptions, conclusion));
    }
}
