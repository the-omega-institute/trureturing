using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class GoldenObserverLightSpectralZetaDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Adelic/GoldenObserverLightSpectralZeta."
            + "golden_observer_light_spectral_zeta";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden massless observer tower has the scaled Riemann zeta shape spectrum.",
        H("Golden Observer-Light Spectral Zeta"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-observer-light-spectral-zeta"),
            DeclarationHandle.Create(Declaration),
            H("The golden light tower has Riemann zeta shape"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The level spacing is pi squared divided by twice log(phi), and the "
                        + "positive-mode energy is that spacing times n+1. The chiral and full "
                        + "spectral zeta functions are constructed as one-branch and two-branch "
                        + "totalized sums.")),
                Paragraph(Text(
                    "The displayed convergence premise is required by the Dirichlet-series "
                        + "representation. Factoring the positive scale gives the chiral identity, "
                        + "and the finite two-branch sum gives the factor of two.")),
                Paragraph(Text(
                    "Dividing each energy by the physical spacing yields n+1 at every mode. "
                        + "Consequently the normalized tower sum is exactly Riemann zeta, which "
                        + "states the dimensionless shape-spectrum clause directly."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula s = F.Id("s");
        Formula n = F.Id("n");
        Formula scale = F.Id("goldenLightScale");
        Formula negativeS = Seq(Minus, s);
        Formula scalePower = new Formula.Power(scale, Grp(negativeS));
        Formula zeta = Call("riemannZeta", s);
        Formula scaledZeta = Seq(scalePower, Sp, Times, Sp, zeta);
        Formula chiralIdentity = EqualTo(
            Call("chiralSpectralZeta", s),
            scaledZeta);
        Formula fullIdentity = EqualTo(
            Call("fullSpectralZeta", s),
            Seq(D(2), Sp, Times, Sp, scaledZeta));
        Formula normalizedEnergy = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            EqualTo(
                new Formula.Fraction(Call("chiralEnergy", n), scale),
                Seq(n, Sp, Plus, Sp, D(1))));
        Formula normalizedSummand = Call(
            "cpow",
            Call("ofReal", new Formula.Fraction(Call("chiralEnergy", n), scale)),
            negativeS);
        Formula normalizedSum = Seq(
            Sum, Underscore, Grp(n, Sp, InMacro, Sp, naturals), Sp,
            normalizedSummand);
        Formula conclusion = And(
            chiralIdentity,
            And(
                fullIdentity,
                And(normalizedEnergy, EqualTo(normalizedSum, zeta))));
        Formula premise = LessThan(D(1), Call("re", s));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complexes)],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
