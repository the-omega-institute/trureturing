using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class FiniteRitzChristoffelBoundsDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive top-atom mass and spectral gap convert an attained reduced-energy "
            + "minimum into a sharp two-sided variational Ritz error bar.",
        H("Finite Ritz--Christoffel Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-ritz-christoffel-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/FiniteRitzChristoffelBounds."
                        + "finite_ritz_christoffel_bounds"),
                H("Sharp finite variational error bar"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The atom mass and spectral gap are explicitly positive. Tail "
                            + "mass and reduced energy are nonnegative, and the gap times "
                            + "tail mass is bounded by reduced energy for every trial.")),
                    Paragraph(Text(
                        "Attainment of both minima avoids any total-infimum convention. "
                            + "Comparing denominators gives the lower error bar; evaluating "
                            + "the Ritz minimum at a Christoffel minimizer gives the upper "
                            + "bar. The two final scalar configurations attain its two "
                            + "endpoints.")),
                    Paragraph(Text(
                        "The source's zeta-specific superfactorial rate is not part of this "
                            + "statement: it requires additional zero-density and "
                            + "orthogonal-polynomial asymptotics."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula TheoremFormula()
    {
        Formula trialType = F.Id("Trial");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula atomMass = F.Id("mu1");
        Formula gap = F.Id("g");
        Formula cost = F.Id("lambda");
        Formula error = F.Id("epsilon");
        Formula correction = F.Id("delta");
        Formula trial = F.Id("q");
        Formula tail = F.Id("T");
        Formula energy = F.Id("E");
        Formula tailAtTrial = Apply(tail, trial);
        Formula energyAtTrial = Apply(energy, trial);
        Formula rayleighAtTrial = Fraction(
            energyAtTrial,
            Seq(atomMass, Sp, Plus, Sp, tailAtTrial));
        Formula trialConditions = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("q", trialType)],
            And(
                LessThanOrEqual(D(0), tailAtTrial),
                And(
                    LessThanOrEqual(D(0), energyAtTrial),
                    LessThanOrEqual(
                        Seq(gap, Sp, Cdot, Sp, tailAtTrial),
                        energyAtTrial))));
        Formula hypotheses = And(
            LessThan(D(0), atomMass),
            And(
                LessThan(D(0), gap),
                And(
                    trialConditions,
                    And(
                        Call("IsLeast", Call("range", energy), cost),
                        Call(
                            "IsLeast",
                            Call("range", Lambda(trial, rayleighAtTrial)),
                            error)))));
        Formula correctionDefinition = EqualTo(
            correction,
            Fraction(cost, Seq(atomMass, Sp, Cdot, Sp, gap)));
        Formula lower = Fraction(
            cost,
            Seq(atomMass, Sp, Cdot, Sp, Grp(D(1), Sp, Plus, Sp, correction)));
        Formula upper = Fraction(cost, atomMass);
        Formula bounds = And(
            LessThanOrEqual(D(0), correction),
            And(
                LessThanOrEqual(lower, error),
                LessThanOrEqual(error, upper)));
        Formula upperSharp = EqualTo(
            Fraction(cost, Seq(atomMass, Sp, Plus, Sp, D(0))),
            upper);
        Formula lowerSharp = EqualTo(
            Fraction(
                cost,
                Seq(atomMass, Sp, Plus, Sp, Fraction(cost, gap))),
            lower);
        Formula conclusion = And(
            correctionDefinition,
            And(bounds, And(upperSharp, lowerSharp)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Trial", F.Id("Type")),
                Bound("mu1", reals),
                Bound("g", reals),
                Bound("lambda", reals),
                Bound("epsilon", reals),
                Bound("T", Seq(trialType, Sp, To, Sp, reals)),
                Bound("E", Seq(trialType, Sp, To, Sp, reals)),
            ],
            Implies(hypotheses, conclusion)));
    }
}
