using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PoissonPhaseHolonomy;

internal sealed class PairwisePoissonHolonomyEnergyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy."
            + "pairwise_poisson_holonomy_energy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pairwise Poisson phase-holonomy integral is nonnegative, detects equal "
            + "heights, and is invariant under common height translation.",
        H("Pairwise Poisson Phase-Holonomy Energy"),
        Blocks(Describe.Lean(
            DescribeId.Create("pairwise-poisson-phase-holonomy-energy"),
            DeclarationHandle.Create(Declaration),
            H("Poisson phase-holonomy energy has the rational closed form"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For positive transverse depths, a is their sum and d is the "
                        + "difference of the two real phase heights. The energy named in "
                        + "the formula is exactly one over two pi times the full real-line "
                        + "integral of the squared norm of the explicit complex Poisson "
                        + "swap curvature.")),
                Paragraph(Text(
                    "The five result leaves are the rational integral evaluation, "
                        + "nonnegativity, each direction of the zero-height criterion, and "
                        + "invariance under every common real translation.")),
                Paragraph(Text(
                    "This conditional analytic theorem does not assert that off-critical "
                        + "zeros exist and does not identify this curvature with the "
                        + "repository's stable residual swap curvature."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(Open, value, Close), D(2));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula deltaI = F.Id("deltaI");
        Formula deltaJ = F.Id("deltaJ");
        Formula gammaI = F.Id("gammaI");
        Formula gammaJ = F.Id("gammaJ");
        Formula c = F.Id("c");
        Formula pi = F.Id("pi");
        Formula energyFunction = F.Id("poissonPhaseHolonomyEnergy");
        Formula depthFunction = F.Id("poissonTransverseDepthSum");
        Formula differenceFunction = F.Id("poissonHeightDifference");
        Formula depth = Apply(depthFunction, deltaI, deltaJ);
        Formula difference = Apply(differenceFunction, gammaI, gammaJ);
        Formula energy = Apply(energyFunction, deltaI, deltaJ, gammaI, gammaJ);
        Formula denominator = Seq(
            pi, Sp, Times, Sp, depth, Sp, Times, Sp, Open,
            Square(depth), Sp, Plus, Sp, Square(difference), Close);
        Formula closedForm = EqualTo(
            energy,
            new Formula.Fraction(Square(difference), denominator));
        Formula nonnegative = LessThanOrEqual(D(0), energy);
        Formula zeroEnergy = EqualTo(energy, D(0));
        Formula equalHeights = EqualTo(gammaI, gammaJ);
        Formula zeroImpliesEqual = Implies(zeroEnergy, equalHeights);
        Formula equalImpliesZero = Implies(equalHeights, zeroEnergy);
        Formula shiftedEnergy = Apply(
            energyFunction,
            deltaI,
            deltaJ,
            Seq(gammaI, Sp, Plus, Sp, c),
            Seq(gammaJ, Sp, Plus, Sp, c));
        Formula shiftInvariant = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("c", real)],
            EqualTo(shiftedEnergy, energy));
        Formula premises = And(
            LessThan(D(0), deltaI),
            LessThan(D(0), deltaJ));
        Formula conclusion = And(
            closedForm,
            And(
                nonnegative,
                And(
                    zeroImpliesEqual,
                    And(equalImpliesZero, shiftInvariant))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("deltaI", real),
                Bound("deltaJ", real),
                Bound("gammaI", real),
                Bound("gammaJ", real),
            ],
            Implies(premises, conclusion)));
    }
}
