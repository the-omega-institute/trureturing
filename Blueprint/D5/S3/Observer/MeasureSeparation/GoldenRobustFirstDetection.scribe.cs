using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class GoldenRobustFirstDetectionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/MeasureSeparation/GoldenRobustFirstDetection."
            + "golden_robust_first_detection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first golden observation layer below a simple local defect has a uniform "
            + "normalized energy floor.",
        H("Golden Robust First Detection"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-robust-first-detection"),
            DeclarationHandle.Create(Declaration),
            H("The first crossing retains golden-scale energy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a positive initial scale and a positive defect depth below it, the "
                        + "displayed golden schedule is the literal local layer construction "
                        + "from the Lean statement. Its least layer below the defect exists "
                        + "and all earlier layers remain at or above the defect.")),
                Paragraph(Text(
                    "The local single-defect law converts the minimal crossing estimate into "
                        + "the fourth inverse golden-ratio lower bound. The statement exposes "
                        + "the crossing, its firstness, and the energy bound together."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula omega0 = F.Id("omega0");
        Formula delta = F.Id("delta");
        Formula energy = F.Id("E");
        Formula omega = F.Id("omega");
        Formula first = F.Id("m");
        Formula n = F.Id("n");

        Formula omega0Positive = Less(D(0), omega0);
        Formula deltaPositive = Less(D(0), delta);
        Formula deltaBelowInitial = Less(delta, omega0);
        Formula energyLaw = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("omega", real)],
            Implies(
                Less(D(0), omega),
                Implies(
                    Less(omega, delta),
                    Equal(
                        Apply(energy, omega),
                        Pow(new Formula.Fraction(omega, delta), D(2))))));

        Formula firstCrosses = Less(Layer(first, omega0), delta);
        Formula earlierLayers = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", natural)],
            Implies(Less(n, first), LessOrEqual(delta, Layer(n, omega0))));
        Formula energyFloor = LessOrEqual(
            Pow(F.Varphi, Seq(Minus, D(4))),
            Apply(energy, Layer(first, omega0)));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("m", natural)],
            And(firstCrosses, And(earlierLayers, energyFloor)));
        Formula premises = And(
            omega0Positive,
            And(deltaPositive, And(deltaBelowInitial, energyLaw)));
        Formula statement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("omega0", real),
                Bound("delta", real),
                Bound("E", new Formula.TypeArrow(real, real)),
            ],
            Implies(premises, witness));

        return Disp(statement);
    }

    private static Formula Layer(Formula index, Formula initialScale)
    {
        Formula inverseGolden = Pow(F.Varphi, Seq(Minus, D(1)));
        Formula ratio = Pow(Grp(inverseGolden), D(2));
        return Seq(initialScale, Sp, Times, Sp, Pow(Grp(ratio), index));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Pow(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));
}
