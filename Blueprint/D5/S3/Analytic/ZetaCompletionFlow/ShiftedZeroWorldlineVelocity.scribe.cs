using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCompletionFlow;

internal sealed class ShiftedZeroWorldlineVelocityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ZetaCompletionFlow/ShiftedZeroWorldlineVelocity.shifted_zero_worldline_universal_velocity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shifted affine zero has a universal velocity and separates its horizontal label from its boundary-crossing time.",
        H("Shifted-Zero Worldline Velocity"),
        Blocks(Describe.Lean(
            DescribeId.Create("shifted-zero-worldline-universal-velocity"),
            DeclarationHandle.Create(Declaration),
            H("The shifted zero moves with velocity minus i"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "At every observation depth, the affine observation equation has exactly "
                        + "one root: the shifted-zero worldline with horizontal coordinate minus "
                        + "gamma and imaginary coordinate delta minus omega.")),
                Paragraph(Text(
                    "For every nonzero real step, the complex difference quotient is exactly "
                        + "minus i. The nonzero-step premise excludes the totalized-division "
                        + "degeneracy, while arbitrary gamma and delta make the velocity universal.")),
                Paragraph(Text(
                    "The imaginary coordinate vanishes exactly when the observation depth equals "
                        + "delta. Thus gamma records the horizontal label and delta records the "
                        + "boundary-crossing time; the theorem does not assert that the trajectory "
                        + "is a zero of the Riemann zeta function."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula gamma = F.Id("gamma");
        Formula delta = F.Id("delta");
        Formula omega = F.Id("omega");
        Formula step = F.Id("step");
        Formula t = F.Id("t");
        Formula z = F.Id("z");

        Formula worldline(Formula depth) =>
            Call("shiftedZeroWorldline", gamma, delta, depth);
        Formula uniqueRoot = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real), Bound("z", complex)],
            Iff(
                EqualTo(Call("shiftedObservation", gamma, delta, t, z), D(0)),
                EqualTo(z, worldline(t))));
        Formula velocity = EqualTo(
            new Formula.Fraction(
                Subtract(worldline(Add(omega, step)), worldline(omega)),
                step),
            Seq(Minus, F.Id("i")));
        Formula coordinates = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            And(
                EqualTo(Call("Re", worldline(t)), Seq(Minus, gamma)),
                EqualTo(Call("Im", worldline(t)), Subtract(delta, t))));
        Formula crossing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            Iff(
                EqualTo(Call("Im", worldline(t)), D(0)),
                EqualTo(t, delta)));
        Formula conclusion = And(uniqueRoot, And(velocity, And(coordinates, crossing)));
        Formula premise = NotEqualTo(step, D(0));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("gamma", real),
                Bound("delta", real),
                Bound("omega", real),
                Bound("step", real),
            ],
            Implies(premise, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Not(EqualTo(left, right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
