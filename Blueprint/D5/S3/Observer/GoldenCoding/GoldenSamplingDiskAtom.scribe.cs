using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenSamplingDiskAtomDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenSamplingDiskAtom.golden_sampling_disk_atom";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden negative-time sampling sends positive-height modes inside the unit disk.",
        H("Golden Sampling Disk Atom"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-sampling-disk-atom"),
            DeclarationHandle.Create(Declaration),
            H("Positive-height golden samples are disk atoms"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The height h is the mode height minus the observer height, and T_phi "
                        + "is the repository's positive golden scale period. The displayed "
                        + "multiplier separates into a radial golden-ratio power and a "
                        + "unit-norm complex phase.")),
                Paragraph(Text(
                    "Strictly positive height makes the radial exponential less than one. "
                        + "The same norm calculation gives unit norm at height zero and "
                        + "places the reciprocal of every positive-height atom outside the "
                        + "unit disk.")),
                Paragraph(Text(
                    "The inverse-Fourier residue formula in the source depends on a transform "
                        + "convention not defined by the atom. This theorem records the "
                        + "self-contained pointwise consequence for its displayed multiplier."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula frequency = F.Id("omega");
        Formula observerHeight = F.Id("hObserver");
        Formula modeHeight = F.Id("hMode");
        Formula height = F.Id("h");
        Formula atom = F.Id("q");
        Formula period = Seq(F.Id("T"), Underscore, Grp(Varphi));
        Formula phase = Call("exp", Mul(Neg(F.Id("i")), Mul(period, frequency)));
        Formula radialPower = new Formula.Power(
            Varphi,
            Grp(Mul(Neg(D(2)), height)));
        Formula sampledAtom = Call("goldenSamplingAtom", frequency, height);
        Formula boundaryAtom = Call("goldenSamplingAtom", frequency, D(0));
        Formula clauses = All(
            Equal(atom, Mul(radialPower, phase)),
            Equal(new Formula.Norm(atom), radialPower),
            Less(new Formula.Norm(atom), D(1)),
            Equal(new Formula.Norm(boundaryAtom), D(1)),
            Less(D(1), new Formula.Norm(new Formula.Power(atom, Neg(D(1))))));
        Formula definitions = Seq(
            F.Id("let"), Sp, height, Sp, Colon, Eq, Sp,
            Sub(modeHeight, observerHeight), Semi, Sp,
            F.Id("let"), Sp, atom, Sp, Colon, Eq, Sp, sampledAtom, Semi, Sp,
            clauses);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("omega", real),
                Bound("hObserver", real),
                Bound("hMode", real),
            ],
            Implies(Less(observerHeight, modeHeight), definitions)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Neg(Formula value) => new Formula.Negate(value);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) => formulas.Aggregate(And);
}
