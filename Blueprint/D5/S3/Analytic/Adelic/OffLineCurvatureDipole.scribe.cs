using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class OffLineCurvatureDipoleDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflected pair of logarithmic squared-distance potentials has an explicit "
            + "zero-mass curvature with a negative core and positive wings.",
        H("Off-Line Curvature Dipole"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("off-line-curvature-dipole"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/OffLineCurvatureDipole."
                        + "off_line_curvature_dipole"),
                H("A reflected logarithmic pair produces a curvature dipole"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The potential is constructed from the two reflected squared-distance "
                            + "logarithms. The curvature is its second derivative in the normal "
                            + "coordinate at zero, rather than an alias for the target formula.")),
                    Paragraph(Text(
                        "Direct differentiation supplies the rational expression and its sign "
                            + "profile. A decaying rational primitive proves integrability and "
                            + "zero total mass over the real line."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(Open, value, Close), D(2));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula u = F.Id("u");
        Formula t = F.Id("t");
        Formula potential = F.Id("potential");
        Formula curvature = F.Id("curvature");
        Formula displacement = Seq(t, Sp, Minus, Sp, gamma);
        Formula deltaSquare = Square(delta);
        Formula displacementSquare = Square(displacement);
        Formula denominator = Seq(displacementSquare, Sp, Plus, Sp, deltaSquare);

        Formula PotentialAt(Formula normal, Formula frequency)
        {
            Formula frequencyDisplacement = Seq(frequency, Sp, Minus, Sp, gamma);
            Formula minusDistance = Seq(
                Square(Seq(normal, Sp, Minus, Sp, delta)),
                Sp, Plus, Sp, Square(frequencyDisplacement));
            Formula plusDistance = Seq(
                Square(Seq(normal, Sp, Plus, Sp, delta)),
                Sp, Plus, Sp, Square(frequencyDisplacement));
            return Seq(
                new Formula.Fraction(Call("log", minusDistance), D(2)),
                Sp, Plus, Sp,
                new Formula.Fraction(Call("log", plusDistance), D(2)));
        }

        Formula curvatureFormula = Seq(
            D(2), Sp, Times, Sp,
            new Formula.Fraction(
                Seq(displacementSquare, Sp, Minus, Sp, deltaSquare),
                Square(denominator)));
        Formula potentialDefinition = Lambda(
            Seq(u, Comma, Sp, t), PotentialAt(u, t));
        Formula curvatureDefinition = Lambda(
            t,
            Call("deriv", Call("deriv", Lambda(u, Apply(potential, u, t))), D(0)));
        Formula formulaClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            EqualTo(Apply(curvature, t), curvatureFormula));
        Formula centerClause = EqualTo(
            Apply(curvature, gamma),
            Seq(Minus, new Formula.Fraction(D(2), deltaSquare)));
        Formula zeroClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            IffFormula(
                EqualTo(Apply(curvature, t), D(0)),
                Or(
                    EqualTo(t, Seq(gamma, Sp, Minus, Sp, delta)),
                    EqualTo(t, Seq(gamma, Sp, Plus, Sp, delta)))));
        Formula integrableClause = Call("Integrable", curvature);
        Formula massClause = EqualTo(
            Call("integral", t, real, Apply(curvature, t), Call("volume")),
            D(0));
        Formula negativeCoreClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            Implies(
                LessThan(new Formula.Absolute(displacement), delta),
                LessThan(Apply(curvature, t), D(0))));
        Formula positiveWingsClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            Implies(
                LessThan(delta, new Formula.Absolute(displacement)),
                LessThan(D(0), Apply(curvature, t))));
        Formula conclusion = And(
            formulaClause,
            And(
                centerClause,
                And(
                    zeroClause,
                    And(
                        integrableClause,
                        And(massClause, And(negativeCoreClause, positiveWingsClause))))));

        return Disp(Seq(
            Forall, Sp, delta, Comma, Sp, gamma, Sp, InMacro, Sp, real, Comma, RowBreak,
            Grp(), LessThan(D(0), delta), Sp, Rightarrow, RowBreak,
            Grp(), Operatorname, Grp(F.Id("let")), Sp,
            potential, Sp, Colon, Eq, Sp, potentialDefinition, Comma, RowBreak,
            Grp(), Operatorname, Grp(F.Id("let")), Sp,
            curvature, Sp, Colon, Eq, Sp, curvatureDefinition, Comma, RowBreak,
            Grp(), conclusion, Dot));
    }
}
