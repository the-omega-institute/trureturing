using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Curvature;

internal sealed class PoissonScaleDipoleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The off-line curvature dipole is the scale derivative of the Poisson kernel.",
        H("Poisson Scale Dipole"),
        Blocks(Describe.Lean(
            DescribeId.Create("poisson-scale-dipole"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Curvature/PoissonScaleDipole.poisson_scale_dipole"),
            H("The off-line curvature dipole is a Poisson scale derivative"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The pointwise identity differentiates the actual real Poisson kernel in its "
                    + "positive scale parameter. Integrability and zero total mass are "
                    + "transported from the frozen off-line curvature theorem, so this is a "
                    + "representation bridge and introduces no RH premise."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LambdaExpr(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(Open, value, Close), D(2));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula scale = F.Id("scale");
        Formula x = F.Id("x");
        Formula t = F.Id("t");
        Formula pi = F.Id("pi");
        Formula poissonKernel = F.Id("poissonKernel");
        Formula curvatureDipole = F.Id("curvatureDipole");
        Formula displacement = Seq(t, Sp, Minus, Sp, gamma);
        Formula deltaSquare = Square(delta);
        Formula displacementSquare = Square(displacement);
        Formula distanceSquare = Seq(
            displacementSquare, Sp, Plus, Sp, deltaSquare);

        Formula poissonDefinition = LambdaExpr(
            Seq(scale, Comma, Sp, x),
            new Formula.Fraction(
                scale,
                Seq(
                    pi, Sp, Times, Sp, Open,
                    Square(scale), Sp, Plus, Sp, Square(x),
                    Close)));
        Formula curvatureDefinition = LambdaExpr(
            t,
            Seq(
                D(2), Sp, Times, Sp,
                new Formula.Fraction(
                    Seq(displacementSquare, Sp, Minus, Sp, deltaSquare),
                    Square(distanceSquare))));
        Formula pointwiseClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            EqualTo(
                Apply(curvatureDipole, t),
                Seq(
                    D(2), Sp, Times, Sp, pi, Sp, Times, Sp,
                    Call(
                        "deriv",
                        LambdaExpr(scale, Apply(poissonKernel, scale, displacement)),
                        delta))));
        Formula integrableClause = Call("Integrable", curvatureDipole);
        Formula massClause = EqualTo(
            Call(
                "integral", t, real, Apply(curvatureDipole, t),
                Call("volume")),
            D(0));
        Formula conclusion = And(
            pointwiseClause,
            And(integrableClause, massClause));

        return Disp(Seq(
            Forall, Sp, delta, Comma, Sp, gamma, Sp, InMacro, Sp, real, Comma, RowBreak,
            Grp(), LessThan(D(0), delta), Sp, Rightarrow, RowBreak,
            Grp(), Operatorname, Grp(F.Id("let")), Sp,
            poissonKernel, Sp, Colon, Eq, Sp, poissonDefinition, Comma, RowBreak,
            Grp(), Operatorname, Grp(F.Id("let")), Sp,
            curvatureDipole, Sp, Colon, Eq, Sp, curvatureDefinition, Comma, RowBreak,
            Grp(), conclusion, Dot));
    }
}
