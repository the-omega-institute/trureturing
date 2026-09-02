using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Curvature;

internal sealed class OffLineCurvatureDipoleTotalVariationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Curvature/OffLineCurvatureDipoleTotalVariation."
            + "off_line_curvature_dipole_total_variation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The off-line curvature dipole has total variation four divided by its scale.",
        H("Off-Line Curvature Dipole Total Variation"),
        Blocks(Describe.Lean(
            DescribeId.Create("off-line-curvature-dipole-total-variation"),
            DeclarationHandle.Create(Declaration),
            H("The off-line curvature dipole has exact total variation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The frozen dipole theorem supplies integrability, zero total mass, "
                    + "the negative core, the positive wings, and the boundary zeros. "
                    + "Its elementary primitive gives core mass minus two divided by "
                    + "the scale, so the wings contribute two divided by the scale."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

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
        Formula t = F.Id("t");
        Formula kappa = F.Id("kappa");
        Formula displacement = Seq(t, Sp, Minus, Sp, gamma);
        Formula deltaSquare = Square(delta);
        Formula displacementSquare = Square(displacement);
        Formula distanceSquare = Seq(
            displacementSquare, Sp, Plus, Sp, deltaSquare);
        Formula kappaDefinition = LambdaExpr(
            t,
            Seq(
                D(2), Sp, Times, Sp,
                new Formula.Fraction(
                    Seq(displacementSquare, Sp, Minus, Sp, deltaSquare),
                    Square(distanceSquare))));
        Formula absoluteIntegral = Call(
            "integral",
            t,
            real,
            new Formula.Absolute(Apply(kappa, t)),
            Call("volume"));
        Formula conclusion = EqualTo(
            absoluteIntegral,
            new Formula.Fraction(D(4), delta));

        return Disp(Seq(
            Forall, Sp, delta, Comma, Sp, gamma, Sp, InMacro, Sp, real, Comma,
            RowBreak, Grp(), LessThan(D(0), delta), Sp, Rightarrow, RowBreak,
            Grp(), Operatorname, Grp(F.Id("let")), Sp,
            kappa, Sp, Colon, Eq, Sp, kappaDefinition, Comma, RowBreak,
            Grp(), conclusion, Dot));
    }
}
