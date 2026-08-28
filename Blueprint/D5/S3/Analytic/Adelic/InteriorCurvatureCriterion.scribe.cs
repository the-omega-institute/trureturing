using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class InteriorCurvatureCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source Riesz-curvature measure has no interior atom exactly when every "
            + "canonical nontrivial zeta zero lies on the critical line.",
        H("Interior Curvature Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interior-curvature-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/InteriorCurvatureCriterion."
                        + "interior_curvature_criterion"),
                H("Interior curvature vanishes exactly under the zeta criterion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The right off-line carrier is cut directly from the canonical "
                            + "IsNontrivialZero predicate. Each zero is sent to the source "
                            + "upper-half-plane point with real coordinate minus its ordinate "
                            + "and imaginary coordinate its displacement from one half.")),
                    Paragraph(Text(
                        "The interior curvature is the Measure.sum of Dirac masses with the "
                            + "source coefficient two pi times the analytic multiplicity. "
                            + "Its vanishing is proved from positivity of every indexed atom, "
                            + "not installed as a definition.")),
                    Paragraph(Text(
                        "Reflection of a hypothetical left off-line zero produces a right "
                            + "off-line zero, completing the converse implication."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula point = F.Id("s");
        Formula zero = F.Id("rho");
        Formula rightZeros = F.Id("Zplus");
        Formula upperPoint = F.Id("z");
        Formula curvature = F.Id("curvatureInt");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula pointReal = Call("re", point);
        Formula zeroValue = Call("val", zero);
        Formula zeroReal = Call("re", zeroValue);

        Formula rightZeroSet = new Formula.SetBuilder(
            And(
                Call("IsNontrivialZero", point),
                LessThan(half, pointReal)),
            point,
            complex);
        Formula upperCoordinate = Seq(
            Minus, Call("im", zeroValue), Sp, Plus, Sp,
            F.Id("i"), Sp, Cdot, Sp,
            Open, zeroReal, Sp, Minus, Sp, half, Close);
        Formula upperMap = Lambda(
            Seq(zero, Colon, Sp, Call("Subtype", rightZeros)),
            upperCoordinate);
        Formula twoPi = Seq(D(2), Sp, Cdot, Sp, F.Id("pi"));
        Formula weight = Seq(
            Call("ofReal", twoPi), Sp, Cdot, Sp,
            Call("toENNReal", Call("zeroMult", zeroValue)));
        Formula weightedAtom = Seq(
            weight, Sp, Cdot, Sp, Call("dirac", Call("z", zero)));
        Formula curvatureMeasure = Call(
            "measureSum",
            Lambda(
                Seq(zero, Colon, Sp, Call("Subtype", rightZeros)),
                weightedAtom));
        Formula allZerosCritical = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Call("IsNontrivialZero", point),
                EqualTo(pointReal, half)));
        Formula conclusion = new Formula.Logic(
            allZerosCritical,
            FormulaLogicOperator.Iff,
            EqualTo(curvature, D(0)));

        return Disp(new Formula.Aligned([
            Seq(rightZeros, Sp, Colon, Eq, Sp, rightZeroSet),
            Seq(upperPoint, Sp, Colon, Eq, Sp, upperMap),
            Seq(curvature, Sp, Colon, Eq, Sp, curvatureMeasure),
            Seq(conclusion, Dot),
        ]));
    }
}
