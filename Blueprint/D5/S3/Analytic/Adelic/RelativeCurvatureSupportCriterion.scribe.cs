using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class RelativeCurvatureSupportCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multiplicity-weighted curvature measure of the canonical nontrivial zeta zeros "
            + "is supported on the critical line exactly when every such zero is critical.",
        H("Relative Curvature Support Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative-curvature-support-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/RelativeCurvatureSupportCriterion."
                        + "relative_curvature_support_criterion"),
                H("Relative curvature is critical exactly under the zeta criterion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The zero carrier is the repository's canonical IsNontrivialZero set. "
                            + "Relative curvature is constructed as the Measure.sum of Dirac "
                            + "masses weighted by the canonical analytic multiplicity zeroMult; "
                            + "its support is not installed by definition.")),
                    Paragraph(Text(
                        "The local proof identifies this carrier with the closed zero locus of "
                            + "the entire xiReading and proves from the measure API that every "
                            + "positive weighted atom, and only such an atom, lies in the support.")),
                    Paragraph(Text(
                        "Since IsNontrivialZero already records the open critical-strip bounds, "
                            + "the resulting support inclusion is equivalent to the universal "
                            + "critical-line assertion."))),
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
        Formula zeros = F.Id("Z");
        Formula curvature = F.Id("curvature");
        Formula strip = F.Id("S");
        Formula line = F.Id("L");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula pointReal = Call("re", point);
        Formula zeroValue = Call("val", zero);

        Formula zeroSet = new Formula.SetBuilder(
            Call("IsNontrivialZero", point), point, complex);
        Formula weightedAtom = Seq(
            Call("toENNReal", Call("zeroMult", zeroValue)), Sp, Cdot, Sp,
            Call("dirac", zeroValue));
        Formula curvatureMeasure = Call(
            "measureSum",
            Lambda(
                Seq(zero, Colon, Sp, Call("Subtype", zeros)),
                weightedAtom));
        Formula criticalStrip = new Formula.SetBuilder(
            And(LessThan(D(0), pointReal), LessThan(pointReal, D(1))),
            point,
            complex);
        Formula criticalLine = new Formula.SetBuilder(
            EqualTo(pointReal, half), point, complex);
        Formula allZerosCritical = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Call("IsNontrivialZero", point),
                Call("mem", point, line)));
        Formula supportInStrip = Call(
            "inter", Call("support", curvature), strip);
        Formula supportCriterion =
            Seq(supportInStrip, Sp, Subseteq, Sp, line);
        Formula conclusion = new Formula.Logic(
            allZerosCritical,
            FormulaLogicOperator.Iff,
            supportCriterion);

        return Disp(new Formula.Aligned([
            Seq(zeros, Sp, Colon, Eq, Sp, zeroSet),
            Seq(curvature, Sp, Colon, Eq, Sp, curvatureMeasure),
            Seq(strip, Sp, Colon, Eq, Sp, criticalStrip),
            Seq(line, Sp, Colon, Eq, Sp, criticalLine),
            Seq(conclusion, Dot),
        ]));
    }
}
