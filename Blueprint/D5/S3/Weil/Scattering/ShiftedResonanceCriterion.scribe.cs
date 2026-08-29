using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class ShiftedResonanceCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shifted zero points lie on one horizontal line exactly when every zero has critical real part.",
        H("Shifted Resonance Horizontal Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shifted-resonances-characterize-the-critical-line"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/ShiftedResonanceCriterion."
                        + "horizontal_resonance_line_iff_critical_line"),
                H("Shifted resonances characterize the critical line"),
                StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For supplied ZeroData and a real shift omega at least one half, the "
                            + "public resonance map sends index n to the complex point "
                            + "minus Im(Z.zero n) plus i times omega plus Re(Z.zero n) minus "
                            + "criticalAbscissa. The displayed inclusion is the range of this "
                            + "map intersected with the upper half-plane contained in the "
                            + "horizontal line of height omega.")),
                    Paragraph(Text(
                        "Every enumerated zero is in the open strip, so the shifted points are "
                            + "automatically in the upper half-plane for the stated shift. "
                            + "The two directions then reduce the line condition to equality "
                            + "of each zero real part with the critical abscissa."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        var z = F.Id("Z");
        var omega = F.Id("omega");
        var n = F.Id("n");
        var critical = Call("criticalAbscissa");
        var zeroLine = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"),
                Seq(Mathbb, Sp, Grp(F.Id("N"))))],
            Equal(Seq(Re, Open, Seq(F.Id("Z"), Dot, F.Id("zero"), Open, n, Close), Close),
                critical));
        var inclusion = new Formula.Relation(
            Call("rangeIntersectUpper", Call("resonance", omega)),
            FormulaRelationOperator.SubsetOf,
            Call("horizontalLine", omega));
        var core = new Formula.Logic(zeroLine, FormulaLogicOperator.Iff, inclusion);
        return Seq(
            Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
            Forall, Sp, omega, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            new Formula.Logic(
                new Formula.Relation(Seq(Frac, Grp(Num(1)), Grp(Num(2))),
                    FormulaRelationOperator.LessThanOrEqual, omega),
                FormulaLogicOperator.Implies,
                core));
    }
}
