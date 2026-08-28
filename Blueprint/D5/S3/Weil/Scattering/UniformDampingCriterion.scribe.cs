using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class UniformDampingCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the minimal shift, uniform damping one half is equivalent to the critical-line condition.",
        H("Uniform Damping Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-damping-is-critical-line"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/UniformDampingCriterion."
                        + "uniform_damping_iff_critical_line"),
                H("Uniform damping is the critical-line condition"),
                StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The damping rate transported from an enumerated zero at the minimal "
                        + "shift is written as one half plus its real part minus the critical "
                        + "abscissa. Uniform rate one half for every index is equivalent to "
                        + "equality of every zero real part with that abscissa."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        var z = F.Id("Z");
        var n = F.Id("n");
        var critical = Call("criticalAbscissa");
        var zeroReal = Seq(Re, Open,
            Seq(F.Id("Z"), Dot, F.Id("zero"), Open, n, Close), Close);
        var left = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"),
                Seq(Mathbb, Sp, Grp(F.Id("N"))))],
            Equal(Seq(Re, Open,
                Seq(F.Id("Z"), Dot, F.Id("zero"), Open, n, Close), Close), critical));
        var right = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"),
                Seq(Mathbb, Sp, Grp(F.Id("N"))))],
            Equal(Subtract(Add(Seq(Frac, Grp(Num(1)), Grp(Num(2))), zeroReal), critical),
                Seq(Frac, Grp(Num(1)), Grp(Num(2)))));
        return Seq(
            Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
            new Formula.Logic(left, FormulaLogicOperator.Iff, right));
    }
}
