using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class GoldenCubePeriodsSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inverse golden-ratio identity used in repetition bounds.",
        H("Inverse golden-ratio identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("inverse-golden-square-add-inverse"),
            DeclarationHandle.Create("D5/S1/Words/Powers/GoldenCubePeriodsSupport.inv_golden_sq_add_inv_golden"),
            H("The inverse golden ratio satisfies a quadratic equation"),
            StatementSource.FromAuthor(Disp(Seq(
                new Formula.Power(new Formula.Power(Seq(Operatorname, Grp(F.Id("Real")), Dot,
                    Operatorname, Grp(F.Id("goldenRatio"))), Seq(Minus, D(1))), D(2)),
                Sp, Plus, Sp,
                new Formula.Power(Seq(Operatorname, Grp(F.Id("Real")), Dot,
                    Operatorname, Grp(F.Id("goldenRatio"))), Seq(Minus, D(1))),
                Sp, Eq, Sp, D(1)))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The square of the inverse golden ratio and the inverse golden ratio sum to one."))),
            DescribeRole.Theorem))));
}
