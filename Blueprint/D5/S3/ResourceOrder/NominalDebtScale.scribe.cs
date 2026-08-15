using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class NominalDebtScaleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed nominal debt burden transforms contravariantly under uniform price scaling.",
        H("Fixed Nominal Debt and Price Scale"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-nominal-debt-burden-scales-inversely"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/NominalDebtScale"
                    + ".fixed_nominal_debt_burden_scales_inversely"),
                H("Fixed nominal debt burden scales inversely"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("D"), Comma, Sp, F.Id("p"), Comma, Sp,
                    LambdaLower, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Lt, F.Id("D"), Sp, Land, Sp,
                    D(0), Lt, F.Id("p"), Sp, Land, Sp,
                    D(0), Lt, LambdaLower, Sp, Rightarrow, Sp,
                    Frac, Grp(F.Id("D")), Grp(LambdaLower, Cdot, Sp, F.Id("p")), Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(LambdaLower), Cdot, Sp,
                    Frac, Grp(F.Id("D")), Grp(F.Id("p"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive nominal debt D, positive commodity price p, and positive "
                        + "uniform scale lambda, holding D fixed while replacing p by lambda p "
                        + "multiplies the real burden D/p by 1/lambda.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle both identify "
                        + "div_mul_eq_div_mul_one_div as the exact division-by-a-product lemma. "
                        + "The Lean proof applies that result and only reorders commutative factors.")),
                    Paragraph(Text(
                        "This closes the displayed scaling identity in qdo-v1 corollary/34.2. "
                        + "The surrounding claims about inflation, deflation, and balance-sheet "
                        + "effects are explanatory consequences and are not separately formalized."))),
                DescribeRole.Theorem))));
}
