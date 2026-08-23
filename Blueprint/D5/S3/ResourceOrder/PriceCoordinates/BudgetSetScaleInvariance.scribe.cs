using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder.PriceCoordinates;

internal sealed class BudgetSetScaleInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous positive scaling of prices and wealth preserves the budget set.",
        H("Budget Set Scale Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("budget-set-scale-invariance"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PriceCoordinates/BudgetSetScaleInvariance."
                        + "budget_set_scale_invariance"),
                H("Positive price and wealth scaling preserves affordable bundles"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For L goods, prices are a strictly positive real vector and nominal "
                            + "wealth is positive. Each budget set is constructed directly as "
                            + "the nonnegative bundles whose finite price dot product does not "
                            + "exceed wealth.")),
                    Paragraph(Text(
                        "Scaling the price vector pulls the positive scalar through the dot "
                            + "product. Multiplication by a positive scalar preserves and reflects "
                            + "the affordability inequality, giving equality of the two sets.")),
                    Paragraph(Text(
                        "Repository search found only the distinct fixed-nominal-debt inverse "
                            + "scaling result. Pinned Mathlib has no exact budget-set theorem; "
                            + "the proof directly applies smul_dotProduct and "
                            + "mul_le_mul_iff_of_pos_left.")),
                    Paragraph(Text(
                        "The module compiles a two-good instance with unit prices, unit wealth, "
                            + "and scale two as simultaneous witnesses for the hypotheses and "
                            + "the set equality."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula goods = F.Id("L");
        Formula price = F.Id("p");
        Formula wealth = F.Id("w");
        Formula scale = LambdaLower;
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula positivePrices = Seq(
            reals, Underscore, Grp(Plus, Plus), Caret, Grp(goods));
        Formula scaledPrice = Seq(scale, Sp, price);
        Formula scaledWealth = Seq(scale, Sp, wealth);

        return Disp(Seq(
            Forall, Sp, goods, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            price, InMacro, Sp, positivePrices, Comma, Sp,
            wealth, Comma, Sp, scale, InMacro, Sp, reals, Comma, Esc,
            D(0), Lt, Sp, wealth, Sp, Land, Sp, D(0), Lt, Sp, scale,
            Sp, Rightarrow, Sp,
            BudgetSet(scaledPrice, scaledWealth, goods), Sp, Eq, Sp,
            BudgetSet(price, wealth, goods), Dot));
    }

    private static Formula BudgetSet(Formula price, Formula wealth, Formula goods)
    {
        Formula bundle = F.Id("x");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula nonnegativeBundles = Seq(
            reals, Underscore, Grp(Plus), Caret, Grp(goods));
        Formula cost = Seq(price, Sp, Cdot, Sp, bundle);

        return Seq(
            OpenBrace, bundle, InMacro, Sp, nonnegativeBundles, Sp, Mid, Sp,
            cost, Sp, Leq, Sp, wealth, CloseBrace);
    }
}
