using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class PaidInformationIncentiveConflictDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive costly information production conflicts with a fully revealing price.",
        H("Paid Information and Full Revelation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paid-information-full-revelation-incentive-conflict"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PaidInformationIncentiveConflict."
                        + "paid_information_full_revelation_conflict"),
                H("Costly private information and full revelation cannot coexist"),
                StatementSource.FromAuthor(ConflictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume that a state with positive private-information production and "
                            + "a fully revealing price identifies at least one paid information "
                            + "trader. Full revelation makes every agent's marginal gross "
                            + "trading benefit from the private information equal to zero.")),
                    Paragraph(Text(
                        "The equilibrium incentive condition is stated explicitly: positive "
                            + "paid information production requires the identified trader's "
                            + "marginal gross benefit to be at least the information cost. This "
                            + "makes the economic content of equilibrium machine-visible.")),
                    Paragraph(Text(
                        "When the information cost is strictly positive, the incentive condition "
                            + "would put that positive cost below zero. Therefore no equilibrium "
                            + "state can have both positive private-information production and a "
                            + "price that fully reveals the information.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle returned the exact order theorem "
                            + "not_le_of_gt, which closes the contradiction directly. Repository "
                            + "search found adjacent pricing modules but no theorem for this "
                            + "incentive conflict; LeanSearch returned HTTP 404."))),
                DescribeRole.Proposition))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply2(Formula function, Formula first, Formula second) =>
        Apply(Apply(function, first), second);

    private static Formula ConflictFormula()
    {
        Formula state = F.Id("state");
        Formula agent = F.Id("agent");
        Formula equilibrium = F.Id("Equilibrium");
        Formula production = F.Id("PositiveProduction");
        Formula revelation = F.Id("FullyRevealing");
        Formula paidTrade = F.Id("PaidTrade");
        Formula benefit = F.Id("MarginalGrossBenefit");
        Formula cost = F.Id("cost");
        return Disp(Seq(
            Open, Forall, Sp, state, Comma, Esc,
            Apply(equilibrium, state), Sp, Land, Sp,
            Apply(production, state), Sp, Land, Sp,
            Apply(revelation, state), Sp, Rightarrow, Sp,
            Exists, Sp, agent, Comma, Sp, Apply2(paidTrade, state, agent), Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, state, Comma, Sp, agent, Comma, Esc,
            Apply(equilibrium, state), Sp, Land, Sp,
            Apply(revelation, state), Sp, Rightarrow, Sp,
            Apply2(benefit, state, agent), Sp, Eq, Sp, D(0), Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, state, Comma, Sp, agent, Comma, Esc,
            Apply(equilibrium, state), Sp, Land, Sp,
            Apply(production, state), Sp, Land, Sp,
            Apply2(paidTrade, state, agent), Sp, Rightarrow, Sp,
            cost, Sp, Leq, Sp, Apply2(benefit, state, agent), Close,
            Sp, Land, Sp, D(0), Sp, Lt, Sp, cost,
            Sp, Rightarrow, RowBreak,
            Neg, Exists, Sp, state, Comma, Esc,
            Apply(equilibrium, state), Sp, Land, Sp,
            Apply(production, state), Sp, Land, Sp,
            Apply(revelation, state), Dot));
    }
}
