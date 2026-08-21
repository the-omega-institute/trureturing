using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TargetRisk;

internal sealed class RefinementRiskCostTradeoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement shrinks target risk while increasing attained-coordinate cost.",
        H("Refinement, Target Risk, and Cost"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-reduces-target-risk-and-raises-cost"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff."
                        + "refinement_reduces_target_risk_and_raises_cost"),
                H("Refinement reduces risk and raises coordinate cost"),
                StatementSource.FromAuthor(TradeoffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The defect relation consists of state pairs identified by a source "
                            + "readout but distinguished by a target. Target risk filters a supplied "
                            + "target family for targets with a nonempty defect relation.")),
                    Paragraph(Text(
                        "A factor-map refinement preserves every equality seen by the finer "
                            + "readout, so each fine defect is also a coarse defect and fine target "
                            + "risk is contained in coarse target risk.")),
                    Paragraph(Text(
                        "Cost is the extended cardinality of attained readout coordinates. The "
                            + "factor map sends the fine range onto the coarse range, so refinement "
                            + "cannot lower this cost. Coarser compression trades that cost benefit "
                            + "against a potentially larger future-risk set."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TradeoffFormula()
    {
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula targetType = F.Id("T");
        Formula coarse = new Formula.Subscript(F.Id("q"), coarseType);
        Formula fine = new Formula.Subscript(F.Id("q"), fineType);
        Formula targets = Seq(Mathcal, Grp(F.Id("T")));
        Formula refines = Apply(
            Seq(Operatorname, Grp(F.Id("Refines"))), coarse, fine);
        Formula coarseRisk = Apply(
            Seq(Operatorname, Grp(F.Id("targetRisk"))), coarse, targets);
        Formula fineRisk = Apply(
            Seq(Operatorname, Grp(F.Id("targetRisk"))), fine, targets);
        Formula coarseCost = Apply(
            Seq(Operatorname, Grp(F.Id("refinementCost"))), coarse);
        Formula fineCost = Apply(
            Seq(Operatorname, Grp(F.Id("refinementCost"))), fine);
        Formula readoutCoarse = Arrow(stateType, coarseType);
        Formula readoutFine = Arrow(stateType, fineType);
        Formula targetReadout = Arrow(stateType, targetType);
        Formula targetFamily = Seq(
            Operatorname, Grp(F.Id("Set")), Sp, Grp(targetReadout));
        Formula types = Seq(
            stateType, Comma, Sp, coarseType, Comma, Sp, fineType, Comma, Sp,
            targetType, Colon, Sp, Operatorname, Grp(F.Id("Type")));

        return Disp(Seq(
            Forall, Sp, types, Comma, Sp,
            coarse, Colon, Sp, readoutCoarse, Comma, Sp,
            fine, Colon, Sp, readoutFine, Comma, Sp,
            targets, Colon, Sp, targetFamily, Comma, Sp,
            refines, Sp, Rightarrow, Esc,
            Open, fineRisk, Sp, Subseteq, Sp, coarseRisk, Close, Sp, Land, Esc,
            Open, coarseCost, Sp, Le, Sp, fineCost, Close, Dot));
    }
}
