using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TargetRisk;

internal sealed class RefinementTargetRiskMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factor-map refinement monotonically shrinks target risk.",
        H("Refinement Monotonicity of Target Risk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-monotonically-shrinks-target-risk"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/TargetRisk/RefinementTargetRiskMonotonicity."
                        + "refinement_monotone_target_risk"),
                H("Refinement monotonically shrinks target risk"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public statement uses the family's frozen factor-map refinement, "
                            + "defect relation, and target-risk definitions. A finer readout "
                            + "cannot create a risky target absent from the coarser readout.")),
                    Paragraph(Text(
                        "The proof directly applies the risk-inclusion projection of the frozen "
                            + "refinement theorem. The qualitative source remark about typical "
                            + "cost is deliberately outside this boxed theorem."))),
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

    private static Formula MonotonicityFormula()
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
        Formula targetFamily = Seq(
            Operatorname, Grp(F.Id("Set")), Sp,
            Grp(Arrow(stateType, targetType)));

        return Disp(Seq(
            Forall, Sp,
            stateType, Comma, Sp, coarseType, Comma, Sp,
            fineType, Comma, Sp, targetType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            coarse, Colon, Sp, Arrow(stateType, coarseType), Comma, Sp,
            fine, Colon, Sp, Arrow(stateType, fineType), Comma, RowBreak, Grp(),
            targets, Colon, Sp, targetFamily, Comma, RowBreak, Grp(),
            refines, Sp, Rightarrow, Sp,
            fineRisk, Sp, Subseteq, Sp, coarseRisk, Dot));
    }
}
