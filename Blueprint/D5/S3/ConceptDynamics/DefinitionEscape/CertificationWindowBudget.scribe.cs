using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class CertificationWindowBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula type = F.Id("Type");
        Formula indexType = F.Id("I");
        Formula targetType = F.Id("Target");
        Formula gamma = Gamma;
        Formula coverage = F.Id("coverage");
        Formula candidateCost = F.Id("candidateCost");
        Formula nnreal = Seq(Operatorname, Grp(F.Id("NNReal")));
        Formula claimA = F.Id("claimA");
        Formula claimB = F.Id("claimB");
        Formula budgetA = F.Id("budgetA");
        Formula budgetB = F.Id("budgetB");
        Formula targetSet = Call("Set", targetType);
        Formula window(Formula budget) =>
            Call("certificationWindow", gamma, coverage, candidateCost, budget);
        Formula certified(Formula claim, Formula budget) =>
            Seq(claim, Sp, InMacro, Sp, window(budget));

        Formula commonBinders = Seq(
            Forall, Sp, Typed(indexType, type), Comma, Sp,
            Typed(targetType, type), Comma, RowBreak, Grp(),
            Typed(gamma, Call("Set", indexType)), Comma, Sp,
            Typed(coverage, new Formula.TypeArrow(indexType, targetSet)), Comma,
            RowBreak, Grp(),
            Typed(candidateCost, new Formula.TypeArrow(indexType, nnreal)), Comma);

        Formula monotoneStatement = Disp(Seq(
            commonBinders, RowBreak, Grp(),
            Call("Monotone", Call("certificationWindow", gamma, coverage, candidateCost)),
            Dot));

        Formula unionStatement = Disp(new Formula.Aligned([
            commonBinders,
            Seq(
                Typed(claimA, targetSet), Comma, Sp,
                Typed(claimB, targetSet), Comma),
            Seq(
                Typed(budgetA, nnreal), Comma, Sp,
                Typed(budgetB, nnreal), Comma),
            Seq(
                certified(claimA, budgetA), Sp, Rightarrow, Sp,
                certified(claimB, budgetB), Sp, Rightarrow),
            Seq(
                certified(
                    Call("union", claimA, claimB),
                    Seq(budgetA, Sp, Plus, Sp, budgetB)),
                Dot),
        ]));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite certification windows grow with budget and are closed under union at "
                + "the summed budget.",
            H("Certification Windows under Budget"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("certification-window-budget-monotone"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget."
                            + "certification_window_budget_monotone"),
                    H("Certification windows are monotone in budget"),
                    StatementSource.FromAuthor(monotoneStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Candidates lie in Gamma. Each candidate has a nonnegative-real "
                                + "cost and covers a set of targets. A target set belongs to the "
                                + "certification window when one finite selection covers it and "
                                + "its canonical finiteSelectionCost is at most the budget.")),
                        Paragraph(Text(
                            "The same finite selection witnesses certification at every larger "
                                + "budget. Consequently the theorem has no finiteness, coverage, "
                                + "positivity, or nonemptiness premise beyond the NNReal types "
                                + "already carried by costs and budgets."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("certification-window-union-closed"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/CertificationWindowBudget."
                            + "certification_window_union_closed"),
                    H("Certified target sets combine at the summed budget"),
                    StatementSource.FromAuthor(unionStatement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Given witnesses for claimA and claimB, the union of their finite "
                                + "candidate selections captures the union of the target sets. "
                                + "Candidates present in both selections occur only once in the "
                                + "combined selection.")),
                        Paragraph(Text(
                            "Nonnegative candidate costs make the combined selection cost at "
                                + "most the sum of the two original costs. This yields unconditional "
                                + "union closure at budgetA plus budgetB; allowing signed costs "
                                + "would invalidate that natural subadditivity argument."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);
}
