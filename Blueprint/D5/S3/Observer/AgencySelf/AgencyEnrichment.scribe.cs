using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencySelf;

internal sealed class AgencyEnrichmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/AgencySelf/AgencyEnrichment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Agency enrichment pairs current state and strategy, isolates the strategy residual inside current fibers, and becomes agency completion only after controlled behavior closure.",
        H("Agency Enrichment"),
        Blocks(
            Theorem(
                "current-kernel-strategy-residual-partition",
                "current_kernel_strategy_residual_partition",
                CurrentKernelStrategyResidualPartitionFormula(),
                "Current Kernel Strategy Residual Partition",
                "Inside a current-state fiber, a pair either agrees under the enriched readout or is a strategy residual.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "agency-kernel-disjoint-strategy-residual",
                "agency_kernel_disjoint_strategy_residual",
                AgencyKernelDisjointStrategyResidualFormula(),
                "Agency Kernel Disjoint Strategy Residual",
                "The enriched kernel and the strategy residual are disjoint.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-strategy-residual-iff-kernel-inclusion",
                "no_strategy_residual_iff_kernel_inclusion",
                NoStrategyResidualIffKernelInclusionFormula(),
                "No Strategy Residual iff Kernel Inclusion",
                "There is no strategy residual exactly when strategy is constant on every current-state fiber.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strategy-factorization-iff-no-residual",
                "strategy_factorization_iff_no_residual",
                StrategyFactorizationIffNoResidualFormula(),
                "Strategy Factorization iff No Residual",
                "Vanishing strategy residual is equivalent to a unique factor from the realized current-state image to the realized strategy image.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "agency-enrichment-kernel-eq-current-iff-no-residual",
                "agency_enrichment_kernel_eq_current_iff_no_residual",
                AgencyEnrichmentKernelEqCurrentIffNoResidualFormula(),
                "Agency Enrichment Kernel eq Current iff No Residual",
                "Pairing strategy adds no new distinction exactly when the strategy residual vanishes.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula CurrentKernelStrategyResidualPartitionFormula() => Statement(
    [Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("current")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P")))), Typed(Seq(F.Id("x")), Seq(F.Id("H"))), Typed(Seq(F.Id("y")), Seq(F.Id("H")))],
        [],
        [],
        Seq(F.Id("current"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("current"), Sp, F.Id("y"), Sp, Leftrightarrow, Sp, F.Id("agencyEnrichment"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("agencyEnrichment"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("y"), Sp, Lor, Sp, F.Id("StrategyResidual"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, F.Id("y")));

private static Formula AgencyKernelDisjointStrategyResidualFormula() => Statement(
    [Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("current")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P")))), Typed(Seq(F.Id("x")), Seq(F.Id("H"))), Typed(Seq(F.Id("y")), Seq(F.Id("H")))],
        [],
        [],
        Seq(Neg, Sp, Open, F.Id("agencyEnrichment"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("agencyEnrichment"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("y"), Sp, Land, Sp, F.Id("StrategyResidual"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, F.Id("y"), Close));

private static Formula NoStrategyResidualIffKernelInclusionFormula() => Statement(
    [Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("current")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P"))))],
        [],
        [],
        Seq(Open, Forall, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp, Neg, Sp, F.Id("StrategyResidual"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, F.Id("y"), Close, Sp, Leftrightarrow, Sp, Forall, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp, F.Id("current"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("current"), Sp, F.Id("y"), Sp, Rightarrow, Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("strategy"), Sp, F.Id("y")));

private static Formula StrategyFactorizationIffNoResidualFormula() => Statement(
    [Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("current")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P"))))],
        [],
        [],
        Seq(Open, Exists, Bang, Sp, F.Id("factor"), Sp, Colon, Sp, new Formula.TypeArrow(Seq(F.Id("Set"), Dot, F.Id("range"), Sp, F.Id("current")), Seq(F.Id("Set"), Dot, F.Id("range"), Sp, F.Id("strategy"))), Comma, Sp, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("factor"), Sp, Open, F.Id("Set"), Dot, F.Id("rangeFactorization"), Sp, F.Id("current"), Sp, F.Id("x"), Close, Sp, Eq, Sp, F.Id("Set"), Dot, F.Id("rangeFactorization"), Sp, F.Id("strategy"), Sp, F.Id("x"), Close, Sp, Leftrightarrow, Sp, Forall, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp, Neg, Sp, F.Id("StrategyResidual"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, F.Id("y")));

private static Formula AgencyEnrichmentKernelEqCurrentIffNoResidualFormula() => Statement(
    [Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("current")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P"))))],
        [],
        [],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("agencyEnrichment"), Sp, F.Id("current"), Sp, F.Id("strategy"), Close, Sp, Eq, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("current"), Sp, Leftrightarrow, Sp, Forall, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp, Neg, Sp, F.Id("StrategyResidual"), Sp, F.Id("current"), Sp, F.Id("strategy"), Sp, F.Id("x"), Sp, F.Id("y")));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
