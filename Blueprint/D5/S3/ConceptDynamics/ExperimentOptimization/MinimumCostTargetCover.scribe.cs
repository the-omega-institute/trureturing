using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentOptimization;

internal sealed class MinimumCostTargetCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ExperimentOptimization/MinimumCostTargetCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target-sufficient finite intervention designs are exactly weighted covers of the "
            + "target-disagreement pairs, including three boundary witnesses.",
        H("Minimum-Cost Target Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-disagreement-pairs"),
                DeclarationHandle.Create(Prefix + "targetDisagreementPairs"),
                H("Target-disagreement pair universe"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The universe contains the unordered finite-model pairs on which the "
                        + "chosen target takes unequal values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("intervention-separation-set"),
                DeclarationHandle.Create(Prefix + "interventionSeparationSet"),
                H("Pairs separated by an intervention"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An intervention contributes the target-disagreement pairs whose two "
                        + "models also have unequal responses under that intervention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("minimum-cost-target-sufficient-design-iff-pair-cover"),
                DeclarationHandle.Create(
                    Prefix + "minimum_cost_target_sufficient_design_iff_pair_cover"),
                H("Minimum-cost target sufficiency is weighted pair cover"),
                StatementSource.FromAuthor(MinimumCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The imported target-sufficiency criterion identifies feasibility "
                            + "with coverage of exactly the target-disagreement universe.")),
                    Paragraph(Text(
                        "The identical real-valued finite sum is minimized over the two "
                            + "extensionally equal feasible families, so no nonnegativity "
                            + "assumption on intervention costs is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-cost-target-sufficient-design-witness"),
                DeclarationHandle.Create(
                    Prefix + "zero_cost_target_sufficient_design_witness"),
                H("Zero costs make every sufficient design minimal"),
                StatementSource.FromAuthor(ZeroCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When every selected summand is zero, any target-sufficient design has "
                        + "the same cost as every candidate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-intervention-cover-witness"),
                DeclarationHandle.Create(Prefix + "singleton_intervention_cover_witness"),
                H("One identity intervention covers the two-state target"),
                StatementSource.FromAuthor(SingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On Fin 2, the sole identity readout is target-sufficient for the identity "
                        + "target and covers every target-disagreement pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-target-cover-witness"),
                DeclarationHandle.Create(Prefix + "empty_target_cover_witness"),
                H("The empty horizon has an empty cover"),
                StatementSource.FromAuthor(EmptyTargetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At horizon zero, the empty intervention type and empty design are "
                        + "sufficient for the constant target and cover its empty pair "
                        + "universe."))),
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
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula CostAt(Formula selection) =>
        Apply(F.Id("C"), selection);

    private static Formula Sufficient(Formula selection) =>
        Apply(F.Id("S"), selection);

    private static Formula Covers(Formula selection) =>
        Apply(F.Id("Cover"), selection);

    private static Formula ZeroSum(Formula selection) =>
        Seq(
            Sum, Underscore,
            Grp(F.Id("a"), Sp, InMacro, Sp, selection), Sp, D(0));

    private static Formula MinimumCostFormula()
    {
        Formula n = F.Id("n");
        Formula intervention = F.Id("A");
        Formula response = F.Id("R");
        Formula targetType = F.Id("Y");
        Formula cost = F.Id("c");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula selected = F.Id("J");
        Formula candidate = F.Id("K");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula finN = Apply(F.Id("Fin"), n);
        Formula selectedType = Apply(F.Id("Finset"), intervention);
        Formula responseFamily = Arrow(intervention, type);
        Formula costType = Arrow(intervention, Seq(Mathbb, Grp(F.Id("R"))));
        Formula readoutType = Seq(
            Forall, Sp, F.Id("a"), Colon, Sp, intervention, Comma, Sp,
            Arrow(finN, Apply(response, F.Id("a"))));
        Formula minimumSufficient = Seq(
            Sufficient(selected), Sp, Land, Sp, Open,
            Forall, Sp, candidate, Colon, Sp, selectedType, Comma, Sp,
            Sufficient(candidate), Sp, Rightarrow, Sp,
            CostAt(selected), Sp, Leq, Sp, CostAt(candidate), Close);
        Formula minimumCover = Seq(
            Covers(selected), Sp, Land, Sp, Open,
            Forall, Sp, candidate, Colon, Sp, selectedType, Comma, Sp,
            Covers(candidate), Sp, Rightarrow, Sp,
            CostAt(selected), Sp, Leq, Sp, CostAt(candidate), Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(n, Seq(Mathbb, Grp(F.Id("N")))), Comma, Sp,
                Typed(Seq(intervention, Comma, Sp, targetType), type), Comma),
            Seq(Typed(response, responseFamily), Comma, Sp, Typed(cost, costType), Comma),
            Seq(Typed(readout, readoutType), Comma, Sp,
                Typed(target, Arrow(finN, targetType)), Comma),
            Seq(Typed(selected, selectedType), Comma),
            Seq(
                Forall, Sp, candidate, Colon, Sp, selectedType, Comma, Sp,
                CostAt(candidate), Sp, Eq, Sp, Sum, Underscore,
                Grp(F.Id("a"), Sp, InMacro, Sp, candidate), Sp,
                Apply(cost, F.Id("a")), Comma),
            Seq(Open, minimumSufficient, Close, Sp, Iff, Sp),
            Seq(Open, minimumCover, Close, Dot),
        ]));
    }

    private static Formula ZeroCostFormula()
    {
        Formula selected = F.Id("J");
        Formula candidate = F.Id("K");

        return Disp(Seq(
            Sufficient(selected), Sp, Rightarrow, RowBreak, Grp(),
            Sufficient(selected), Sp, Land, Sp, Open,
            Forall, Sp, candidate, Comma, Sp,
            ZeroSum(selected), Sp, Leq, Sp, ZeroSum(candidate), Close, Dot));
    }

    private static Formula SingletonFormula()
    {
        Formula selected = F.Id("J");
        Formula identity = F.Id("id");

        return Disp(Seq(
            F.Id("A"), Sp, Eq, Sp, F.Id("Unit"), Comma, Sp,
            F.Id("X"), Sp, Eq, Sp, Apply(F.Id("Fin"), D(2)), Comma, Sp,
            selected, Sp, Eq, Sp, OpenBrace, F.Id("star"), CloseBrace, Comma,
            RowBreak, Grp(),
            Apply(F.Id("q"), F.Id("star")), Sp, Eq, Sp, identity, Comma, Sp,
            F.Id("T"), Sp, Eq, Sp, identity, Sp, Rightarrow, RowBreak, Grp(),
            Sufficient(selected), Sp, Land, Sp, Covers(selected), Dot));
    }

    private static Formula EmptyTargetFormula()
    {
        Formula selected = F.Id("J");

        return Disp(Seq(
            F.Id("n"), Sp, Eq, Sp, D(0), Comma, Sp,
            F.Id("A"), Sp, Eq, Sp, Emptyset, Comma, Sp,
            selected, Sp, Eq, Sp, Emptyset, Comma, RowBreak, Grp(),
            F.Id("T"), Sp, Eq, Sp, F.Id("constant"), Sp, Rightarrow, RowBreak, Grp(),
            Sufficient(selected), Sp, Land, Sp, Covers(selected), Dot));
    }
}
