using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class ThresholdPublicGoodDualEquilibriaDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/DecisionValue/ThresholdPublicGoodDualEquilibria.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An all-or-nothing public good has both unanimous contribution and unanimous "
            + "noncontribution equilibria.",
        H("Threshold Public-Good Dual Equilibria"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-contribute"),
                DeclarationHandle.Create(DeclarationPrefix + "allContribute"),
                H("Unanimous contribution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The public good succeeds exactly when every agent's Boolean action is "
                        + "contribution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold-utility"),
                DeclarationHandle.Create(DeclarationPrefix + "thresholdUtility"),
                H("All-or-nothing public-good utility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Success gives every agent the common benefit. A contributor pays the cost "
                        + "whether the public good succeeds or fails."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nash-stable"),
                DeclarationHandle.Create(DeclarationPrefix + "nashStable"),
                H("Unilateral stability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A profile is stable when every agent's utility at the profile is at least "
                        + "its utility after any unilateral Boolean action update."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold-public-good-dual-equilibria"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "threshold_public_good_dual_equilibria"),
                H("Both unanimous profiles are stable"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source proof requires at least two agents: only then does one lone "
                            + "contributor fail to reach unanimity. This restriction is explicit "
                            + "in the theorem statement together with zero less than cost less "
                            + "than benefit.")),
                    Paragraph(Text(
                        "At unanimous contribution, deviating destroys the benefit and changes "
                            + "payoff from benefit minus cost to zero. At unanimous "
                            + "noncontribution, deviating alone changes payoff from zero to "
                            + "negative cost.")),
                    Paragraph(Text(
                        "The two equilibrium conclusions are separate public conjuncts over the "
                            + "same utility constructed from the all-or-nothing success rule."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula benefit = F.Id("b");
        Formula cost = F.Id("c");
        Formula allContribute = Seq(D(1), Caret, n);
        Formula allAbstain = Seq(D(0), Caret, n);
        Formula stableContribute = Apply("nashStable", benefit, cost, allContribute);
        Formula stableAbstain = Apply("nashStable", benefit, cost, allAbstain);

        return Disp(Seq(
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            benefit, Comma, Sp, cost, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(2), Sp, Leq, Sp, n, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, cost, Sp, Lt, Sp, benefit, Sp, Rightarrow, RowBreak, Grp(),
            stableContribute, Sp, Land, Sp, stableAbstain, Dot));
    }
}
