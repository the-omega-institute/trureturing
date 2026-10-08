using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identify the computed continued fraction of the minority-to-majority ratio.",
        H("The infinite period-two expansion"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-ratio-expansion"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdExpansion.uniform_ratio_expansion"),
            H("Two initial digits and an alternating tail"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every integer t at least five, the ratio alpha/(1-alpha) for "
                + "the explicit uniform frequency has computed continued fraction "
                + "[0; t+2, t, t-2, t+1, t-2, t+1, ...]. The positive quadratic root "
                + "and its opposite tail satisfy reciprocal equations. Simultaneous "
                + "induction follows Mathlib's floor algorithm through every alternating "
                + "tail digit, and two prefix steps supply the initial coefficients. "
                + "The mechanical frequency alpha itself has a different expansion. "
                + "No Sturmian return classification or recurrence conclusion is "
                + "asserted by this theorem."))),
            DescribeRole.Theorem))));
}
