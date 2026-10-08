using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdBalanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count constant-gap palette colours in mechanical windows.",
        H("Balance of the palette colouring"),
        Blocks(Describe.Lean(
            DescribeId.Create("palette-colouring-balanced"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdBalance.palette_colouring_balanced"),
            H("Colour counts differ by at most one"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every positive t, every mechanical slope in the half-open interval "
                + "from zero to one, and every real intercept, the palette word is balanced "
                + "in the fixed balanced-threshold window-count sense. Each colour determines "
                + "a source letter and one residue class. Physical-window induction converts "
                + "its count into a rank-quotient difference; remainder bounds and mechanical "
                + "balance limit count differences to one. Irrationality is not assumed, "
                + "and this statement supplies no critical-exponent upper bound."))),
            DescribeRole.Theorem))));
}
