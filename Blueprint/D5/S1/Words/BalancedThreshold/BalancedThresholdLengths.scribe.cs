using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdLengthsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Computed continuant coordinates give positive and increasing physical return lengths.",
        H("Growth of the total coordinates"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-uniform-continuant-length-growth"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdLengths.uniform_continuant_length_growth"),
            H("Positive seeds and the recurrence give strict growth after the initial pair"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For each parameter at least five, every auxiliary continuant has a positive "
                + "sum of numerator and denominator coordinates. The first two sums are both "
                + "one. At every later index, the next sum is strictly larger. Two-step "
                + "induction propagates positivity through the actual computed recurrence; "
                + "the positive predecessor and partial denominator at least one then give "
                + "strict growth. Thus the predecessor and current primitive return lengths "
                + "satisfy zero less than H less than R whenever the convergent index is "
                + "positive. This estimate supplies the finite-length comparison in the "
                + "synchronized return bounds; it does not assert the critical exponent."))),
            DescribeRole.Theorem))));
}
