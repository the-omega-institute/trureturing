using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every occurring irrational mechanical factor has distinct return blocks.",
        H("Mechanical return variation"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-mechanical-return-variation"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdRealization.mechanical_return_variation"),
            H("A single return block is impossible"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every irrational frequency in (0,1), every intercept and "
                + "every occurring factor, including the empty factor, some "
                + "adjacent return differs from any proposed finite block. "
                + "Induction through successive occurrences would otherwise "
                + "produce unbounded multiples of a nonzero irrational "
                + "discrepancy, contradicting the mechanical error bound. "
                + "Together with the two-candidate bispecial classification "
                + "this realizes both candidates. It does not establish their "
                + "continued-fraction indices or the derived-language strip."))),
            DescribeRole.Theorem))));
}
