using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.BalancedThreshold;

internal sealed class BalancedThresholdBracketingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct mechanical bispecial returns have opposite physical discrepancy signs.",
        H("Strict return bracketing"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-threshold-mechanical-return-bracketing"),
            DeclarationHandle.Create(
                "D5/S1/Words/BalancedThreshold/"
                + "BalancedThresholdBracketing.mechanical_return_bracketing"),
            H("Accumulation rules out a common discrepancy sign"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "At any bispecial factor of an irrational characteristic mechanical "
                + "word with frequency in (0,1), the discrepancies of any two distinct "
                + "actual adjacent returns have strictly negative product. The empty "
                + "factor is included. The existing two-return classification and "
                + "bounded-gap recurrence are applied directly. A successive-return "
                + "induction accumulates the common signed error beyond the strict "
                + "window discrepancy bound. Irrationality makes both return errors "
                + "nonzero. This supplies bracketing for continued-fraction identification; "
                + "it does not assert any particular convergent index."))),
            DescribeRole.Theorem))));
}
