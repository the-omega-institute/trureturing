using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TwistedSameRuleDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/TwistedSameRuleDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same deterministic rule has a defect in every complemented period.",
        H("Same-rule Defects on Twisted Cycles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("twistedsameruledefect-twisted-same-rule-forces-defect"),
                DeclarationHandle.Create(Prefix + "twisted_same_rule_forces_defect"),
                H("A pointwise defect in every period"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Extend a finite signed cycle by complementing the absolute sign after every turn. "
                    + "Its relation bits are periodic. Evaluate one fixed deterministic table on every "
                    + "adjacent R-bit relation window, using the window ending at each output vertex. "
                    + "The corrected label, equal to the current absolute sign XOR the rule output, "
                    + "changes sign over one period. Hence some adjacent corrected labels differ. "
                    + "This is exactly a transport defect of the same rule, and the integer sum of "
                    + "defect indicators in each period is at least one. The statement is pointwise; "
                    + "it does not identify or average a probability law."))),
                DescribeRole.Theorem))));
}
