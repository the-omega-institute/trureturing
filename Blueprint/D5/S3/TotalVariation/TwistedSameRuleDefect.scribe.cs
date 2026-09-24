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
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural period L with L > 0, every base sign word v : Fin L -> Bool, every "
                    + "natural window length R, and every deterministic table f : (Fin R -> Bool) -> Bool, "
                    + "extend v by complementing its absolute sign after each turn of length L. The resulting "
                    + "relation bits are L-periodic. Apply the same table f to each adjacent R-bit relation "
                    + "window. The defect at t is the XOR of the outputs at t+1 and t with the complement of "
                    + "the relation bit at t+R. Then the defect is true at some t < L, and the sum over "
                    + "t in range L of its zero-one defect indicator is at least one. This is a pointwise "
                    + "statement for the fixed word and rule; it asserts no probability law."))),
                DescribeRole.Theorem))));
}
