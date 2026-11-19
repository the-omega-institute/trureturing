using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParrySectionMarginalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero-bit marginals and shift dependence of the conditional Parry probability.",
        H("The zero-section probability under the original shift"),
        Blocks(Describe.Lean(
            DescribeId.Create("parry-section-zero-marginals"),
            DeclarationHandle.Create("D5/S3/TotalVariation/ParrySectionMarginals.section_zero_marginals"),
            H("The first two zero-bit probabilities"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Use the bilateral Parry law and its normalized restriction to the zero "
                    + "section. Write p for the reciprocal Perron root. The probability of a "
                    + "false bit at index zero is p, and the probability of a false bit at index "
                    + "one is 2 p^2. The original left shift does not preserve this probability.")),
                Paragraph(Text(
                    "The one-bit word 0 and each of the two-bit words 00 and 10 end in a reset. "
                    + "The conditional raw-window formula assigns them masses p, p^2 and p^2. "
                    + "The latter two cylinders are disjoint and exhaust the false-bit event at "
                    + "index one. Since p > 1/2, this event has strictly larger probability than "
                    + "the false-bit event at index zero whose preimage it is."))),
            DescribeRole.Theorem))));
}
