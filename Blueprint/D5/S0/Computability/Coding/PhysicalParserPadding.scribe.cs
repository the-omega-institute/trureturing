using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class PhysicalParserPaddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ruler-first physical padding sweep with exact retained digits and a four-head rewind.",
        H("Physical Buffer Padding"),
        Blocks(
            Paragraph(Text(
                "The finite padding subroutine moves each component head separately, checks "
                    + "the ruler before the selected buffer, preserves occupied digits, and "
                    + "writes an occupied zero only into a blank buffer cell.")),
            Describe.Lean(
                DescribeId.Create("pad-one"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PhysicalParserPadding.pad_one"),
                H("A complete sweep with its literal frame"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every selected field, natural width W, initial Boolean word of "
                            + "length at most W, and arbitrary other memory and head frame, "
                            + "the actual routine enters with its four selected heads at home "
                            + "and returns with the same ruler and the original word followed "
                            + "by exactly enough zeros to occupy W cells. All four selected "
                            + "heads return to zero; the finite continuation selects the next "
                            + "field or halts after the sixth field.")),
                    Paragraph(Text(
                        "The time is at most fourteen times W plus eleven elementary actions. "
                            + "Every intermediate step preserves the fourteen other tapes and "
                            + "their heads, and preserves every ruler cell. Each selected head "
                            + "lies between zero and W + 1. The successor at W + 1 remains "
                            + "blank. The proof includes separate component moves, partial "
                            + "writes, scanning existing digits, extending padding and the "
                            + "unbounded physical rewind."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This phase contract supplies padding after the coupled source rewind. "
                    + "PhysicalParserExecution composes the full run and its storage bound. "
                    + "The later arithmetic initializer and executor remain separate obligations."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PhysicalSixParser"))]));
}
