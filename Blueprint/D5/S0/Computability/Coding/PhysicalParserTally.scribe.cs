using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class PhysicalParserTallyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A physical unary append and canonical binary increment with every intermediate head charged.",
        H("Physical Tally Increment"),
        Blocks(
            Paragraph(Text(
                "CountOne is the shared tally subroutine of the eighteen-tape program. It "
                    + "moves the two unary heads separately, writes both components of the new "
                    + "mark, and then increments the binary pair by a ripple carry. The counter "
                    + "returns to its home marker before the finite continuation is selected.")),
            Describe.Lean(
                DescribeId.Create("count-one"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PhysicalParserTally.count_one"),
                H("Increment with a literal frame"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every memory frame, head frame, natural numbers u and n, and "
                            + "finite continuation, the actual routine starting with unary u at "
                            + "its end and canonical binary n at home returns with unary u + 1 "
                            + "and canonical binary n + 1. Its time is at most eight times the "
                            + "binary length of n plus fourteen elementary actions.")),
                    Paragraph(Text(
                        "At every intermediate step, all fourteen other tapes and their heads "
                            + "are unchanged. Each unary head remains between u and u + 1. Each "
                            + "binary head remains between zero and the old binary length plus "
                            + "one. The proof includes the empty counter, overflow, partial "
                            + "component writes, arbitrary carry length and the physical rewind. "
                            + "Equal initial tally values therefore give equal final values; "
                            + "equality is not assumed during the carry."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The routine keeps the raw source head parked. The surrounding parser must "
                    + "call CountOne exactly once per consumed bit and once more at the final "
                    + "boundary; those calls are established by the field and execution proofs."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PhysicalSixParser"))]));
}
