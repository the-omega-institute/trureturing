using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class DyadicResetBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset decomposition of arbitrary legal words.",
        H("Reset decomposition of arbitrary legal words"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyadic-package-dyadicresetblocks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/DyadicResetBlocks.reset_decomposition"),
                H("Reset decomposition of arbitrary legal words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any label type, integer-valued step function f, and integer height M, suppose each step is positive or equals -M. Every list W satisfying InStrip(f,M,0,W) decomposes exactly as packets(P) followed by a positive tail T. Each packet consists of a positive physical list of mass M and its actual reset label of value -M. The tail has mass between zero and M. This is a conclusion from every-prefix legality; no block placement or arrival gate is a premise.")),
                    Paragraph(Text("The proof appends one actual label at a time. A positive label extends the tail. A reset is legal only when that tail has reached exactly M, and then closes a complete packet. Each complete packet has total zero. Positive monotonicity proves every interior prefix and the actual reset returns its endpoint to zero. Existing positive_block_strip is reused at its original owner."))),
                DescribeRole.Theorem)), []));
}
