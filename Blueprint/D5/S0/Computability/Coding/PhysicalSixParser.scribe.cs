using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class PhysicalSixParserDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary bit instructions and the coupled source and ruler rewind.",
        H("Physical Six-Field Parser"),
        Blocks(
            Paragraph(Text(
                "The fixed program uses eighteen Boolean tapes in nine pairs. The first pair "
                    + "contains raw input and a parked origin companion. Six pairs retain the "
                    + "parameters; the final two pairs hold a unary ruler and a binary counter. "
                    + "Each transition performs one selected-tape read, write, or unit move. "
                    + "Only reads branch. All nine origin markers are written by the program.")),
            Paragraph(Text(
                "Header ones allocate occupied zero cells. Payload bits arrive most significant "
                    + "first and are copied backwards into little-endian buffers. Every consumed "
                    + "header, delimiter and payload bit calls the tally routine. A final extra "
                    + "tick constructs the common width before the source and ruler rewind.")),
            Describe.Lean(
                DescribeId.Create("coupled-source-rewind"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PhysicalSixParser.coupled_source_rewind"),
                H("Coupled rewind with a literal frame"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary physical memory and other head positions, suppose the "
                            + "ruler has its home marker at zero and occupied one marks through W. "
                            + "For every k at most W and B, starting the source and both ruler "
                            + "heads at k reaches the first padding control with all three heads "
                            + "zero after exactly 5k + 2 elementary actions.")),
                    Paragraph(Text(
                        "Every intermediate configuration preserves every memory cell and the "
                            + "other fifteen head positions. The source, ruler occupancy and ruler "
                            + "value heads remain ordered, nonnegative and at most B, with their "
                            + "maximum separation at most one. The two ruler reads precede three "
                            + "separate left moves; the home test uses two further reads."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Contract specifies the complete valid-input execution, exact padded return "
                    + "frame, uniform quadratic action bound and linear bound on every prefix's "
                    + "total charge. PhysicalParserExecution supplies its complete operational proof. "
                    + "The charge includes initial zero input cells, all origins, persistent visited "
                    + "cells, signed and terminated unary head descriptions, current finite "
                    + "control and the whole instruction table. These descriptions account for "
                    + "the sign and framing of each address without an assumed logarithmic label."))),
        []));
}
