using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class PhysicalParserExecutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete physical six-field parser returns an exact frame with uniform time and storage bounds.",
        H("Physical Parser Execution and Resources"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parser-frame-resources"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PhysicalParserExecution.parser_frame_resources"),
                H("Actual run, exact frame and every intermediate charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are fixed positive natural constants C_T and C_S before all "
                            + "six source parameters P, A, R, B, E and C. For every positive "
                            + "choice satisfying 2P < A and 2R < B, let q concatenate their "
                            + "six unary-header codewords, let s be its bit length and let "
                            + "W = s + 1. The actual elementary run from raw q, eighteen "
                            + "heads at zero and blank work tapes reaches the exact returned "
                            + "configuration after some T actions.")),
                    Paragraph(Text(
                        "The program pays for nine origin-marker writes. Header ones create "
                            + "placeholders; source payload n.bits.reverse is copied backwards "
                            + "to n.bits. Every header, delimiter and payload bit moves the "
                            + "source once and physically updates both tallies. One final "
                            + "CountOne adds the extra unit without source movement. The "
                            + "coupled source/ruler rewind parks those heads before six "
                            + "ruler-first padding sweeps. Termination is after field six, "
                            + "without an end-of-file test or supplied length register.")),
                    Paragraph(Text(
                        "At return, every head is zero and the raw source is preserved. "
                            + "Each parameter pair contains exactly its canonical little-endian "
                            + "bits followed by occupied zeros through W, with the successor "
                            + "and all further cells blank. The ruler contains W marks and "
                            + "the binary counter contains canonical W. Each source parameter "
                            + "is strictly less than 2 to the power W.")),
                    Paragraph(Text(
                        "Time is at most C_T times (s + 1) squared. Every intermediate "
                            + "configuration has total charge at most C_S times (s + 1), "
                            + "and every head lies between zero and s + 3. Charge counts all "
                            + "initial source cells including zeros, all origins, the union "
                            + "of every earlier visited cell even if blank or erased, all "
                            + "eighteen signed terminated unary head descriptions, finite "
                            + "control and the whole fixed program encoding. The proof "
                            + "witnesses C_T = 256 and C_S equal to the program-description "
                            + "length plus the number of controls plus 198.")),
                    Paragraph(Text(
                        "The same theorem proves that the signed head descriptions are "
                            + "prefix-free, including negative addresses. For every raw "
                            + "Boolean input and every number of steps, even outside the "
                            + "valid-input contract, the source companion head remains at "
                            + "zero and every raw source cell remains unchanged. Coordinates, "
                            + "lengths and visited histories are proof data inaccessible to "
                            + "the fixed finite control."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The returned frame proves input capacity. Arithmetic definitions D and H, "
                    + "the comparison 4EA versus CD, u/v and m, denominator positivity, "
                    + "intermediate arithmetic widths, multiplication, division and the "
                    + "complete initializer and executor remain outside this theorem. "
                    + "Preservation of this eighteen-tape frame by a later divider requires "
                    + "its own paid composition proof."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PhysicalParserField")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PhysicalParserPadding"))]));
}
