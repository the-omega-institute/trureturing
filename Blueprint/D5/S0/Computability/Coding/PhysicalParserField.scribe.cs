using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class PhysicalParserFieldDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A raw header and payload are physically parsed with one paid tally increment per bit.",
        H("Physical Field Parsing"),
        Blocks(
            Paragraph(Text(
                "The source supplies a unary length header, a zero delimiter and a "
                    + "most-significant-bit-first payload. Header ones create occupied zero "
                    + "placeholders. The payload loop writes backwards into those cells; "
                    + "the resulting physical word is the reversed payload. Lengths and "
                    + "coordinates in the statement are proof data, unavailable to control.")),
            Describe.Lean(
                DescribeId.Create("parse-field"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/PhysicalParserField.parse_field"),
                H("One field with synchronized physical tallies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every field i, consumed prefix length n, Boolean payload of "
                            + "length L, bound N at least n + 2L + 1, and literal surrounding "
                            + "memory and head frame, assume only that the raw source cells "
                            + "at the next 2L + 1 positions contain the stated header, delimiter "
                            + "and payload. From an empty buffer and equal tallies n, the "
                            + "actual run returns with the reversed payload, both buffer heads "
                            + "home, raw head n + 2L + 2 and both tallies n + 2L + 1.")),
                    Paragraph(Text(
                        "The finite continuation enters the next field or the final extra "
                            + "CountOne after field six. Time is at most (2L + 1)(8N + 20) + 2 "
                            + "elementary actions. Every intermediate raw, selected-buffer "
                            + "and tally head lies between zero and N + 1. Source cells, "
                            + "unused tapes and unused heads are unchanged. Each header bit, "
                            + "delimiter and payload bit physically moves the source once "
                            + "and calls the proved tally routine once."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Canonical source payloads are n.bits.reverse, so this physical reversal "
                    + "produces n.bits. PhysicalParserExecution composes initialization, six "
                    + "field calls, the final extra tick, rewind and padding, and accounts "
                    + "for every earlier visited cell. Later arithmetic remains outside the parser."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PhysicalParserTally"))]));
}
