using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class ArchiveRecordEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Legal finite graph records reconstruct full causal archives and preserve their time constraints.",
        H("Legal Archive Records"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("archive-record-reconstruction-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_record_equiv"),
                H("Archive fields are exactly recoverable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Record legality requires a total single-valued attribute graph, a relation whose endpoints "
                    + "are archived, irreflexivity, transitivity and strict increase of decoded integer time. "
                    + "Reconstruction uses the unique graph values to recover each dependent attribute function."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("archive-hf-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/ArchiveRecordEncoding.archive_code_equiv"),
                H("Literal HF tuples have an independent legality predicate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The record becomes a Kuratowski tuple of the event set, attribute graph and causal graph. "
                    + "Its grammar is specified directly on those components. Encoding and decoding are inverse "
                    + "on every legal record, so code equality reflects complete archive equality. "
                    + "Current regions remain a separate component of the context representation."))),
                DescribeRole.Definition))));
}
