using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class MatrixUnitDecoderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices and realizes normalized logical instruments. No global bundle or Chern-number claim is made.",
        H("MatrixUnitDecoder"),
        Blocks(new[]
        {
            "unit_support_projection",
            "unit_support_action",
            "decoder_kraus_gram",
            "decoder_trace_pairing",
            "matrix_unit_decoder_channel",
            "commutant_trace_pairing",
            "represented_matrix_mul",
            "represented_matrix_star",
            "decoder_recovers_commutant_weight",
            "represented_instrument_normalized"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/MatrixUnitDecoder." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/benykempfkribs2007observables"), LibraryNoteRef.Create("D5/L/choijohnstonkribs2009multiplicative")),
            Blocks(Paragraph(Text("Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices and realizes normalized logical instruments. No global bundle or Chern-number claim is made."))),
            DescribeRole.Theorem)).ToArray())));
}
