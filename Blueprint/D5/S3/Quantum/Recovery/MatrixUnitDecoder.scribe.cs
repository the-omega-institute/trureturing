using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class MatrixUnitDecoderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made.",
        H("MatrixUnitDecoder"),
        Blocks(new[]
        {
            "decoder_kraus_gram",
            "decoder_trace_pairing",
            "matrix_unit_decoder_channel",
            "represented_matrix_mul",
            "decoder_recovers_commutant_weight"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/MatrixUnitDecoder." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/benykempfkribs2007observables"), LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
            Blocks(Paragraph(Text(name == "decoder_recovers_commutant_weight"
                ? "The original weighted_pairing proof is public at its original owner and remains used by decoder_recovers_commutant_weight. Matrix-unit multiplication, commutation of Q with every F(i,j), and trace(F(v,v) Q)=1 give trace(F(j,i) Q representedMatrix(F,A))=A(i,j). The proof and hypotheses are unchanged; this exposure adds no mathematical content. This owner result supplies no normalized physical instrument, syndrome holonomy, generator norm bound, or adaptive protocol law."
                : "Actual matrix units construct the full decoder without a syndrome basis. Its trace-pairing formula recovers supported commutant-weighted logical matrices. No global bundle or Chern-number claim is made."))),
            DescribeRole.Theorem)).ToArray())));
}
