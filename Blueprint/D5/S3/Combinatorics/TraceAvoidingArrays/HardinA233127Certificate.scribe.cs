using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127RowsDocument;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233127CertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact square-strip transition counts from scanner fibres.",
        H("The single-row transition certificate"),
        Blocks(Describe.Lean(DescribeId.Create("rows"), DeclarationHandle.Create(
            "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233127Certificate.row_counts"),
            H("Every valid scanner boundary"), StatementSource.FromAuthor(Disp(RowCounts())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Automata/hardin2013a233127")),
            Blocks(Paragraph(Text(
                "The theorem is D5.S3.Combinatorics.TraceAvoidingArrays."
                + "HardinA233127SquareStrip.row_counts. Exact scanner fibres reduce each "
                + "continuation count to label rows, preserving individual colour "
                + "multiplicities and order constraints. The private proofs cover the 96 "
                + "completed and two unseen valid boundaries. This public interface is "
                + "consumed by finite_certificate in the square-strip recurrence module."))),
            DescribeRole.Theorem))));
}
