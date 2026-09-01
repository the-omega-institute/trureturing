using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TimeOrderedMemoryMatrixRepresentationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/TimeOrderedMemoryMatrixRepresentation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Time-ordered affine memory evolution is exactly an upper-triangular matrix representation of chronological words.",
        H("Time-Ordered Memory Matrix Representation"),
        Blocks(
            Def("event-matrix", "timedPrimeUpdateMatrix", "One-event update matrix",
                "A timed event is represented by a two-by-two upper-triangular matrix acting on memory and scalar coordinates."),
            Def("word-matrix", "timeOrderedMemoryMatrix", "Chronological word matrix",
                "The matrix of a word is the reverse ordered product because the head event acts first on a column state."),
            Thm("event-action", "timed_prime_update_matrix_mulVec", "Matrix action equals the affine update",
                "Multiplying the encoded state by the event matrix reproduces the frozen timed memory update."),
            Thm("append", "time_ordered_memory_matrix_append", "Word append is reversed matrix multiplication",
                "The earlier word acts first, so concatenation maps to the later matrix multiplied by the earlier matrix."),
            Thm("entries", "time_ordered_memory_matrix_entries", "Exact triangular cocycle entries",
                "The chronological matrix contains the stable power, memory cocycle, zero lower-left entry, and scalar cocycle."),
            Thm("memory-entry", "time_ordered_memory_matrix_zero_one", "Memory is the upper-right entry",
                "The frozen time-ordered memory cocycle is exactly the upper-right matrix coefficient."),
            Thm("matrix-action", "time_ordered_memory_matrix_mulVec", "Word matrix realizes full evolution",
                "The complete matrix product acts exactly as the frozen chronological affine evolution.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
