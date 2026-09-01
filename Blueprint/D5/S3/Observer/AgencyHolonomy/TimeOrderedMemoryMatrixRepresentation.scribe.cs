using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class TimeOrderedMemoryMatrixRepresentationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The time-ordered scalar and memory cocycles are exactly the diagonal and upper-right entries of a two-dimensional chronological matrix representation.",
        H("Time-Ordered Memory Matrix Representation"),
        Blocks(
            Item("state-vector", "stateVector", "Two-coordinate state vector",
                "The affine memory and scalar state pair is encoded as a two-coordinate column vector.", DescribeRole.Definition),
            Item("event-matrix", "timedEventMatrix", "Timed event matrix",
                "A timed memory event acts by an upper-triangular complex matrix carrying stable transport, Fourier-twisted injection, and the local scalar factor.", DescribeRole.Definition),
            Item("summary-matrix", "memorySummaryMatrix", "Chronological summary matrix",
                "A finite word is summarized by stable power, memory cocycle, and scalar cocycle in one upper-triangular matrix.", DescribeRole.Definition),
            Item("singleton", "memory_summary_matrix_singleton", "One-event matrix realization",
                "The summary matrix of a singleton word is exactly its local event matrix.", DescribeRole.Theorem),
            Item("matrix-action", "memory_summary_matrix_mulVec", "Matrix action equals affine evolution",
                "Matrix-vector multiplication by the summary matrix exactly realizes the frozen time-ordered affine evolution.", DescribeRole.Theorem),
            Item("append", "memory_summary_matrix_append", "Chronological matrix multiplication",
                "An earlier word followed by a later word is represented by the later summary matrix multiplied by the earlier summary matrix.", DescribeRole.Theorem),
            Item("append-action", "memory_summary_matrix_append_mulVec", "Sequential matrix action",
                "The matrix append law acts on state vectors as sequential time-ordered transport.", DescribeRole.Theorem),
            Item("upper-right", "memory_summary_matrix_upper_right", "Memory cocycle entry",
                "The upper-right summary entry is the time-ordered memory cocycle.", DescribeRole.Theorem),
            Item("lower-right", "memory_summary_matrix_lower_right", "Scalar cocycle entry",
                "The lower-right summary entry is the scalar cocycle.", DescribeRole.Theorem),
            Item("upper-left", "memory_summary_matrix_upper_left", "Stable transport entry",
                "The upper-left summary entry is the stable factor raised to the word length.", DescribeRole.Theorem),
            Item("commutator", "timed_event_matrix_commutator_upper_right", "Matrix commutator curvature",
                "The upper-right entry of the two-event matrix commutator is exactly the frozen prime swap curvature.", DescribeRole.Theorem),
            Item("swap", "memory_summary_matrix_two_event_swap", "Summary swap curvature",
                "Swapping two events changes the upper-right summary entry by the same prime swap curvature.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle")),
        ]));

    private static DocumentBlock.Describe Item(
        string id, string declaration, string heading,
        string paragraph, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);
}
