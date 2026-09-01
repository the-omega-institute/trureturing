using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class TimeOrderedMemoryMatrixRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryMatrixRepresentation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Time-ordered prime memory cocycles are exactly the upper-right entries of finite upper-triangular matrix transports.",
        H("Time-Ordered Memory Matrix Representation"),
        Blocks(
            Entry("event-matrix", "timedEventMatrix",
                "Timed event matrix",
                "One timed event is represented by an upper-triangular two-by-two complex matrix.", DescribeRole.Definition),
            Entry("word-matrix", "timeOrderedWordMatrix",
                "Chronological word matrix",
                "The matrix of a finite event word multiplies later event matrices on the left.", DescribeRole.Definition),
            Entry("event-action", "timedEventMatrix_mulVec",
                "One-event action",
                "Matrix-vector action agrees exactly with the frozen affine timed-prime update.", DescribeRole.Theorem),
            Entry("append", "timeOrderedWordMatrix_append",
                "Matrix append law",
                "Concatenating event words reverses matrix multiplication order for column-vector action.", DescribeRole.Theorem),
            Entry("closed-form", "timeOrderedWordMatrix_closed_form",
                "Exact upper-triangular closed form",
                "The diagonal entries are the stable power and scalar cocycle, while the upper-right entry is the memory cocycle.", DescribeRole.Theorem),
            Entry("upper-right", "timeOrderedWordMatrix_upperRight",
                "Memory is the upper-right entry",
                "Reading matrix coordinate zero-one recovers the frozen time-ordered memory cocycle.", DescribeRole.Theorem),
            Entry("evolution", "timeOrderedWordMatrix_mulVec",
                "Word matrix represents evolution",
                "The complete word matrix acts exactly as the frozen list evolution on every state.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle"))
        ]));

    private static DocumentBlock.Describe Entry(
        string id, string declaration, string heading, string paragraph,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);
}
