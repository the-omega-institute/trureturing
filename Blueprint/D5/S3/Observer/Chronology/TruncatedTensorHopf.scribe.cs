using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TruncatedTensorHopfDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Chronology/TruncatedTensorHopf.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree-two tensor signatures satisfy the exact group-like symmetry equation and are closed under Chen multiplication.",
        H("Truncated Tensor Group-Like Laws"),
        Blocks(
            Entry("flip", "tensorFlip",
                "Tensor-leg exchange",
                "The linear equivalence exchanges the two factors of the degree-two tensor product.", DescribeRole.Definition),
            Entry("group-like", "IsStepTwoGroupLike",
                "Degree-two group-like equation",
                "Doubled degree two plus its flipped tensor equals two copies of the square of degree one.", DescribeRole.Definition),
            Entry("event", "eventTensorSignature_isStepTwoGroupLike",
                "One-event group-like law",
                "Every pure one-event truncated exponential satisfies the degree-two group-like equation.", DescribeRole.Theorem),
            Entry("mul", "IsStepTwoGroupLike.mul",
                "Closure under Chen multiplication",
                "The degree-two group-like locus is preserved by chronological composition.", DescribeRole.Theorem),
            Entry("word", "chronologicalTensorSignature_isStepTwoGroupLike",
                "Every finite word is group-like",
                "Induction through Chen multiplication places every finite chronological tensor signature in the group-like locus.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/TruncatedTensorSignature"))
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
