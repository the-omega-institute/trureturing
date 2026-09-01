using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TruncatedTensorHopfDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/TruncatedTensorHopf.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor flip characterizes the group-like degree-two equation and preserves chronological Chen products.",
        H("Truncated Tensor Group-Like Laws"),
        Blocks(
            Def("flip", "tensorFlip", "Tensor-square flip",
                "The canonical linear involution exchanges the two tensor factors."),
            Def("group-like", "IsStepTwoGroupLike", "Doubled group-like equation",
                "A signature is group-like through degree two when its symmetric tensor part equals twice the pure square of degree one."),
            Thm("flip-involutive", "tensor_flip_involutive", "Tensor flip is involutive",
                "Applying the canonical flip twice recovers every tensor."),
            Thm("event-group-like", "event_tensor_signature_isStepTwoGroupLike", "Single events are group-like",
                "The pure square carried by one event satisfies the doubled group-like equation."),
            Thm("mul-group-like", "isStepTwoGroupLike_mul", "Chen multiplication preserves group-like signatures",
                "The group-like equation is closed under the ordered degree-two Chen product."),
            Thm("word-group-like", "chronological_tensor_signature_isStepTwoGroupLike", "Chronological words are group-like",
                "Every finite event word inherits the group-like equation from its single-event factors."),
            Thm("symmetric-part", "chronological_tensor_signature_symmetric_part", "Word symmetric part is fixed by degree one",
                "For every word, tensor degree one determines the complete symmetric part of doubled degree two.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/TruncatedTensorSignature")),
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
