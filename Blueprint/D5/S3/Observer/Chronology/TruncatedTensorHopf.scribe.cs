using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TruncatedTensorHopfDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/TruncatedTensorHopf.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The degree-two group-like equation is multiplicative, and its logarithmic coordinate is exactly flip-primitive.",
        H("Truncated Tensor Hopf Laws"),
        Blocks(
            Item("flip", "tensorFlip", "Tensor-factor flip",
                "The tensor flip exchanges the two degree-one factors.", DescribeRole.Definition),
            Item("flip-involutive", "tensor_flip_involutive", "Tensor flip is involutive",
                "Applying the factor flip twice recovers every degree-two tensor.", DescribeRole.Theorem),
            Item("group-like", "IsStepTwoGroupLike", "Step-two group-like equation",
                "A normalized doubled signature is group-like through degree two when its degree-two tensor plus its flip equals twice the pure square of degree one.", DescribeRole.Definition),
            Item("primitive", "IsStepTwoPrimitive", "Step-two primitive equation",
                "A degree-two logarithmic tensor is primitive precisely when flipping it negates it.", DescribeRole.Definition),
            Item("event-group-like", "event_isStepTwoGroupLike", "One-event group-like law",
                "Every pure one-event tensor signature satisfies the degree-two group-like equation.", DescribeRole.Theorem),
            Item("mul-group-like", "isStepTwoGroupLike_mul", "Group-like multiplication closure",
                "Chen multiplication preserves the degree-two group-like equation.", DescribeRole.Theorem),
            Item("word-group-like", "chronological_tensor_signature_isStepTwoGroupLike", "Chronological words are group-like",
                "Every finite chronological tensor word satisfies the degree-two group-like equation.", DescribeRole.Theorem),
            Item("group-to-primitive", "groupLike_implies_magnus_primitive", "Group-like logarithms are primitive",
                "The group-like equation forces the doubled Magnus coordinate to be antisymmetric under tensor flip.", DescribeRole.Theorem),
            Item("primitive-to-group", "magnus_primitive_implies_groupLike", "Primitive logarithms recover group-likeness",
                "Flip-primitivity of the doubled logarithm reconstructs the degree-two group-like equation.", DescribeRole.Theorem),
            Item("equivalence", "groupLike_iff_magnus_primitive", "Group-like and primitive equivalence",
                "A step-two signature is group-like exactly when its doubled logarithmic coordinate is flip-primitive.", DescribeRole.Theorem),
            Item("word-primitive", "chronological_tensor_magnus_isStepTwoPrimitive", "Chronological Magnus coordinates are primitive",
                "The doubled tensor Magnus coordinate of every finite event word is primitive through degree two.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/TruncatedTensorSignature")),
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
