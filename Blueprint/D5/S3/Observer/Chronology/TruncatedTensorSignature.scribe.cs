using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TruncatedTensorSignatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Chronology/TruncatedTensorSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite event words carry a division-free degree-two tensor signature satisfying Chen concatenation.",
        H("Truncated Tensor Signature"),
        Blocks(
            Entry("step-two-tensor-signature", "StepTwoTensorSignature",
                "Step-two tensor signature",
                "A degree-one module element is stored together with twice its degree-two tensor coordinate.", DescribeRole.Definition),
            Entry("compose", "StepTwoTensorSignature.compose",
                "Chronological tensor composition",
                "Composition adds degree one and inserts two copies of the ordered cross tensor.", DescribeRole.Definition),
            Entry("event", "eventTensorSignature",
                "One-event tensor signature",
                "One event contributes its value at degree one and its pure square tensor at doubled degree two.", DescribeRole.Definition),
            Entry("word", "chronologicalTensorSignature",
                "Chronological word tensor signature",
                "A finite event list is folded in operational order using the tensor signature product.", DescribeRole.Definition),
            Entry("append", "chronological_tensor_signature_append",
                "Chen append identity",
                "The signature of an earlier word followed by a later word is the product of their signatures.", DescribeRole.Theorem),
            Entry("degree-one", "chronological_tensor_signature_degree_one",
                "Degree-one projection",
                "The degree-one coordinate is the ordinary sum of all observed event values.", DescribeRole.Theorem),
            Entry("two-events", "chronological_tensor_signature_two_events",
                "Two-event expansion",
                "The exact two-event signature exposes the two ordered cross tensors.", DescribeRole.Theorem)),
        []));

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
