using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TruncatedTensorSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/TruncatedTensorSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree-two tensor signatures carry Chen multiplication and finite chronological word signatures.",
        H("Truncated Tensor Chronological Signature"),
        Blocks(
            Def("tensor-signature", "TensorSignature", "Doubled tensor signature",
                "A normalized step-two signature stores degree one together with twice tensor degree two."),
            Def("compose", "TensorSignature.compose", "Step-two Chen multiplication",
                "Composition adds degree one and inserts twice the ordered cross tensor at degree two."),
            Def("event", "eventTensorSignature", "Single-event tensor signature",
                "One event contributes its value in degree one and its pure square tensor in doubled degree two."),
            Def("word", "chronologicalTensorSignature", "Chronological tensor word signature",
                "A finite event list is folded in operational order using the Chen product."),
            Thm("append", "chronological_tensor_signature_append", "Tensor Chen append identity",
                "The signature of an earlier word followed by a later word is the product of their tensor signatures."),
            Thm("degree-one", "chronological_tensor_signature_degree_one", "Degree one is the event sum",
                "The first tensor degree forgets chronology and equals the ordinary sum of observed event values."),
            Thm("two-events", "chronological_tensor_signature_two_events", "Two-event ordered cross tensor",
                "The degree-two coordinate of two events contains the ordered cross tensor with coefficient two.")),
        []));

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
