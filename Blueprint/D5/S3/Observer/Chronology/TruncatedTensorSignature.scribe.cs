using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class TruncatedTensorSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/TruncatedTensorSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree-one and doubled degree-two tensors form the universal step-two Chen signature with an alternating Magnus coordinate.",
        H("Truncated Tensor Signature"),
        Blocks(
            Item("tensor-signature", "TensorSignature", "Step-two tensor signature",
                "The carrier stores degree one in the event module and doubled degree two in its tensor square.", DescribeRole.Definition),
            Item("twice-tensor", "twiceTensor", "Division-free tensor doubling",
                "A tensor is doubled by adding it to itself, so no inverse of two is required.", DescribeRole.Definition),
            Item("event-signature", "eventTensorSignature", "One-event tensor signature",
                "One event contributes its value at degree one and its pure tensor square at doubled degree two.", DescribeRole.Definition),
            Item("word-signature", "chronologicalTensorSignature", "Chronological tensor word signature",
                "A finite event word is evaluated by composing one-event tensor signatures in operational order.", DescribeRole.Definition),
            Item("chen-append", "chronological_tensor_signature_append", "Tensor Chen append identity",
                "The signature of an earlier word followed by a later word is the chronological product of their signatures.", DescribeRole.Theorem),
            Item("degree-one", "chronological_tensor_signature_degree_one", "Degree-one event sum",
                "The degree-one coordinate is the ordinary sum of all observed event values.", DescribeRole.Theorem),
            Item("tensor-commutator", "tensorCommutator", "Alternating tensor commutator",
                "The universal second-order orientation is the difference of the two ordered pure tensors.", DescribeRole.Definition),
            Item("tensor-magnus", "doubledTensorMagnus", "Doubled tensor Magnus coordinate",
                "Subtracting the pure square of degree one from doubled degree two extracts the alternating logarithmic coordinate.", DescribeRole.Definition),
            Item("magnus-product", "doubled_tensor_magnus_mul", "Universal degree-two BCH law",
                "The tensor Magnus coordinate of a product is the sum of the two coordinates plus their alternating tensor commutator.", DescribeRole.Theorem),
            Item("event-zero", "doubled_tensor_magnus_event_eq_zero", "One-event logarithmic vanishing",
                "A single event has no alternating degree-two chronological memory.", DescribeRole.Theorem),
            Item("two-event", "doubled_tensor_magnus_two_events", "Two-event tensor commutator",
                "The logarithmic coordinate of two events is exactly their alternating tensor commutator.", DescribeRole.Theorem),
            Item("two-event-swap", "doubled_tensor_magnus_two_events_swap", "Two-event orientation reversal",
                "Reversing two events negates the tensor Magnus coordinate.", DescribeRole.Theorem),
            Item("symmetric-zero", "doubled_tensor_magnus_two_events_eq_zero_of_tmul_commute", "Tensor-symmetric collapse",
                "When the two ordered pure tensors agree, the degree-two chronological defect vanishes.", DescribeRole.Theorem)),
        []));

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
