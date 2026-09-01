using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoFreeLieBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepTwoFreeLieBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating tensor Magnus coordinate and the degree-two free Lie bracket have the same image in every associative algebra representation.",
        H("Step-Two Free Lie Bridge"),
        Blocks(
            Item("free-lie-word", "freeLieDegreeTwo", "Degree-two free Lie word",
                "An ordered generator pair determines the bracket of the corresponding free Lie generators.", DescribeRole.Definition),
            Item("free-lie-swap", "free_lie_degree_two_swap", "Free Lie orientation reversal",
                "Reversing the generator pair negates the degree-two free Lie word.", DescribeRole.Theorem),
            Item("free-lie-self", "free_lie_degree_two_self", "Repeated generator vanishing",
                "The bracket of a free generator with itself is zero.", DescribeRole.Theorem),
            Item("representation", "freeLieRepresentation", "Universal associative representation",
                "A map from generators into an associative algebra extends uniquely to a free Lie representation.", DescribeRole.Definition),
            Item("represented-bracket", "free_lie_representation_degree_two", "Represented free Lie commutator",
                "Every associative representation maps the degree-two free Lie word to the ordinary ring commutator.", DescribeRole.Theorem),
            Item("tensor-multiplication", "tensor_commutator_mul", "Tensor alternant multiplication",
                "The tensor multiplication map sends the alternating pure tensor to the same ring commutator.", DescribeRole.Theorem),
            Item("tensor-free-lie", "tensor_commutator_eq_free_lie_representation", "Tensor and free Lie compatibility",
                "The alternating tensor and free Lie bracket have identical images under every associative representation.", DescribeRole.Theorem),
            Item("magnus-free-lie", "represented_two_event_magnus_eq_free_lie", "Two-event Magnus is represented free Lie curvature",
                "The represented two-event tensor Magnus coordinate is exactly the image of the degree-two free Lie bracket.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/TruncatedTensorHopf")),
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
