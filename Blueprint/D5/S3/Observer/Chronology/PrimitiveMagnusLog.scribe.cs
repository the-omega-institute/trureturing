using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimitiveMagnusLogDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimitiveMagnusLog.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subtracting the tensor square of degree one extracts the primitive alternating Magnus coordinate.",
        H("Primitive Degree-Two Magnus Logarithm"),
        Blocks(
            Def("bracket", "tensorLieBracket", "Universal tensor bracket",
                "The alternating tensor of two vectors is their ordered pure tensor minus the reversed pure tensor."),
            Def("magnus", "doubledPrimitiveMagnus", "Doubled primitive Magnus coordinate",
                "The tensor square of degree one is removed from doubled degree two."),
            Def("alternating", "IsAlternatingTensor", "Alternating tensor condition",
                "A degree-two tensor is alternating when tensor flip sends it to its additive inverse."),
            Thm("bracket-swap", "tensor_lie_bracket_swap", "Bracket orientation reversal",
                "Exchanging the two vector inputs negates the tensor bracket."),
            Thm("flip-bracket", "tensor_flip_lie_bracket", "Tensor flip negates the bracket",
                "The universal bracket lies in the anti-invariant subspace of tensor flip."),
            Thm("bch", "doubled_primitive_magnus_mul", "Tensor BCH law",
                "The logarithm of a Chen product is the sum of the two logarithms plus the cross bracket."),
            Thm("primitive", "doubled_primitive_magnus_alternating", "Group-like implies primitive alternating",
                "The finite group-like equation forces the doubled Magnus coordinate to be anti-invariant under tensor flip."),
            Thm("two-events", "doubled_primitive_magnus_two_events", "Two events give their bracket",
                "The primitive logarithm of a two-event chronology is exactly the tensor Lie bracket."),
            Thm("append", "doubled_primitive_magnus_append", "Chronological tensor BCH append law",
                "Word concatenation transports Chen multiplication to the degree-two tensor BCH formula."),
            Thm("word-alternating", "chronological_primitive_magnus_alternating", "Every word logarithm is alternating",
                "Every finite chronological tensor signature has a primitive anti-invariant degree-two logarithm.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/TruncatedTensorHopf")),
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
