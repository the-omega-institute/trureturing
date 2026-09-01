using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimitiveMagnusLogDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Chronology/PrimitiveMagnusLog.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The degree-two logarithm of a group-like tensor signature is antisymmetric and obeys the truncated tensor BCH law.",
        H("Primitive Magnus Logarithm"),
        Blocks(
            Entry("commutator", "tensorCommutator",
                "Tensor commutator",
                "The degree-two Lie generator is the antisymmetric tensor x tensor y minus y tensor x.", DescribeRole.Definition),
            Entry("magnus", "doubledPrimitiveMagnus",
                "Doubled primitive Magnus coordinate",
                "Subtracting the square tensor of degree one removes the symmetric group-like component.", DescribeRole.Definition),
            Entry("primitive", "doubledPrimitiveMagnus_antisymmetric",
                "Primitive antisymmetry",
                "The logarithmic degree-two coordinate of a group-like signature changes sign under tensor-leg exchange.", DescribeRole.Theorem),
            Entry("bch", "doubledPrimitiveMagnus_mul",
                "Tensor BCH law",
                "The logarithm of a Chen product adds the two logarithms and the tensor commutator of degree one.", DescribeRole.Theorem),
            Entry("append", "doubledPrimitiveMagnus_append",
                "Chronological BCH append law",
                "Chen concatenation becomes the degree-two tensor BCH identity after applying the primitive logarithm.", DescribeRole.Theorem),
            Entry("two-events", "doubledPrimitiveMagnus_two_events",
                "Two-event primitive coordinate",
                "The two-event logarithmic coordinate is exactly the tensor commutator.", DescribeRole.Theorem),
            Entry("swap", "doubledPrimitiveMagnus_two_events_swap",
                "Two-event orientation reversal",
                "Reversing two events negates the primitive degree-two coordinate.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/TruncatedTensorHopf"))
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
