using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoFreeLieBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Chronology/StepTwoFreeLieBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-event primitive tensor logarithm evaluates to the degree-two free-Lie bracket in every associative ring representation.",
        H("Step-Two Free-Lie Bridge"),
        Blocks(
            Entry("free-lie-degree-two", "freeLieDegreeTwo",
                "Formal degree-two free-Lie bracket",
                "Two event labels determine their bracket in the universal free Lie algebra over the integers.", DescribeRole.Definition),
            Entry("evaluation", "freeLieEvaluation",
                "Universal Lie evaluation",
                "An event observation in an associative ring extends to the unique free-Lie evaluation morphism.", DescribeRole.Definition),
            Entry("tensor-multiply", "tensorMultiply",
                "Tensor multiplication contraction",
                "The algebra multiplication map contracts an integral tensor of ring elements.", DescribeRole.Definition),
            Entry("evaluate-bracket", "freeLieEvaluation_degreeTwo",
                "Free-Lie evaluation is the ring commutator",
                "The universal evaluation sends the formal degree-two bracket to xy minus yx.", DescribeRole.Theorem),
            Entry("tensor-bracket", "tensorMultiply_tensorCommutator",
                "Tensor antisymmetry is the ring commutator",
                "Multiplication sends x tensor y minus y tensor x to the same commutator.", DescribeRole.Theorem),
            Entry("bridge", "chronological_primitive_eq_freeLie_evaluation",
                "Chronological primitive equals represented free Lie",
                "The represented primitive Magnus coordinate of a two-event word equals its evaluated free-Lie bracket.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/PrimitiveMagnusLog"))
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
