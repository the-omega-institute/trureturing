using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoFreeLieBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepTwoFreeLieBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree-two chronological orientation is the universal free-Lie bracket and maps to every interpreted Lie commutator.",
        H("Step-Two Free-Lie Bridge"),
        Blocks(
            Def("degree-two", "freeLieDegreeTwo", "Universal degree-two free-Lie word",
                "An ordered event pair is sent to the bracket of its two free-Lie generators."),
            Thm("swap", "free_lie_degree_two_swap", "Free-Lie orientation reversal",
                "Exchanging the two events negates their universal degree-two bracket."),
            Thm("self", "free_lie_degree_two_self", "Repeated events have zero bracket",
                "The free-Lie degree-two word of one event with itself vanishes."),
            Thm("lift", "free_lie_degree_two_lift", "Universal lift preserves the bracket",
                "Every Lie-algebra interpretation sends the universal event bracket to the corresponding interpreted bracket."),
            Thm("orientation", "tensor_and_free_lie_swap_orientation", "Tensor and free-Lie orientations agree",
                "The tensor alternant and free-Lie bracket both reverse sign under the same event exchange."),
            Thm("zero", "free_lie_degree_two_lift_eq_zero_of_bracket_eq_zero", "Commuting interpretations annihilate degree two",
                "If the interpreted bracket vanishes, the universal degree-two free-Lie word maps to zero.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/PrimitiveMagnusLog")),
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
