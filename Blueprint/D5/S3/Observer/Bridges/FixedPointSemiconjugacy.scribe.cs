using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class FixedPointSemiconjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Bridges/FixedPointSemiconjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semiconjugate bridges transport fixed points and stable fibers.",
        H("Fixed Point Semiconjugacy"),
        Blocks(
            Theorem(
                "fixed-point-maps",
                "fixed_point_maps",
                "Fixed Point Maps",
                "A fixed point is transported through every semiconjugate bridge.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-point-reflects-of-injective",
                "fixed_point_reflects_of_injective",
                "Fixed Point Reflects Of Injective",
                "An injective semiconjugate bridge also reflects fixed points.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-point-iff-of-injective",
                "fixed_point_iff_of_injective",
                "Fixed Point iff Of Injective",
                "Under an injective semiconjugacy, fixedness is exactly preserved.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "observation-fiber-forward-invariant",
                "observation_fiber_forward_invariant",
                "Observation Fiber Forward Invariant",
                "Equality under the observer remains equal after one semiconjugate step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "semiconjugacy-iterate",
                "semiconjugacy_iterate",
                "Semiconjugacy Iterate",
                "Semiconjugacy transports every finite iterate, not only one step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-point-maps-across-composite",
                "fixed_point_maps_across_composite",
                "Fixed Point Maps Across Composite",
                "Fixed-point transport composes along two observer bridges.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}
