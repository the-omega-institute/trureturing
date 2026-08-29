using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class WormholeKernelTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Bridges/WormholeKernelTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wormhole composition records exact observer-kernel loss.",
        H("Wormhole Kernel Transport"),
        Blocks(
            Theorem(
                "kernel-forward-invariant",
                "kernel_forward_invariant",
                "Kernel Forward Invariant",
                "The observation kernel of a wormhole is forward-invariant under the source dynamics.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "kernel-le-composite",
                "kernel_le_composite",
                "Kernel le Composite",
                "Postcomposing a wormhole can only enlarge its source observer kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "kernel-eq-composite-of-outer-injective",
                "kernel_eq_composite_of_outer_injective",
                "Kernel eq Composite Of Outer Injective",
                "An injective outer wormhole preserves the source observer kernel exactly.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strict-kernel-growth-of-outer-collision",
                "strict_kernel_growth_of_outer_collision",
                "Strict Kernel Growth Of Outer Collision",
                "A pair visible after the first bridge but collapsed by the second bridge witnesses strict growth of the composite kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strict-growth-refutes-outer-injectivity",
                "strict_growth_refutes_outer_injectivity",
                "Strict Growth Refutes Outer Injectivity",
                "Strict information loss through a composite refutes injectivity of the outer bridge.",
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
