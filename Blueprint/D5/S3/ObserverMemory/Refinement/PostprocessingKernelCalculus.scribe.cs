using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class PostprocessingKernelCalculusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Postprocessing enlarges readout kernels, with equality exactly on injective realized postprocessing and strictness witnessed by a realized collision.",
        H("Postprocessing Kernel Calculus"),
        Blocks(
            Theorem(
                "postprocessing-kernel-le",
                "postprocessing_kernel_le",
                "Postprocessing Kernel le",
                "Deterministic postprocessing can only enlarge the equality kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "postprocessing-kernel-eq-iff-inj-on-range",
                "postprocessing_kernel_eq_iff_injOn_range",
                "Postprocessing Kernel eq iff Inj On Range",
                "Postprocessing preserves exactly the original kernel iff it is injective on values that the original readout actually realizes.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "postprocessing-strict-iff-range-collision",
                "postprocessing_strict_iff_range_collision",
                "Postprocessing Strict iff Range Collision",
                "Kernel growth is strict exactly when two realized readout values are separated before postprocessing and collide afterwards.",
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
