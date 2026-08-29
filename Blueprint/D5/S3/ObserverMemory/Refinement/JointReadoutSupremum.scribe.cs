using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class JointReadoutSupremumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/Refinement/JointReadoutSupremum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A paired readout has the intersection kernel and is the least common refinement of its two coordinates.",
        H("Joint Readout Supremum"),
        Blocks(
            Theorem(
                "pair-readout-kernel",
                "pair_readout_kernel",
                "Pair Readout Kernel",
                "Equality under the joint readout is exactly equality under both component readouts.",
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
