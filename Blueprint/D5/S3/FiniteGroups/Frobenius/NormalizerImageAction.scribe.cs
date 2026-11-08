using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class NormalizerImageActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugation and faithful complement action on the actual image center.", H("Conjugation and faithful complement action on the actual image center."),
        Blocks(
            Paragraph(Text("The representation, image, image automorphisms and center action are constructed from the same operators on the original carrier. Semisimplicity and isotypy refer to the actual restricted group-algebra module. The algebra proof of Skolem-Noether is reused from AxiomMath/Stacks at revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. Neither faithfulness on the center nor an inner implementer is assumed.")),
            Describe.Lean(DescribeId.Create("normalizerimageaction-ambient-q"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/NormalizerImageAction.ambient_q"), H("ambient q"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Conjugating an actual operator agrees with applying normal-subgroup conjugation to its group-algebra input. The identity follows by group-algebra induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizerimageaction-alpha-subgroup-inner"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/NormalizerImageAction.alpha_subgroup_inner"), H("alpha subgroup inner"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("An element of the normal subgroup acts on the image by conjugation by its actual representation unit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizerimageaction-centeraction-subgroup"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/NormalizerImageAction.centerAction_subgroup"), H("centerAction subgroup"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The normal subgroup therefore acts trivially on the center."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalizerimageaction-complement-center-kernel-eq-bot"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/NormalizerImageAction.complement_center_kernel_eq_bot"), H("complement center kernel eq bot"), StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The simple image center is a field. If an element fixes it, Skolem-Noether supplies an inner implementer in the actual image. The Frobenius inner-action obstruction then forces that element into the normal subgroup. A complement intersects this kernel trivially, giving a faithful action on the actual center."))), DescribeRole.Theorem))));
}
