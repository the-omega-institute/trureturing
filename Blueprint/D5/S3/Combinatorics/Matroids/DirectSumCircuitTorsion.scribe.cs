using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class DirectSumCircuitTorsionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The transpose cokernel of joint circuit restriction factors over ordered direct sums.",
        H("Joint circuit torsion for ordered direct sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-circuit-transpose-cokernel-tensor"),
                DeclarationHandle.Create(Module + ".joint_circuit_transpose_cokernel_tensor"),
                H("The transpose cokernel of a direct sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M and N be matroids on a finite linearly ordered carrier. Their "
                        + "grounds are disjoint, and every ground vertex of M precedes every ground "
                        + "vertex of N. The source lattice is the lattice of integral augmented "
                        + "top cycles. The joint target contains one contraction cycle lattice for "
                        + "each circuit. The joint map records all signed aggregate restrictions.")),
                    Paragraph(Text(
                        "The ordered join induces an integral linear equivalence from the tensor "
                        + "product of the source lattices to the source lattice of the direct sum. "
                        + "Under the dual equivalence, a pure tensor of functionals evaluates on a "
                        + "joined pair as the product of the evaluations. Sending the tensor of two "
                        + "quotient classes to the class of the corresponding tensor functional "
                        + "gives an isomorphism onto the transpose cokernel of the direct sum.")),
                    Paragraph(Text(
                        "A basis and every allowable one-element exchange split over the two "
                        + "grounds. The ordered join takes pairs of normalized passive cycles to "
                        + "normalized passive cycles of the sum. Every circuit lies in one factor "
                        + "and contraction leaves the other factor unchanged. The signed readout "
                        + "on a left circuit factors without an extra sign. A right circuit has "
                        + "the sign from passing its facet across the left face. These signs are "
                        + "units, so the transpose relations are the sum of the two tensor "
                        + "extensions of the factor relation submodules."))),
                DescribeRole.Theorem))));
}
