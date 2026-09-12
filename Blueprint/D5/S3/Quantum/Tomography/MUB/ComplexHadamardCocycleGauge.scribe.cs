using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class ComplexHadamardCocycleGaugeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent unitary vertex gauges preserve scaled relative-Gram cocycles.",
        H("Complex Hadamard Cocycle Gauge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "cocycle-gauge-right-vertex-gauge-action"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge."
                    + "relativeGram_right_vertexGauge"),
                H("Right vertex gauge action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two families H and M of complex square matrices on a finite "
                    + "coordinate type, the relative Gram of H(a) M(a) and H(b) M(b) equals the "
                    + "relative Gram of H(a) and H(b), multiplied on the left by the adjoint of "
                    + "M(a) and on the right by M(b)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "cocycle-gauge-scaled-cocycle-covariance"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge."
                    + "scaledCocycle_vertexGauge"),
                H("Scaled cocycle covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose G(a,b) G(b,c) equals scale times G(a,c) for every vertex triple, "
                    + "and each M(b) times its adjoint is the identity. Replacing every G(a,b) "
                    + "by M(a)-adjoint times G(a,b) times M(b) preserves the same scaled "
                    + "cocycle equation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "cocycle-gauge-relative-gram-cocycle-after-gauging"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/ComplexHadamardCocycleGauge."
                    + "relativeGram_cocycle_after_vertexGauge"),
                H("Relative Gram cocycle after gauging"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a family of complex Hadamard matrices H and vertex matrices M "
                    + "satisfying M(b) times its adjoint equals the identity, the relative "
                    + "Grams of H(b) M(b) satisfy the cocycle equation with scale equal to the "
                    + "finite coordinate cardinality."))),
                DescribeRole.Theorem))));
}
