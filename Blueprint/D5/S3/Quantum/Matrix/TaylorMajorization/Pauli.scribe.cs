using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.TaylorMajorization;

internal sealed class PauliDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/TaylorMajorization/Pauli";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A negative defect at every odd order at least five.",
        H("A negative defect at every odd order at least five."), Blocks(
            Describe.Lean(DescribeId.Create("taylor-majorization-pauli-defect-even"),
                DeclarationHandle.Create(Module + ".defect_even"),
                H("Exact even Pauli defects"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m at least one, the Pauli pair Z=diag(1,-1) and X with off-diagonal entries one has defect at order 2m equal to 4 to the m minus 2 to the m+1. Order zero has defect zero. The product moments follow from Z squared and X squared equal to I; a scalar binomial expansion computes the trace of Q. Anticommutation gives (Z+X) squared equal to 2I."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("taylor-majorization-pauli-defect-odd"),
                DeclarationHandle.Create(Module + ".defect_odd"),
                H("Vanishing odd Pauli defects"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every odd order 2m+1 the unshifted Pauli defect is zero. The binomial trace formula for Q has opposite signed powers, and (Z+X) to an odd power is a scalar multiple of the traceless matrix Z+X."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("taylor-majorization-pauli-defect-shift-negative"),
                DeclarationHandle.Create(Module + ".defect_shift_negative"),
                H("Strictly negative defects after translation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every odd natural k at least five and every positive real t, the defect for Z-tI and X is strictly negative. In the binomial translation sum, odd defects vanish. Every even defect is nonnegative, and its coefficient has negative sign because k is odd. The order-four term is strictly negative since choose(k,4) and t to the k-4 are positive."))), DescribeRole.Theorem))));
}
