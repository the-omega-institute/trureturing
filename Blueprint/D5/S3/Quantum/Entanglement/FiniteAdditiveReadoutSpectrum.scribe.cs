using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteAdditiveReadoutSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive readouts of one coherent source determine quotient blocks and flat marginals.",
        H("Finite Additive Readout Spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-readout-eigenspaces"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_eigenspaces"),
                H("Exact eigenspaces and dimensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On either side, a vector has eigenvalue equal to the positive block weight exactly "
                    + "when it lies in the range of that side's block-column matrix. The zero eigenspace "
                    + "is the kernel of its conjugate transpose. The positive eigenspaces have dimension "
                    + "equal to the quotient cardinality; the zero eigenspaces have the ambient dimension "
                    + "minus that cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-flat-reductions"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_flat_reductions"),
                H("Ranks and flat marginal spectra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The kernels intersect only at zero, their sum has the product cardinality, and "
                    + "the source cardinality is that product times the quotient cardinality. "
                    + "The block weight is the reciprocal quotient cardinality. Both actual marginals "
                    + "have trace one and rank equal to the quotient cardinality, as does the actual "
                    + "coefficient matrix. Their positive eigenvalues equal the block weight with "
                    + "that multiplicity; all remaining eigenvalues are zero. The von Neumann entropy "
                    + "of either actual marginal is the logarithm of the quotient cardinality, equal "
                    + "to the source-cardinality logarithm minus the two kernel-cardinality logarithms. "
                    + "The actual coefficient map between Euclidean spaces has the square root of the "
                    + "block weight as each positive singular value, repeated the quotient cardinality "
                    + "times, with every subsequent singular value zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-joint-state"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_joint_state"),
                H("Normalized joint pure state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The outer product of the actual coefficients is positive semidefinite and "
                    + "Hermitian, has trace and rank one, and is idempotent. The coefficient norm "
                    + "square is one. The sum of the actual source basis kets equals the coefficient "
                    + "vector coordinate by coordinate, and equals the sum of the products of the "
                    + "normalized block vectors scaled by the square root of the block weight."))),
                DescribeRole.Theorem))));
}
