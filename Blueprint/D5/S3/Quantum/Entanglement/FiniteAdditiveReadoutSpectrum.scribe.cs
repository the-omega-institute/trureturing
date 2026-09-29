using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteAdditiveReadoutSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive readouts of one coherent source determine quotient blocks and flat marginals.",
        H("Finite Additive Readout Spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-readout-paired-block"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.paired_block_iff"),
                H("Paired block criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A pair of readout labels comes from one source element exactly when the two labels "
                    + "occur in the same quotient block. The kernel sum lets representatives on the "
                    + "two sides be joined into one source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-actual-coefficient"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_coefficient_block"),
                H("Actual coefficient blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a jointly injective pair of readouts, each coefficient of the actual source "
                    + "sum is the normalized indicator of its unique quotient block. The assertion "
                    + "comes from the source sum, rather than a prescribed block matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-right-block-card"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.right_block_card"),
                H("Right block cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each right block has as many distinct labels as the left readout kernel has "
                    + "elements. Joint injectivity gives the needed bijection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-source-coset-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.source_coset_product"),
                H("Source cosets and product blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The paired readout restricts to a bijection from each source coset onto the "
                    + "product of its left and right label blocks. Both coordinates of the "
                    + "bijection are the original readout values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-actual-block-matrices"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_block_matrices"),
                H("Matrices from the actual source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalized left and right block columns are orthonormal. The actual coefficient "
                    + "matrix factors through these columns with the square-root block weight. "
                    + "Taking its two actual partial traces gives scaled block projections, their "
                    + "column actions, and zero action on the respective conjugate-transpose kernels. "
                    + "Both block projections are Hermitian and idempotent. The blocks on each side "
                    + "are disjoint and their union is precisely that readout's image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-left-eigenspaces"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_left_eigenspaces"),
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
