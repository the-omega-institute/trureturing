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
                DescribeId.Create("finite-readout-kernel-quotient"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.kernel_quotient_normalization"),
                H("Kernel and quotient sizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two readout kernels intersect only at zero. Their sum has the product "
                    + "cardinality, and the source cardinality is the quotient cardinality times "
                    + "that product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-block-partitions"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.readout_block_partitions"),
                H("Partitions of realized labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Distinct quotient blocks have disjoint labels on each side. The union of left "
                    + "blocks is the left readout image, and the union of right blocks is the right image."))),
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
                    + "column actions, and zero action on the respective conjugate-transpose kernels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-left-eigenspaces"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_left_eigenspaces"),
                H("Exact left eigenspaces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A left vector has eigenvalue equal to the positive block weight exactly when it "
                    + "lies in the range of the actual left block-column matrix. It has eigenvalue "
                    + "zero exactly when its conjugate transpose annihilates it. Both converses use "
                    + "orthonormality of the actual block columns."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-flat-reductions"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_flat_reductions"),
                H("Ranks and flat marginal spectra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The block weight is the reciprocal quotient cardinality. Both actual marginals "
                    + "have trace one and rank equal to the quotient cardinality, as does the actual "
                    + "coefficient matrix. Their positive eigenvalues equal the block weight with "
                    + "that multiplicity; all remaining eigenvalues are zero."))),
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
                    + "square is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-reduced-entropy"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutSpectrum.actual_reduced_entropy"),
                H("Entropy of the actual marginals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The von Neumann entropy of either actual reduced density state is the natural "
                    + "logarithm of the quotient cardinality. It also equals the source-cardinality "
                    + "logarithm minus the logarithms of the two kernel cardinalities."))),
                DescribeRole.Theorem))));
}
