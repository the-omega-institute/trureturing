using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteAdditiveReadoutBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive readouts of one coherent source determine quotient blocks and flat marginals.",
        H("Finite Additive Readout Blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-readout-paired-block"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.paired_block_iff"),
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
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_coefficient_block"),
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
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.right_block_card"),
                H("Right block cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each right block has as many distinct labels as the left readout kernel has "
                    + "elements. Joint injectivity gives the needed bijection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-source-coset-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.source_coset_product"),
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
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_block_matrices"),
                H("Matrices from the actual source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalized left and right block columns are orthonormal. The actual coefficient "
                    + "matrix factors through these columns with the square-root block weight. "
                    + "Taking its two actual partial traces gives scaled block projections, their "
                    + "column actions, and zero action on the respective conjugate-transpose kernels. "
                    + "Both block projections are Hermitian and idempotent. The blocks on each side "
                    + "are disjoint and their union is precisely that readout's image. Left and right "
                    + "blocks have the respective opposite kernel cardinalities. For every chosen "
                    + "representative, their labels are its readout translated by the opposite kernel "
                    + "image. Both reductions square to the block weight times themselves. Their "
                    + "entries are the same-block indicators summed over the quotient and scaled "
                    + "by the corresponding kernel cardinality divided by the source cardinality. "
                    + "The quotient cardinality is bounded by both ambient label cardinalities."))),
                DescribeRole.Theorem))));
}
