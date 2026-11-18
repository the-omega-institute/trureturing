using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class QubitActualResidualGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual AB and B marginals inherit the recovered residual. Every centered Hermitian test is approximately fixed by the reduced channel. Diagonalizing an attained nonzero test controls the physical flip terms and the complex off-diagonal block; small centered correlation gives an A-BC product repair.",
        H("Actual marginal residual geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partialtraceright-contract"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.partialTraceRight_contract"),
                H("Right partial trace contracts Hermitian trace norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace norm of the right partial trace of a Hermitian matrix is no greater than the trace norm of the original matrix."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensorright"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.tensorRight"),
                H("The right tensor algebra map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Tensoring a matrix on the left with the identity defines a complex star algebra map into matrices on the product coordinate type."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reducedaction"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.reducedAction"),
                H("The channel with C discarded"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the physical B to BC channel and then discard C, obtaining the actual reduced B action on matrices."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-b-residual"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_B_residual"),
                H("Residual of the actual B marginal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace norm difference between the actual B marginal and its reduced-channel image is at most twice the half trace distance between the original state and its actual recovered reference."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-centered-tests-residual"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.all_centered_tests_residual"),
                H("Every centered test is approximately fixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every Hermitian A contraction, its centered qubit slice has residual at most 4r under the actual reduced channel obtained by discarding C after T. The AB and B residuals each have trace norm at most 2r."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonalized-residual-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.diagonalized_residual_geometry"),
                H("An actual isometry in the attained eigenbasis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any nonzero traceless Hermitian qubit K and any actual physical isometry W, diagonalize K and rotate the same input and output qubit coordinate. The resulting physical isometry V has the exact transported action on every complex matrix. If the K residual has trace norm at most e, both its total flip probability and the difference of its diagonal-to-coherence terms are at most e divided by twice the operator norm of K."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-block-bound-of-diagonal-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.complex_block_bound_of_diagonal_geometry"),
                H("Complex block duality from the same diagonal geometry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the centered AB matrix, suppose every Hermitian contraction slice has operator norm at most x greater than zero and actual reduced-isometry residual at most 4r. If the total flip probability and coherence-coefficient difference are each at most 2r divided by x, then for positive retained-column gap g the complex off-diagonal block has trace norm at most 16r divided by g. The modulus trace pairing first has bound 8r divided by g, and complex duality retains its factor two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-diagonal-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_diagonal_geometry"),
                H("Actual residual geometry in the attained basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive attained centered slice norm x, diagonalization and coherent transport give an actual dilation of the transported channel. Every Hermitian contraction has residual at most 4r. The flip sum and coefficient difference are at most 2r divided by x; a positive phase-sensitive gap g bounds the complex off-diagonal centered block by 16r divided by g. The physical dilation is obtained by finite reindexing of the output coordinate, so arbitrary finite coordinate universes remain in scope."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-repair-of-centered-correlation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitActualResidualGeometry.product_repair_of_centered_correlation"),
                H("A product repair from small correlation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an attaining reference test with slice operator norm x, the actual state a tensor T(b) on the same ABC space has ordinary conditional mutual information zero and lies within trace distance r plus 3x of rho. Here a and b are the actual marginals of P."))),
                DescribeRole.Theorem))));
}
