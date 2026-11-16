using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class QubitResidualRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let rho be a canonical density state on A times (B times C), with B the two-dimensional coordinate type, and let T be an arbitrary canonical channel from B to B times C. Write P for the actual AB marginal and r for half the trace norm of rho minus the actual recovered reference state. Centering P at the product of its two marginals and testing all Hermitian contractions gives quantitative control that is independent of the dimensions of A and C. These statements describe correlation and dilation bounds; the universal fifth-root repair estimate requires additional estimates.",
        H("Physical qubit residual geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-b-unitary-transport"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.actual_B_unitary_transport"),
                H("Coherent transport of the physical recovery data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A local B unitary transports the same canonical ABC state, its actual AB, BC and B marginals, the canonical CPTP channel, and its recovered reference state. Every centered contraction slice transforms by the same conjugation. Half trace distance and ordinary conditional mutual information are unchanged, including singular states. Inverse transport returns every repaired state to the original physical carrier."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-diagonal-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.actual_diagonal_geometry"),
                H("Actual residual geometry in the attained basis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive attained centered slice norm x, diagonalization and coherent transport give an actual dilation of the transported channel. Every Hermitian contraction has residual at most 4r. The flip sum and coefficient difference are at most 2r divided by x; a positive phase-sensitive gap g bounds the complex off-diagonal centered block by 16r divided by g. This intermediate dilation supplier uses an ordinary Type coordinate for C; arbitrary-universe transport of that supplier remains separate from the still unfinished whole estimate."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("localbstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.localBState"),
                H("The same state in a B coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugate the original ABC density state by identity on A, the inverse unitary on B, and identity on C. The system and every rank are retained."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("localbchannel"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.localBChannel"),
                H("The coherently transported physical channel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Precompose the canonical recovery channel by the input unitary and postcompose by its inverse on the same output B coordinate. These are canonical completely positive trace preserving channels."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pointerisometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.pointerIsometry"),
                H("A normalized retained-column pointer map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two environment vectors define a qubit map whose j-th column has support only on output pointer j. Unit norms make this map an isometry."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-pointer-isometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.normalized_pointer_isometry"),
                H("Normalize retained columns below unit flip probability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the sum s squared of the two flip probabilities is below one, both retained columns of the actual isometry have positive norm. Normalize them and delete the flips to obtain a pointer isometry within operator norm 2s. No input block weight is inverted."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("offdiagonal-gap-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.offDiagonal_gap_bound"),
                H("A phase-sensitive coherence bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every traceless Hermitian qubit M tested against the same actual isometry, the retained-column gap times the off-diagonal modulus is bounded by half its trace-norm residual plus the coefficient-difference bound times its operator-norm bound and half the flip bound times that operator-norm bound. Complex phases and both nonunital coherence coefficients are retained."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-block-bound-of-diagonal-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.complex_block_bound_of_diagonal_geometry"),
                H("Complex block duality from the same diagonal geometry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the centered AB matrix, suppose every Hermitian contraction slice has operator norm at most x greater than zero and actual reduced-isometry residual at most 4r. If the total flip probability and coherence-coefficient difference are each at most 2r divided by x, then for positive retained-column gap g the complex off-diagonal block has trace norm at most 16r divided by g. The modulus trace pairing first has bound 8r divided by g, and complex duality retains its factor two."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonalized-residual-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.diagonalized_residual_geometry"),
                H("An actual isometry in the attained eigenbasis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any nonzero traceless Hermitian qubit K and any actual physical isometry W, diagonalize K and rotate the same input and output qubit coordinate. The resulting physical isometry V has the exact transported action on every complex matrix. If the K residual has trace norm at most e, both its total flip probability and the difference of its diagonal-to-coherence terms are at most e divided by twice the operator norm of K."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("column"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.column"),
                H("The four physical column slices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output B coordinate splits the two Stinespring columns into retained and flipped vectors in the full environment space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reduced"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.reduced"),
                H("The reduced physical action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation by the isometry followed by the actual environment partial trace defines the reduced qubit action on every complex input matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("isometry-coefficient-geometry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.isometry_coefficient_geometry"),
                H("Phase-sensitive two-column cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite environment and actual two-column isometry, the reduced off-diagonal entry is the sum of four complex coefficient terms. Column orthogonality gives exact cancellation in the sum of the two diagonal-to-coherence coefficients. Their modulus is bounded by twice the square root of total flip probability times the square root of the phase-sensitive retained-column gap. No unitality is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-residual-controls-coefficients"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.diagonal_residual_controls_coefficients"),
                H("Diagonal residual bounds the flip terms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A trace-norm residual e for the diagonal Pauli direction bounds both the total flip probability and the difference of the diagonal-to-coherence coefficients by e divided by two. The exact trace norm of a traceless Hermitian qubit supplies both bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centered"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.centered"),
                H("The centered AB correlation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtract the product of the two actual marginals from the AB density matrix. Both partial traces of this centered matrix vanish."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slicelinear"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.sliceLinear"),
                H("Hermitian reference tests"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pair each reference block with a complex-linear test on A. For Hermitian inputs and Hermitian tests the resulting B matrix is Hermitian."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("attained-centered-tracenorm-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.attained_centered_traceNorm_bound"),
                H("An attained correlation maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The maximum operator norm of the centered slice over all Hermitian A contractions is attained. Pauli reconstruction and Hermitian trace duality bound the trace norm of the centered AB matrix by six times this maximum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-centered-tests-residual"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.all_centered_tests_residual"),
                H("Every centered test is approximately fixed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every Hermitian A contraction, its centered qubit slice has residual at most 4r under the actual reduced channel obtained by discarding C after T. The AB and B residuals each have trace norm at most 2r."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-repair-of-centered-correlation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.product_repair_of_centered_correlation"),
                H("A product repair from small correlation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an attaining reference test with slice operator norm x, the actual state a tensor T(b) on the same ABC space has ordinary conditional mutual information zero and lies within trace distance r plus 3x of rho. Here a and b are the actual marginals of P."))),
                DescribeRole.Theorem))));
}
