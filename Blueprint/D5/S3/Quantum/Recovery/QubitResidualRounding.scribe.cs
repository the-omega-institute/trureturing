using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class QubitResidualRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let rho be a canonical density state on A times (B times C), with B the two-dimensional coordinate type, and let T be an arbitrary canonical channel from B to B times C. Write P for the actual AB marginal and r for half the trace norm of rho minus the actual recovered reference state. Centering P at the product of its two marginals and testing all Hermitian contractions gives quantitative control that is independent of the dimensions of A and C. Every such state and channel admit a density state sigma on the same ABC system with ordinary conditional mutual information zero and half trace distance from rho at most the minimum of one and six times the fifth root of r. No rank, spectral-floor, channel-closeness or repaired-marginal premise is imposed.",
        H("Physical qubit residual geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qubit-residual-fifth-root-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.qubit_residual_fifth_root_repair"),
                H("A dimension-independent fifth-root physical repair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary finite A and C, a canonical state rho on A times (Fin 2 times C), and every canonical channel T from Fin 2 to Fin 2 times C, form its actual AB marginal P and the recovered reference state. If r is their half trace distance, there exists sigma on the same ABC carrier with ordinary qcmi zero and distance at most min(1, 6 r^(1/5)). Every rank and zero eigenvalue are allowed. The four true marginal entropies agree exactly with ordinary qcmi.")), Paragraph(Text("The maximum centered Hermitian slice is attained. A small maximum yields an A-BC product directly. Otherwise diagonalizing the attained slice transports rho, its actual marginal and T coherently, and controls the total flip probability. A small retained-column gap gives an AB-C product; small B coherence gives a classical pointer repair. For large B coherence the actual marginal equation forces a product comparison. With delta the fifth root of r, the nontrivial scale delta below one sixth gives flip probability at most 2 delta to the fourth power and all comparison bounds at most 6 delta. The distance cap handles the other scales. At r zero, the same geometry gives exactly zero flips and either a common environment vector or zero coherence in the classical repair. Undoing the local B unitary returns sigma to the original system."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-environment-product-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.common_environment_product_repair"),
                H("A common environment gives an AB-C product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let g be the modulus of one minus the inner product of the two retained Stinespring vectors. If the total flip probability s squared is below one, normalize the first retained vector and use it for both pointer columns. This is a physical product across AB and C, with ordinary qcmi zero and half trace distance from rho at most r plus 2s plus the square root of 2g. The comparison retains every rank and the same ABC system."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("marginal-coherence-gap-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.marginal_coherence_gap_bound"),
                H("The actual marginal constrains the phase gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual B density state b with reduced-channel residual at most 2r, the phase gap times the modulus of b's off-diagonal entry is bounded by r plus s times the square root of g plus half the coefficient-difference bound and half the flip bound. The trace-one equation separates the sum and difference of the two diagonal-to-coherence coefficients, and isometry orthogonality bounds their sum."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classical-pointer-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.classical_pointer_repair"),
                H("A classical repair on the same physical system"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let W be an actual dilation of T, and let s squared be its total flip probability in the chosen qubit basis. If s squared is below one, normalizing its two retained vectors and pinching the actual AB input produces a classical Markov state on the same ABC carrier. Its half trace distance from rho is at most r plus the trace norm z of the actual off-diagonal AB block plus 2s. A positive block weight normalizes its conditional A state; a zero block has zero positive matrix and needs no division."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pointerinput-distance"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.pointerInput_distance"),
                H("The cost of deleting qubit coherence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pinching an actual AB density state in the two-dimensional B basis changes it in half trace distance by at most the trace norm of its complex off-diagonal A block. The two conjugate off-diagonal terms and the half-distance convention account for the factor."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physicaloutput-distance"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitResidualRounding.physicalOutput_distance"),
                H("A common environment comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two physical isometries applied to the same AB density state, followed by discarding their common environment, differ in half trace distance by at most the operator norm of the difference of the isometries. This comparison has no reference-dimension factor."))), DescribeRole.Theorem),
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
                Blocks(Paragraph(Text("For a positive attained centered slice norm x, diagonalization and coherent transport give an actual dilation of the transported channel. Every Hermitian contraction has residual at most 4r. The flip sum and coefficient difference are at most 2r divided by x; a positive phase-sensitive gap g bounds the complex off-diagonal centered block by 16r divided by g. The physical dilation is obtained by finite reindexing of the output coordinate, so arbitrary finite coordinate universes remain in scope."))), DescribeRole.Theorem),
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
