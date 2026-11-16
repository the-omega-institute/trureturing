using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class QubitCenteredTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Center an AB density state at the product of its actual marginals. Hermitian contraction tests attain a maximum and control its trace norm. Coherent local B transport preserves the actual recovered residual and ordinary conditional mutual information.",
        H("Centered tests and unitary transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qcmi-eq-four-marginals"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_eq_four_marginals"),
                H("The four actual marginal entropies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ordinary qcmi of the canonical state converted to MState equals the entropy of its actual AB marginal plus the entropy of its actual BC marginal minus the entropy of its actual B marginal and the entropy of the state itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qcmi-product-left"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.qcmi_product_left"),
                H("A product across A and BC"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every density state a on A and every density state omega on B times C, the physical product a tensor omega has ordinary conditional mutual information zero. Product entropy additivity applies without a rank condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centered"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.centered"),
                H("The centered AB correlation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtract the product of the two actual marginals from the AB density matrix. Both partial traces of this centered matrix vanish."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slicelinear"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.sliceLinear"),
                H("Hermitian reference tests"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pair each reference block with a complex-linear test on A. For Hermitian inputs and Hermitian tests the resulting B matrix is Hermitian."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("centered-marginals-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_marginals_zero"),
                H("Both centered marginals vanish"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtracting the product of the two actual marginals from a density matrix gives zero under both partial traces."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("block"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.block"),
                H("An outer-coordinate block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixing the two inner coordinates of a bipartite matrix gives its matrix block on the outer coordinate."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pauli"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.pauli"),
                H("The three Pauli directions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three Pauli matrices specify the traceless qubit directions used to reconstruct the centered correlation."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("centered-hermitian"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.centered_hermitian"),
                H("Hermiticity of centered correlation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A density matrix minus the product of its actual marginals is Hermitian."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tracenorm-tensor"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.traceNorm_tensor"),
                H("Trace norm of a tensor product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace norm of a finite tensor product is the product of the two trace norms."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("attained-centered-tracenorm-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.attained_centered_traceNorm_bound"),
                H("An attained correlation maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The maximum operator norm of the centered slice over all Hermitian A contractions is attained. Pauli reconstruction and Hermitian trace duality bound the trace norm of the centered AB matrix by six times this maximum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensorunitary"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.tensorUnitary"),
                H("Tensor product of two unitaries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The tensor product of two unitary matrices is unitary on the product coordinate type."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conjugatestate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateState"),
                H("Unitary transport of a density state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugating a canonical density matrix by a unitary gives a density state on the same coordinate type."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conjugatealg"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.conjugateAlg"),
                H("Unitary conjugation as an algebra equivalence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Unitary conjugation defines a complex star algebra equivalence of the full finite matrix algebra."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tensor-conjugate-block"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.tensor_conjugate_block"),
                H("Conjugation of each reference block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugation on the second tensor factor acts by the same matrix conjugation on every block indexed by the first factor."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("localbchannel"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel"),
                H("The coherently transported physical channel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Precompose the canonical recovery channel by the input unitary and postcompose by its inverse on the same output B coordinate. These are canonical completely positive trace preserving channels."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("localbchannel-reference"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.localBChannel_reference"),
                H("Transport of the recovered reference"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport the input and output B coordinates of the actual channel coherently. Recovering the transported AB state then equals local B transport of the original recovered reference state."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tracedistance-conjugatestate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.traceDistance_conjugateState"),
                H("Unitary invariance of half trace distance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Simultaneous unitary conjugation of two density states preserves their half trace distance."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("localbstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState"),
                H("The same state in a B coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugate the original ABC density state by identity on A, the inverse unitary on B, and identity on C. The system and every rank are retained."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("localbstate-ab"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.localBState_AB"),
                H("The actual AB marginal after transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual AB marginal of local B transport equals conjugation of the original AB marginal by the identity on A and the corresponding B unitary."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("referenceraw"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceRaw"),
                H("The linear recovered action on matrices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the canonical channel to the B coordinate of each block of a bipartite matrix, retaining its A coordinate."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("referencestate-contract"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_contract"),
                H("Recovered states contract distance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying the same channel to the B coordinate of two density states does not increase their half trace distance."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("referencestate-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.referenceState_product"),
                H("Recovery of a product input"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Recovery of a product of an A state and a B state is the product of the A state and the channel output on B."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cstar-sum-entry"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.cstar_sum_entry"),
                H("Entries of finite matrix sums"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluating an entry of a finite sum of CStar matrices gives the sum of the corresponding entries."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("slice-sub"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_sub"),
                H("Slices commute with subtraction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Testing the blocks of a difference of bipartite matrices gives the difference of the two tested slices."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("slice-reference"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_reference"),
                H("Testing commutes with recovery"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Testing the A coordinate of a recovered matrix equals applying the channel to the tested input slice."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("slice-centered-conjugate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.slice_centered_conjugate"),
                H("Centered slices under B transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugating the B coordinate of a density state conjugates every centered A-test slice by the same B unitary."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-b-unitary-transport"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/QubitCenteredTransport.actual_B_unitary_transport"),
                H("Coherent transport of the physical recovery data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the input unitary U, localBState conjugates rho by its inverse on B. The public conjunction identifies the actual AB marginal, its B marginal, the transported canonical channel and recovered reference state, and conjugation of every centered slice. The proof of ordinary qcmi invariance uses the actual AB, BC and B marginal entropy identities. Half trace distance is unchanged. Applying localBState with star U returns a repair and its qcmi and distance bounds to the original ABC carrier, including singular states."))), DescribeRole.Theorem))));
}
