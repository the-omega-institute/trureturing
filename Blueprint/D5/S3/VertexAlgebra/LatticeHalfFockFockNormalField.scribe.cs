using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockFockNormalFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField.";
    private static readonly LibraryNoteRef Architecture =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/kytola2025virasoro");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Statewise finite physical current-jet insertion on the actual native tensor module.",
        H("Native Fock Normal Fields"),
        Blocks(
            Paragraph(Text("The carrier is the existing ActualTensor D hu with hu : IsUnit D.G.det. A source oscillator (i,k) inserts the physical divided jet with coefficient binomial(-j-3/2,k) and cover exponent -2j-2k-3. Negative j acts on the left and nonnegative j on the right, independently of jet order. In particular j=-1 remains a creation mode. Ordinary cover normalMinusOne is not used.")),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-negative-finite"),
                DeclarationHandle.Create(Prefix + "negativeTerm_finite"),
                H("The left creation convolution is finite on each vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("For a fixed exponent, increasing the negative-mode creation index decreases the tail-field coefficient exponent. Its actual Hahn order gives a finite index bound before any finsum distribution is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-positive-finite"),
                DeclarationHandle.Create(Prefix + "positiveTerm_finite"),
                H("The right annihilation convolution is finite on each vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The released tensor_current_truncation supplies a finite cutoff for the original vector. No support condition on an End-valued infinite family is assumed. The actual tensor current and the actual existing tail field are used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-lower-truncation"),
                DeclarationHandle.Create(Prefix + "normalCoefficient_lower_truncation"),
                H("Finite intermediate orders give lower truncation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The creation part uses the tail field order minus the source jet shift. The annihilation part uses the minimum of finitely many actual tail-field orders after the right current acts. This lower bound proves each convolution term vanishes below it and is consumed directly by HVertexOperator.of_coeff. Additivity and scalar linearity use the preceding finite-support proofs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-zero-charge-identity"),
                DeclarationHandle.Create(Prefix + "charged_zero_identity"),
                H("The existing zero-charge tensor field is the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("At zero charge the creation series is zero, the existing translated polynomial is constant, and the genuine ground representation acts by its unit. The actual charged coefficient is the identity at exponent zero and zero elsewhere, first on pure tensors and then by tensor induction. No alternate charged map is defined."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-polynomial-unit"),
                DeclarationHandle.Create(Prefix + "normalPolynomial_one"),
                H("The unit polynomial selects the existing charged field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("This consumed monomial-basis evaluation is used by charged-state recovery and carries no new mathematical-content credit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-polynomial-variable"),
                DeclarationHandle.Create(Prefix + "normalPolynomial_X"),
                H("A source variable selects its actual physical current insertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The single-occurrence basis evaluation is consumed by current recovery, with insertion order k and exponent -2j-2k-3. It is a proof-organization lemma, not new mathematical content."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-zero-shift"),
                DeclarationHandle.Create(Prefix + "shiftLinear_zero"),
                H("Zero physical shift preserves a native field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The coefficient equality is consumed by generator recovery and has no new-content credit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-current-recovery"),
                DeclarationHandle.Create(Prefix + "normalInsertion_identity_current"),
                H("Insertion into the identity recovers the native tensor current"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The order-zero physical jet has scalar coefficient one. Each odd cover exponent selects exactly one negative or nonnegative underlying current mode in the already finite convolution; even cover exponents select none. The recovered field is the existing tensorCurrentField, including the creation mode j=-1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-unfiltered-support-bound"),
                DeclarationHandle.Create(Prefix + "flatTerm_support_bound"),
                H("The original target cutoff bounds every unfiltered tuple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("ModeTuple labels occurrences by their positions, retaining repeated variables. flatCoefficient uses every integer tuple, without filtering: all negative jet currents act left of the one existing charged coefficient and all nonnegative currents act right. Same-sign native current commutation preserves the ORIGINAL target annihilation cutoff R after every right derivative. A nonzero term therefore has every j<R. Replacing negative indices by -1 leaves the right action unchanged, so its states come from the finite box [-1,R]. Let L be the minimum of zero and the actual base-field orders on these right-derivative states, n the word length and W=sum(2k+3). A nonzero term has e+2sum(j)+W>=L; with M=min(L-e-W,0), every mode lies in [M-nR,R]. The bound is on individual full products, not a cancellation-raised intermediate tail-field order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-unfiltered-support-finite"),
                DeclarationHandle.Create(Prefix + "flatTerm_finite"),
                H("Every native state has finite unfiltered tuple support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("On a pure polynomial tensor ground state the cutoff is exactly the original polynomial vars.sup(k+1), using current_vanish. Tensor induction extends finite support to every algebraic tensor; sums use coefficient linearity and finite support of the two original families. No signature, norm sign, occupation or source-word restriction is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-native-factorization"),
                DeclarationHandle.Create(Prefix + "flatCoefficient_factorization"),
                H("The term is the exact full Fock-normal product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The recursive tuple operator equals leftAction times the original field coefficient at e+2sum(j)+sum(2k+3) times rightAction. Each actual jet factor is jetScalar(k,j) times the existing native tensorCurrent(i,j). This consumed normalization identifies the native charged middle without defining a second charged map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-flattened-sequence"),
                DeclarationHandle.Create(Prefix + "normalSequence_flattened"),
                H("Pointwise finite sums equal the existing nested insertions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("After full tuple support is proved, finsum_curry and finite-support map_finsum identify the unfiltered sum with normalInsertion recursion. Integer modes split bijectively into -(r+1) and r, exactly the two existing single-insertion sums. No End-valued infinite sum is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-jet-same-sign"),
                DeclarationHandle.Create(Prefix + "jetCurrent_same_sign"),
                H("Actual same-sign jet currents commute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The native Heisenberg commutator has no contraction when both modes are negative or both nonnegative. Pure-tensor lifting and scalar linearity prove the exact jet identity; no oscillator law is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-insertions-commute"),
                DeclarationHandle.Create(Prefix + "normalInsertion_commute"),
                H("Fock-normal insertions commute on every native field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The finite flattened two-occurrence sum is reindexed by exchanging its two labelled mode coordinates. Two negative factors commute on the left, two nonnegative factors commute on the right, and opposite signs act on different sides of the middle coefficient. This is not an asserted field locality or Jacobi law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-word-permutation"),
                DeclarationHandle.Create(Prefix + "normalWord_perm"),
                H("Repeated-occurrence enumeration is immaterial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("List.Perm induction uses the actual commuting insertion theorem, including arbitrary repeated labels and the empty word. The result is consumed by normalPolynomial_monomial_enumeration and the polynomial expansion of the actual corrected Ytw."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-normal-word-flattened"),
                DeclarationHandle.Create(Prefix + "normalWord_flattened"),
                H("The existing charged word has its full native expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("The general sequence theorem is applied to the existing chargedField and consumed by Ytw_fock_normal_coefficients. This is an organizational application, not separately claimed new mathematics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-polynomial-enumerated-expansion"),
                DeclarationHandle.Create(Prefix + "normalPolynomial_enumerated_expansion"),
                H("Arbitrary polynomial coefficients consume enumeration independence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Architecture),
                Blocks(Paragraph(Text("Each supported monomial may use any permutation of its occurrence list. Monomial-basis linear extension gives the exact finite expansion with the original complex coefficients, consumed directly inside correctedPolynomial/Ytw rather than defining an alternate assignment."))),
                DescribeRole.Theorem),
            Paragraph(Text("The construction adapts the finite-support normal-product architecture attributed to Scott Carnahan and the classical twisted lattice construction. Full twisted Jacobi, physical translation, sectorTranslation recurrences, ground monodromy and inverse-Gram stress equality remain separate obligations. Compilation and source-admission registrations are distinct; Reg obligation aliases do not constitute completed four-slot registrations.")))));
}
