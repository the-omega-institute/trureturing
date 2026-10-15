using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockFiniteCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite singleton and pair correction on the full ordinary lattice oscillator algebra.",
        H("Finite Twisted Correction"),
        Blocks(
            Paragraph(Text("The source weight of (i,k) is k+1, not the native half-Fock weight 2k+1. The extra polynomial variable records physical negative shifts. Singleton weights are binomial(-1/2,m) times the charge pairing; pair weights are mn binomial(-1/2,m) binomial(-1/2,n)/(m+n) times the Gram pairing. No inverse Gram matrix, positivity, rank condition or occupation cutoff occurs.")),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-insertion-commute"),
                DeclarationHandle.Create(Prefix + "insertion_commute"),
                H("Symmetric differential insertions commute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Each insertion is multiplication by the retained variable plus its singleton correction, followed by the pair derivation. Pair derivations kill the shift variable and every singleton and pair coefficient. Their commutator vanishes on every polynomial generator; the mixed multiplication commutators cancel by Gram and pair-coefficient symmetry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-word-permutation"),
                DeclarationHandle.Create(Prefix + "correctionWord_permutation"),
                H("Occurrence order does not change the correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The insertion algorithm terminates by word length. Adjacent swaps use the actual commuting insertions, and transitivity gives every occurrence permutation. Repeated variables remain separate list occurrences; differentiation supplies their multiplicities. The existing monomial basis extends the construction linearly to every finite oscillator polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-arbitrary-monomial"),
                DeclarationHandle.Create(Prefix + "Corr_monomial_enumeration"),
                H("Every monomial enumeration gives the same finite correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual monomial-basis correction agrees with every permutation of its source occurrences, using the insertion commutation proof rather than a chosen enumeration as a premise. This is the finite coefficient family Corr consumed by correctedPolynomial and Ytw. The insertion of two occurrences expands into the full retained-plus-singleton product plus its pair derivative, including singleton-singleton contributions and repeated variables."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-labelled-derivative"),
                DeclarationHandle.Create(Prefix + "pairDerivation_matching"),
                H("Differentiation contracts one labelled occurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("labelledRemainders traverses positions recursively. Each entry retains every occurrence except the selected one, including other occurrences of the same variable. The derivation of an arbitrary correction word is the finite sum of its pair coefficient times the correction of each such remainder. The proof commutes the pair derivation through an insertion and inducts on the actual source word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-labelled-matching"),
                DeclarationHandle.Create(Prefix + "correctionWord_matching"),
                H("Every word obeys the singleton and labelled-pair recurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The active occurrence is either retained, removed as a singleton, or paired with exactly one labelled remaining occurrence. Recursive remainders shorten the word. Two occurrences therefore include retained factors, each singleton, the singleton-singleton term and the pair term, without erasing all equal variables."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-word-shift-bound"),
                DeclarationHandle.Create(Prefix + "correctionWord_shift_bound"),
                H("Word corrections never exceed the ordinary source weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Strong induction on occurrence count bounds the degree of the actual shift polynomial. A singleton spends the active source weight. A pair spends both removed weights, while the remainder has exactly the complementary weight. The bound applies without positivity, a charge norm bound or a rank hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-unit"),
                DeclarationHandle.Create(Prefix + "Corr_one"),
                H("The empty oscillator state has no correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The monomial basis sends the empty word to the unit at shift zero. This evaluation is consumed by exact charged-state recovery and is not counted as new mathematical content."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-neutral-current"),
                DeclarationHandle.Create(Prefix + "Corr_X_zero"),
                H("A neutral single oscillator is unchanged"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("There is no pair partner and the charge pairing is zero. The actual correction is the same oscillator at shift zero. This evaluation is consumed by current recovery and has no new-content credit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-polynomial-shift-bound"),
                DeclarationHandle.Create(Prefix + "Corr_shift_bound"),
                H("Every supported shift of an arbitrary polynomial is bounded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The unrestricted polynomial expands over its actual finite monomial support. Scalar multiplication cannot increase shift degree; every supported monomial weight is bounded by the ordinary weighted total degree. The resulting Corr support bound is consumed by the actual all-state lower-truncation estimate."))),
                DescribeRole.Theorem),
            Paragraph(Text("These are derived classical twisted-lattice corrections, not a literature-novelty claim or a twisted-Jacobi proof. The actual native-field constructor consumes Corr. Physical translation compatibility remains a separate obligation.")))));
}
