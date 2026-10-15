using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockFiniteCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection.";
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    private static Formula Successor(Formula value) => Seq(value, Plus, D(1));
    private static Formula Sign(Formula degree) => Seq(Open, Minus, D(1), Close, Caret, Grp(degree));

    private static Formula HalfSuccessorFormula()
    {
        var d = F.Id("d");
        return Disp(Seq(Forall, Sp, d, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("halfBinomial", Successor(d)), Eq, Frac,
            Grp(Open, Frac, Grp(Minus, D(1)), Grp(D(2)), Minus, d, Close,
                Call("halfBinomial", d)), Grp(Successor(d))));
    }

    private static Formula PairReflectionFormula()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var r = F.Id("r");
        var s = F.Id("s");
        return Disp(Seq(Forall, Sp, m, Comma, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("pairScalar", Successor(m), Successor(n)), Eq,
            Sum, Underscore, Grp(r, Eq, D(0)), Caret, Grp(m), Sp,
            Sum, Underscore, Grp(s, Eq, D(0)), Caret, Grp(n), Sp,
            Open, Sign(Successor(m)), Call("choose", Successor(m), Successor(r)), Close,
            Open, Sign(Successor(n)), Call("choose", Successor(n), Successor(s)), Close,
            Call("pairScalar", Successor(r), Successor(s))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite singleton and pair correction on the full ordinary lattice oscillator algebra.",
        H("Finite Twisted Correction"),
        Blocks(
            Paragraph(Text("The source weight of (i,k) is k+1, not the native half-Fock weight 2k+1. The extra polynomial variable records physical negative shifts. Singleton weights are binomial(-1/2,m) times the charge pairing; pair weights are mn binomial(-1/2,m) binomial(-1/2,n)/(m+n) times the Gram pairing. No inverse Gram matrix, positivity, rank condition or occupation cutoff occurs.")),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-half-successor"),
                DeclarationHandle.Create(Prefix + "half_successor"),
                H("The original half-binomial successor coefficient"),
                StatementSource.FromAuthor(HalfSuccessorFormula()),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every natural d, halfBinomial(d+1) = ((-1/2-d) halfBinomial(d))/(d+1), over Complex. This is the shared factorial-product recurrence consumed by the pair reflection proof and by the existing translation calculus; the recurrence is not new mathematical content."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-pair-scalar-reflection"),
                DeclarationHandle.Create(Prefix + "pairScalar_reflection"),
                H("Independent all-order reflection of the original pair coefficient"),
                StatementSource.FromAuthor(PairReflectionFormula()),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("For every pair of natural orders m,n, pairScalar(m+1,n+1) is the sum over 0 <= r <= m and 0 <= s <= n of ((-1)^(m+1) choose(m+1,r+1)) ((-1)^(n+1) choose(n+1,s+1)) pairScalar(r+1,s+1). Both orders are independent and unbounded. The coefficients are exactly the original jetReflectionScalar coefficients. The definitions halfBinomial(d) = product over 0 <= j < d of (-1/2-j), divided by d!, and pairScalar(k,l) = k l halfBinomial(k) halfBinomial(l)/(k+l) are unchanged.")),
                    Paragraph(Text("The finite binomial transform obeys a new all-order inductive identity: its signed transform equals the original pairScalar, with zero auxiliary axis values. The proof derives a finite two-coordinate recurrence and identifies its unique solution by induction, using the positive cast of the sum of the two source weights. It assumes no covariance premise, rank, signature, occupation cutoff, determinant or lattice data.")),
                    Paragraph(Text("In the actual pairPolynomial, the Gram entry stays unchanged. A reduced pair of orders r,s needs the extra shift power (m-r)+(n-s) to recover the original total source weight m+n+2. This scalar theorem alone does not prove correctionWord covariance or native all-state BPZ; labelled remainders, singleton contributions, and the operator transpose law remain required."))),
                DescribeRole.Theorem),
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
