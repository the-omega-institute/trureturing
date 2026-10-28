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
            Paragraph(Text("LatticeData consists of an arbitrary finite rank and a symmetric integral Gram matrix with even diagonal. Rank zero, degeneracy and indefinite forms are allowed. The source weight of (i,k) is k+1; the native half-Fock weight is 2k+1. The extra polynomial variable records physical negative shifts. Singleton weights are binomial(-1/2,m) times the charge pairing; pair weights are mn binomial(-1/2,m) binomial(-1/2,n)/(m+n) times the Gram pairing. No inverse Gram matrix, positivity, rank condition or occupation cutoff occurs.")),
            Describe.Lean(DescribeId.Create("finite-correction-l1-insertion-scalar"),
                DeclarationHandle.Create(Prefix + "insertion_l1_scalar"), H("The original insertion L1 scalar cancellation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every natural r,n, put m=r+1 and k(m,n)=m halfBinomial(m) halfBinomial(n)/(m+n). Then one half times halfBinomial(r) choose(1/2,n) equals (m+n)k(m,n), plus zero when n=0 or (n-1)k(m,n-1) otherwise, plus m k(m-1,n) when r is positive or the n=0 delta when r=0. Both boundary axes are retained. The proof uses the original half-binomial successor and Pascal identities. This is the scalar cancellation required by the original evaluated negative-current insertion route; it alone is not corrected-field L1 covariance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-correction-consumed-half-binomial-transform"),
                DeclarationHandle.Create(Prefix + "half_binomial_transform"), H("The original half-binomial finite transform"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Visibility-only exposure of the existing theorem with its exact original statement and proof body preserved. The new ActualCorrCovariance singleton_scalar proof consumes this finite transform; no new binomial proof is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-correction-consumed-labelled-remainders-size"),
                DeclarationHandle.Create(Prefix + "labelledRemainders_size"), H("Length and exact weight of a labelled remainder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Visibility-only exposure of the original joint length and wordWeight law. ActualCorrCovariance correctionWord_homogeneous consumes both clauses in the actual pair-matching branch, including repeated generators. Its proof body is unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-correction-consumed-word-weight-occurrences"),
                DeclarationHandle.Create(Prefix + "wordWeight_occurrences"), H("Exact weight of the original occurrences enumeration"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Visibility-only exposure of the original equality between wordWeight of occurrences and Finsupp.weight sourceWeight. ActualCorrCovariance consumes it to transport matching homogeneity to original oscillator polynomials. Its proof body is unchanged."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-positive-source-convolution"),
                DeclarationHandle.Create(Prefix + "halfBinomial_positive_convolution"),
                H("Positive source weight half convolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For all natural m,n with m>0, sum over 0<=s<=n of halfBinomial(m+s) choose(1/2,n-s) equals m halfBinomial(m) halfBinomial(n)/(m+n), over Complex. The certificate uses the arbitrary-complex binomial recurrence, telescopes only the interior 0<=s<n, and treats s=n separately. Division uses m+n nonzero from m>0, and includes n=0. The divided extension at m=n=0 is false: its left side is 1 and its right side is 0. The actual finite-current insertion triangle consumes this theorem at m=sourceWeight(D,index)=index.2+1; no standalone general cross-form API is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockfinitecorrection-pairderivation-variable"),
                DeclarationHandle.Create(Prefix + "pairDerivation_variable"),
                H("The original pair derivation on an ordinary variable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original generator lemma is public for direct reuse by correctionConnection_pair_commutator in CorrectionTranslation. Its statement and proof are retained; this is consumed support, not additional mathematical content."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-half-successor"),
                DeclarationHandle.Create(Prefix + "half_successor"),
                H("The original half-binomial successor coefficient"),
                StatementSource.FromAuthor(HalfSuccessorFormula()),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every natural d, halfBinomial(d+1) = ((-1/2-d) halfBinomial(d))/(d+1), over Complex. This factorial-product recurrence supplies the weighted binomial transform and the two-coordinate pair recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-pair-scalar-reflection"),
                DeclarationHandle.Create(Prefix + "pairScalar_reflection"),
                H("Independent all-order reflection of the original pair coefficient"),
                StatementSource.FromAuthor(PairReflectionFormula()),
                AssessedProvenance.FromRepo(Background),
                Blocks(
                    Paragraph(Text("For every pair of natural orders m,n, pairScalar(m+1,n+1) is the sum over 0 <= r <= m and 0 <= s <= n of ((-1)^(m+1) choose(m+1,r+1)) ((-1)^(n+1) choose(n+1,s+1)) pairScalar(r+1,s+1). Both orders are independent and unbounded. The coefficients are exactly the original jetReflectionScalar coefficients. The definitions halfBinomial(d) = product over 0 <= j < d of (-1/2-j), divided by d!, and pairScalar(k,l) = k l halfBinomial(k) halfBinomial(l)/(k+l) are unchanged.")),
                    Paragraph(Text("The finite binomial transform obeys an all-order inductive identity: its signed transform equals the original pairScalar, with zero auxiliary axis values. The proof derives a finite two-coordinate recurrence and identifies its unique solution by induction, using the positive cast of the sum of the two source weights. It assumes no covariance premise, rank, signature, occupation cutoff, determinant or lattice data.")),
                    Paragraph(Text("In the actual pairPolynomial, the Gram entry stays unchanged. A reduced pair of orders r,s needs the extra shift power (m-r)+(n-s) to recover the original total source weight m+n+2. This scalar theorem alone does not prove correctionWord covariance or native all-state BPZ; labelled remainders, singleton contributions, and the operator transpose law remain required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-derivation-shift"),
                DeclarationHandle.Create(Prefix + "pairDerivation_shift"),
                H("Pair derivations annihilate every shift power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every LatticeData, oscillator index and natural degree, pairDerivation sends X(none) raised to that degree to zero. The shift coordinate has derivative zero. This identity supplies the shift-generator case of commutation on arbitrary correction polynomials."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-derivation-pair"),
                DeclarationHandle.Create(Prefix + "pairDerivation_pair"),
                H("Pair derivations annihilate every pair coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every LatticeData and every three oscillator indices, pairDerivation annihilates pairPolynomial. Its scalar coefficient is constant and its polynomial factor is a shift power. This identity supplies generator commutation and permits pair coefficients to pass through insertions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("half-fock-correction-insertion-commute"),
                DeclarationHandle.Create(Prefix + "insertion_commute"),
                H("Symmetric differential insertions commute"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Each insertion is the sum of multiplication by the retained variable plus its singleton correction and the pair derivation. Pair derivations kill the shift variable and every singleton and pair coefficient. Their commutator vanishes on every polynomial generator; the mixed multiplication commutators cancel by Gram and pair-coefficient symmetry."))),
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
                Blocks(Paragraph(Text("For every word whose occurrences permute the canonical list, the monomial-basis correction equals its word correction. The proof uses insertion commutation to compare these enumerations. Corr records this finite coefficient family as a linear map on the original oscillator algebra. The insertion of two occurrences expands into the full retained-plus-singleton product plus its pair derivative, including singleton-singleton contributions and repeated variables."))),
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
                DescribeId.Create("half-fock-correction-polynomial-shift-bound"),
                DeclarationHandle.Create(Prefix + "Corr_shift_bound"),
                H("Every supported shift of an arbitrary polynomial is bounded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The unrestricted polynomial expands over its actual finite monomial support. Scalar multiplication cannot increase shift degree; every supported monomial weight is bounded by the ordinary weighted total degree. The bound holds for the actual support of Corr, with no cutoff on the polynomial or the shift index."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the state-field application, write V_D=Carrier D=(Charge D -> finitely supported Oscillator D). "
                + "A source u is thus a finite sum of single-charge states [a,p], with p an arbitrary polynomial in "
                + "Fin(D.rank) times N. When hu:IsUnit D.G.det, let T_D=Oscillator D tensor ActualGround D hu, "
                + "using exactly the actual ground representation and chargedField of "),
                Ref("D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients"),
                Text(". This determinant premise is needed for that ground realization; Corr itself still allows degenerate forms. "
                + "The ordinary source field is Y_D from "), Ref("D5/S3/VertexAlgebra/LatticeAllStateField"),
                Text(". Its source variables have weight k+1, whereas the target half-Fock variables have cover weight 2k+1.")),
            Paragraph(Text("Define N_a(p) by extending linearly from monomials the normally ordered insertion of their "
                + "labelled divided-current derivatives into chargedField(a). Negative current modes act to the left "
                + "and nonnegative modes to the right; the insertion order is independent of the chosen occurrence enumeration. "
                + "For a native Laurent field A(t)=sum_e A[e] t^e, define S_s(A)[e]=A[e+2s], so S_s is multiplication "
                + "by t^(-2s), or z^(-s) for physical z=t^2. Write Corr(a,p)[s] for its finite oscillator coefficient. "
                + "The corrected field is Ytw([a,p])=sum_s S_s(N_a(Corr(a,p)[s])); extend by the actual finite charge "
                + "sum to Ytw:V_D -> HVertexOperator(C,T_D). The singleton, pair and singleton-singleton terms of Corr "
                + "are all retained. In particular Ytw([a,1])=chargedField(a), and the neutral first source "
                + "Ytw([0,X(i,0)]) is the actual tensor current. No abstract replacement representation enters this definition.")),
            Paragraph(Text("Corr_shift_bound controls the inner shift support by the ordinary source weight, not by "
                + "a chosen occupation bound. Each normal coefficient also uses finite sums on each target vector. "
                + "These are different finiteness statements from a finite Laurent field: the complete field may have "
                + "infinitely many external cover coefficients. Its lower bound depends on the input vector. "
                + "Neither the source polynomial, its charge nor the external mode is truncated.")),
            Paragraph(Text("For A=Ytw(u), B=Ytw(w), first choose an actual operator-uniform locality order N: "
                + "(t^2-s^2)^N A(t)B(s)=(t^2-s^2)^N B(s)A(t), coefficientwise as endomorphisms of the same T_D. "
                + "Such an N exists for every u,w in V_D. Write C_0[e,f]=A[e] B[f] and "
                + "C_(n+1)[e,f]=C_n[e-2,f]-C_n[e,f-2] for the cleared ordered coefficients. "
                + "For r<N, set d=N-r-1 and define Pair_N(A,B;r)[e]x="
                + "sum_{j in Z} choose(j/2,d) C_N[j,e+2d-j]x. If L_A(x),L_B(x) are native lower bounds, "
                + "locality restricts this sum to L_A(x)<=j<=e+2d-L_B(x), so it is finite on each x. "
                + "For r>=N set Pair_N(A,B;r)=0. The product is independent of the chosen valid order. "
                + "The all-source identity is Pair_N(Ytw(u),Ytw(w);r)=Ytw((Y_D(u)[[r]])w), for every "
                + "integer r. No theta-sector hypothesis is imposed on this native identity. A product totalized as "
                + "zero when no locality witness exists can be used only after this existence result, so totalization "
                + "cannot supply the identity by itself.")),
            Paragraph(Text("The derivation compares the actual cleared charged products in both cover charts, "
                + "including the ground cocycle and the scalar 2^(-B(a,a)). Current insertion then propagates locality "
                + "and the residue equations through the same normally ordered construction. For the defect "
                + "D_r(u,w)=Ytw((Y_D(u)[[r]])w)-Pair_N(Ytw(u),Ytw(w);r), the two insertion recurrences reduce "
                + "negative-current insertions on the left and on the right to lower source-generation cases. "
                + "First induct on the left source against theta-projected charged ground states, then on the right "
                + "source against arbitrary left states. The projections span each charged ground state, so the "
                + "native conclusion is unrestricted. Finite source frequency bounds and common locality orders "
                + "justify each sum and cancellation. The scalar correction identities alone do not supply these "
                + "operator comparisons or either source induction.")),
            Paragraph(Text("To pass to ordinary modes, define I_alpha(A).coeff(k)=A[2k-alpha], equivalently "
                + "I_alpha(A)[[m]]=A[-2m-alpha-2]. For integers P,Q,r,k and x in T_D, assume the actual left "
                + "sector condition: Ytw(u)[e]=0 whenever e+P is odd. A sufficient source condition is "
                + "theta(u)=(-1)^P u, with theta the lattice involution of "),
                Ref("D5/S3/VertexAlgebra/LatticeInvolution"),
                Text(". Then the ordinary r-th residue product of I_P(Ytw(u)) and I_Q(Ytw(w)), at mode k on x, "
                + "equals sum_{i>=0} choose(P/2,i) Ytw((Y_D(u)[[r+i]])w)[-P-Q-2k+2i-2]x. "
                + "The sum is finite because high ordinary source modes vanish. The right source w and its label Q "
                + "are arbitrary; no right theta-eigenstate premise is added. Omitting the left sector condition "
                + "would erase the distinction between the two cover parities.")),
            Paragraph(Text("This is an application of the classical twisted-lattice construction of Frenkel, "
                + "Lepowsky and Meurman, with the twisted-module context also described by Bakalov and Kac, "
                + "Twisted Modules over Lattice Vertex Algebras, math/0402315; no literature novelty is claimed. "
                + "The finite correction, local residue comparison and state-field faithfulness concern formal "
                + "Laurent operators. Translation and arbitrary-word BPZ transpose require their own identities; "
                + "a full VOA or twisted-module structure, analytic CFT, anomalies, fusion, string dynamics and "
                + "AdS/CFT do not follow from this application alone.")))));
}
