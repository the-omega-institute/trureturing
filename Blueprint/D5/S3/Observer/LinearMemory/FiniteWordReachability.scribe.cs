using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class FiniteWordReachabilityDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Observer/LinearMemory/FiniteWordReachability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered endomorphism words reach the whole reachable seed span by its rank gap.",
        H("Finite word reachability"),
        Blocks(
            Paragraph(Text("Let K be a division ring, E a left K-module with an additive commutative group, "
                + "I any alphabet, A an I-indexed family of K-linear endomorphisms, and U a seed submodule. "
                + "The three type universes are independent. The alphabet may be empty or infinite. "
                + "For a list w, its action is the product of the list mapped through A. Multiplication "
                + "of endomorphisms is composition: the head acts after the tail, and the empty word acts as identity.")),
            Describe.Lean(DescribeId.Create("bounded-word-span"),
                DeclarationHandle.Create(Root + "boundedSpan"), H("Words through a finite horizon"),
                StatementSource.FromAuthor(Parameters(Seq(
                    Forall, Sp, F.Id("n"), Colon, Sp, F.Id("N"), Comma, Sp,
                    Call("boundedSpan", F.Id("A"), F.Id("U"), F.Id("n")), Sp, Eq, Sp,
                    WordSpan(true)), false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The length condition includes every shorter word and the empty word. "
                    + "The span permits arbitrary finite linear combinations of word images from U."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reachable-word-span"),
                DeclarationHandle.Create(Root + "reachableSpan"), H("All finite words"),
                StatementSource.FromAuthor(Parameters(Seq(
                    Call("reachableSpan", F.Id("A"), F.Id("U")), Sp, Eq, Sp, WordSpan(false)), false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the smallest submodule containing U and invariant under every A(i). "
                    + "The ordered-word induction in the proof establishes the closure property used below."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bounded-span-equals-reachable"),
                DeclarationHandle.Create(Root + "bounded_span_eq_reachable"),
                H("The reachable rank gap bounds the horizon"),
                StatementSource.FromAuthor(Parameters(Seq(
                    Call("boundedSpan", F.Id("A"), F.Id("U"),
                        Seq(Call("finrank", F.Id("K"), Call("reachableSpan", F.Id("A"), F.Id("U"))),
                            Sp, Minus, Sp, Call("finrank", F.Id("K"), F.Id("U")))),
                    Sp, Eq, Sp, Call("reachableSpan", F.Id("A"), F.Id("U"))), true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume E is finite dimensional. Write R for the full reachable span and "
                        + "b = dim(R) - dim(U). Then W(b) = R, so every ordered word image of every seed vector "
                        + "lies in W(b). This is stabilization by b; b need not be the first stable index. "
                        + "Neither commutation, positive seed rank, invariance, nor a pre-existing plateau is assumed. "
                        + "The zero seed and zero ambient space are included.")),
                    Paragraph(Text("For F(S) = S + sup over i of A(i)S, induction identifies F iterated n times "
                        + "on U with W(n). These iterates increase inside R. The public bounded_monotone_has_equal_step "
                        + "theorem in FiniteSequentialWordCertificate supplies an equal-rank consecutive pair by b. "
                        + "Inclusion and equal finite rank turn that pair into an F-fixed submodule. Ordered-word "
                        + "induction puts every finite word image inside it, identifying it with R. Fixed-point "
                        + "iteration reaches the same space at b. Since R is contained in E, monotonicity also "
                        + "gives W(dim(E) - dim(U)) = R.")),
                    Paragraph(Text("The application is the finite-horizon step of section 349.2, Lemma 349.1, "
                        + "equations 349.8 through 349.12 of RECURSIVE_RELATIONAL_OBSERVATION_PHASE_BOUNDARY. "
                        + "Take the scalar field to be the complex numbers and E the coordinate space on Fin(d), with "
                        + "dimension d counting the full persistent carrier. Set A(i) = mulVecLin(K(i)) "
                        + "and U = range(tau), where tau is the positive initial operator. A finite Kraus family "
                        + "defines Phi(X) = sum over i of K(i) X K(i)*; the empty family and zero CP map are allowed. "
                        + "At an interior parameter with strictly positive branch weights, rescaling Kraus operators "
                        + "by their nonzero square-root weights preserves the word-image spans. This theorem supplies "
                        + "the horizon b for that algebraic span.")),
                    Paragraph(Text("The quantum application takes any finite coordinate type n, any finite Kraus "
                        + "alphabet I and any positive semidefinite complex matrix tau. No nonempty carrier or alphabet, "
                        + "pure seed, normalization, trace preservation or commuting Kraus family is required. Put "
                        + "U = range(mulVecLin(tau)), A(i) = mulVecLin(K(i)), R = reachableSpan(A,U), "
                        + "b = dim(R) - dim(U), and X(N) = sum of Phi^k(tau) for 0 <= k <= N. Then X(N) is "
                        + "positive semidefinite, range(mulVecLin(X(N))) = W(N), and in particular range(X(b)) = R. "
                        + "For every nonzero v in R, the Hermitian quadratic form v* X(b) v is strictly positive. "
                        + "X(b) is positive definite on the ambient carrier if and only if R is the whole carrier.")),
                    Paragraph(Text("Here support means the linear range of a positive matrix. The positive-sum "
                        + "identity follows from HermitianMat.ker_sum in PositiveFilterTransposeRefutation, together "
                        + "with LinearMap.orthogonal_ker, Submodule.iInf_orthogonal and finite-dimensional double "
                        + "orthogonal complementation. It says that the range of a finite positive sum is the supremum "
                        + "of the summand ranges. To obtain the Kraus-image identity, factor a positive Y as B* B using "
                        + "CStarAlgebra.nonneg_iff_eq_star_mul_self. Each K(i) Y K(i)* is the Gram matrix "
                        + "(K(i) B*) (K(i) B*)*. LinearMap.range_self_comp_adjoint identifies its range with that "
                        + "of K(i) B*, while the same Gram identity identifies range(Y) with range(B*). Thus "
                        + "range(Phi(Y)) is the supremum over i of map(A(i),range(Y)). Matrix.toEuclideanLin and "
                        + "WithLp.linearEquiv transport the adjoint and kernel statements to the coordinate module; "
                        + "the coordinate transport changes neither the range nor its dimension.")),
                    Paragraph(Text("Let F(S) = S + sup over i of map(A(i),S), and let P be the linear matrix map "
                        + "of the Kraus family. On positive matrices, support intertwines Y -> P(Y) + Y with F. "
                        + "Function.Semiconj.iterate_right therefore identifies the support of (P + identity)^N(tau) "
                        + "with F^N(U). The existing iterate_eq_bounded identity in this module gives F^N(U) = W(N). "
                        + "Only P and identity need commute: Commute.add_pow expands (P + identity)^N(tau) as the "
                        + "sum of choose(N,k) times Phi^k(tau), for 0 <= k <= N. Nat.choose_pos makes each of these "
                        + "coefficients strictly positive. LinearMap.range_smul and the positive-sum identity remove "
                        + "the weights without changing support, yielding range(X(N)) = W(N). This does not assume "
                        + "commutation between distinct K(i), nor between distinct ordered word products.")),
                    Paragraph(Text("Apply bounded_span_eq_reachable with division ring C, module n -> C, "
                        + "endomorphisms mulVecLin(K(i)) and seed U. Its rank-gap horizon gives range(X(b)) = R. "
                        + "For a positive matrix X, Matrix.PosSemidef.dotProduct_mulVec_zero_iff identifies zero "
                        + "quadratic form with membership in ker(X). A Hermitian matrix has range orthogonal to "
                        + "its kernel, so a range vector with zero quadratic form is zero. Nonnegativity then gives "
                        + "strict positivity on every nonzero range vector. Applying this to X(b) proves positivity "
                        + "on R. In finite dimension a Hermitian matrix has zero kernel exactly when its range is "
                        + "the whole carrier, giving the stated ambient-positive-definiteness equivalence.")),
                    Paragraph(Text("If tau is zero, U and R are zero, b = 0 and X(b) = 0; positivity on nonzero "
                        + "vectors of R is vacuous. If I is empty, Phi is zero, R = U, b = 0 and X(b) = tau. "
                        + "If n is empty, the whole carrier is also zero, and ambient positive definiteness is "
                        + "vacuous. X(b) is strictly positive on nonzero vectors of R, and its kernel is exactly "
                        + "the orthogonal complement of R. A proper R therefore prevents ambient positive definiteness. "
                        + "The application is a composition "
                        + "of existing declarations, with no additional mathematical declaration. It supplies no "
                        + "quantitative lower eigenvalue bound, preparation procedure or finite-CP growth estimate. "
                        + "Every persistent classical register, retained seed, program counter, clock value, archive "
                        + "and returning environment belongs in the carrier dimension; physical resource savings "
                        + "and literature novelty are separate questions.")),
                    Paragraph(Text("For a regular-language application, let E be a finite-dimensional real effect "
                        + "space, T a terminal effect family, U = span(T), and A_i real linear endomorphisms of E "
                        + "indexed by a finite alphabet Sigma. Fix a finite deterministic partial automaton "
                        + "(Q, Sigma, delta, q0, F), with no epsilon moves. Its extended transition delta*(q,w) "
                        + "starts at q on the empty word and follows the symbols in chronological order; it is "
                        + "undefined if any transition is missing. Let L be the words with delta*(q0,w) in F. "
                        + "For w = i1...ik in chronological symbol order, put A_w = A_i1...A_ik, with A_empty = id. "
                        + "This is the Heisenberg effect convention: the head acts after the tail. A source "
                        + "functional x in the real dual E* evaluates the word effect as x(A_w u).")),
                    Paragraph(Text("Set V = direct sum over q in Q of E, with coordinate embedding iota_q and "
                        + "projection P_q. Define the endomorphism B_i by (B_i v)_q = A_i(v_delta(q,i)) when "
                        + "delta(q,i) exists, and zero otherwise; put B_w = B_i1...B_ik. For every q in Q, f in F "
                        + "and u in U, P_q B_w iota_f u equals A_w u if delta*(q,w) = f, and zero otherwise. "
                        + "For the empty word this follows from P_q iota_f. For w = iv, a missing transition "
                        + "makes the q coordinate zero; otherwise P_q B_i B_v iota_f u = "
                        + "A_i P_delta(q,i) B_v iota_f u. Induction on v gives the stated condition and "
                        + "A_i A_v u = A_w u. No injectivity of delta in its state argument is needed.")),
                    Paragraph(Text("Take the seed S = direct sum over f in F of iota_f U, of dimension "
                        + "s = |F| dim(U). Let R_n = span{B_w z : |w| <= n, z in S}, R = span{B_w z : w finite, "
                        + "z in S}, H_n = span{A_w u : w in L, |w| <= n, u in U}, and H the corresponding span "
                        + "over all accepted words. Then P_q0 R_n = H_n: expand a seed into its accepting-state "
                        + "coordinates and use the word identity for one inclusion; for an accepted word choose "
                        + "its unique final state f and seed iota_f u for the other. Likewise P_q0 R = H. "
                        + "For a fixed word at most one accepting-state coordinate contributes at q0, so the "
                        + "separated seeds do not grant extra terminal tests.")),
                    Paragraph(Text("Apply the existing bounded_span_eq_reachable directly with the real scalar field, "
                        + "ambient module V, endomorphisms B_i and seed S. Writing r = dim(R), it gives R_N = R "
                        + "at N = r - s, hence H_N = H and N <= |Q| dim(E) - |F| dim(U). The rank gap belongs "
                        + "to the full DFA product space. If F is empty or U is zero, S and R are zero and N = 0; "
                        + "if q0 is not accepting, H_0 = 0 even when S is nonzero. This is an application of the "
                        + "existing theorem. The word and projection identities above supply its mathematical "
                        + "adapter; that adapter and any native realization are not additional kernel-checked "
                        + "Lean declarations in this module.")),
                    Paragraph(Text("Consequently, for any x,y in E*, equality x(A_w t) = y(A_w t) for every "
                        + "t in T and accepted w of length at most N is equivalent to equality for all accepted "
                        + "words and t in T. Indeed x-y then vanishes on H_N = H; the reverse implication is "
                        + "restriction to shorter words. Each longer effect has a finite linear expansion in "
                        + "the bounded family, independent of x,y. Such expansions may have negative coefficients "
                        + "and do not describe executable mixtures of tests.")),
                    Paragraph(Text("The DFA filtering construction is literature-attested; see "
                        + "Library/Automata/fliess1974products.md for the Hadamard closure and tensor-product "
                        + "representation. With D_i(q,r) = 1 when delta(q,i) = r and zero otherwise, "
                        + "B_i = D_i tensor A_i. For fixed x,u and t_u = sum over f in F of iota_f u, "
                        + "x(P_q0 B_w t_u) = 1_L(w) x(A_w u), the coefficientwise product of the language "
                        + "indicator and the original series. The cited result treats a finite nonempty alphabet "
                        + "over a commutative unital coefficient ring, including the reals; the empty alphabet "
                        + "case here follows directly from the empty-word identity.")),
                    Paragraph(Text("Regularly constrained reachability and unobservability algorithms are "
                        + "also literature-attested; see Library/Automata/bastug2014restricted.md, section VI, "
                        + "Lemma 5 and Algorithms 1-2. Their forward matrix convention A_ik...A_i1 corresponds "
                        + "to the present effect convention by taking dual maps, without reversing the chronological "
                        + "word. In the present notation set H_q^(n) = P_q R_n. Then H_q^(0) = U for "
                        + "q in F and zero otherwise, and H_q^(n+1) = H_q^(n) + sum over defined delta(q,i)=r "
                        + "of A_i H_r^(n). This follows by separating the empty word and the first symbol of "
                        + "each accepted word from q. All spaces must stabilize simultaneously: equality at "
                        + "every q makes this tuple a fixed point, so induction gives every later tuple unchanged. "
                        + "Equality at q0 alone supplies no such implication. These separate coordinate spaces "
                        + "are projections of R_n; their dimension sum need not equal dim(R_n), since projection "
                        + "can discard correlations between blocks. The cited algorithms assume a co-reachable "
                        + "finite automaton with a nonempty accepting set; the zero seed cases above are handled "
                        + "directly. Their language-restricted output guarantee does not silently include outputs "
                        + "at every nonaccepted intermediate prefix.")),
                    Paragraph(Text("Normalization and complete measurements still allow an arbitrarily long "
                        + "initial-slice plateau. For any integer m >= 2, take E = R^2, one = (1,1), "
                        + "T = {one}, U = span(one), and normalized states x_p = (p,1-p), acting by dot product, "
                        + "0 <= p <= 1. Put e0 = (1,0), e1 = (0,1), A_t = id, A_b0 = diag(1,0), and "
                        + "A_b1 = diag(0,1). The two b maps are branches of one complete two-result classical "
                        + "measurement: A_b0 + A_b1 = id, and their effects on one are e0,e1. Let "
                        + "Q = {0,...,m}, q0 = 0 and F = Q. The only transitions are delta(j,t)=j+1 for "
                        + "0 <= j < m-1, and delta(m-1,b0)=delta(m-1,b1)=m. All other transitions are missing. "
                        + "Thus L = {t^j : 0 <= j <= m-1} union {t^(m-1)b0, t^(m-1)b1}, a prefix-closed "
                        + "language allowing termination at every waiting prefix.")),
                    Paragraph(Text("For n < m the accepted effects A_w one are all one, since only waiting words "
                        + "occur and A_t = id. At length m the two branch words give e0,e1. Therefore "
                        + "H_n = span(one) for n < m and H_n = E for n >= m. The projected gap "
                        + "dim(H)-dim(H_0) is 1, yet the first new direction appears at the arbitrarily large "
                        + "horizon m. This is statistically nontrivial on normalized states: x_p(one)=1, "
                        + "x_p(e0)=p and x_p(e1)=1-p. The full lift instead has seed dimension m+1 and "
                        + "R = (direct sum over j=0,...,m-1 of iota_j E) plus iota_m span(one). To prove the "
                        + "lower inclusion, for each j < m and ell in {0,1}, "
                        + "B_t^(m-1-j) B_bell iota_m one = iota_j e_ell, transporting the branch effects "
                        + "backwards along the t edges. For the upper inclusion, that displayed space contains "
                        + "S and is invariant under every B_i: the t maps only copy coordinates "
                        + "backwards, the b maps send the last block to block m-1, and the last block of every "
                        + "nonempty-word image is zero because m has no outgoing edges. Hence dim(R)=2m+1 "
                        + "and dim(R)-dim(S)=m. The product-space bound is sharp, since H_(m-1) differs from H. "
                        + "This example supplies no source reset or extra side channel.")),
                    Paragraph(Text("A sufficient extra condition for the initial-slice gap is invariance of "
                        + "K0 = R intersect ker(P_q0) under every B_i. Then define an endomorphism C_i of H by "
                        + "C_i(P_q0 v) = P_q0 B_i v for v in R. Changing v by an element of K0 changes the "
                        + "right side by zero, so C_i is well defined; B_i preserves R, so its values lie in H. "
                        + "Induction gives C_w P_q0 = P_q0 B_w on R. With seed P_q0 S = H_0, the bounded "
                        + "C-word spans are exactly H_n and the full span is H. Applying the same existing "
                        + "theorem on H therefore gives H_(dim(H)-dim(H_0)) = H. Finite DFA size alone "
                        + "does not establish this invariance condition.")),
                    Paragraph(Text("For native FIB action languages, the DFA is an independent hypothesis. "
                        + "A faithful finite abstraction eta: Config -> Q of native configurations must map the actual paired "
                        + "initial sources to q0, preserve enabled actions and allowed termination, and make "
                        + "each retained action/output symbol update the abstract state exactly by delta. "
                        + "Configurations identified at one abstract state must agree on these permissions and "
                        + "abstract updates, including intervention rights, write permissions and control memory. Omitted "
                        + "internal events must be represented or shown to leave this abstraction unchanged. "
                        + "Every claimed native test must be represented, and each accepted test must have a "
                        + "legal implementation at its original source; taking a union of source-dependent "
                        + "languages cannot lend one source another source's permissions. The same source "
                        + "functional must reproduce the native composite statistics x(A_w t). Finite-dimensional "
                        + "statistics alone supply neither this abstraction nor a bound on permission memory.")),
                    Paragraph(Text("Branches may be indexed by an action and its output. Their effect maps "
                        + "must be dual to unnormalized linear state-branch updates with the correct composite pairing; a "
                        + "quantum interpretation additionally needs actual CP branches, their dual effect maps, "
                        + "complete instruments for licensed actions and physical terminal effects. Zero extension "
                        + "at a missing DFA transition is algebraic filtering, not an execution witness. A legal "
                        + "zero-probability test remains distinct from an illegal test. Rejecting an output word "
                        + "does not physically remove that output: its probability mass must remain in the "
                        + "instrument, for example in a rejecting state. Such a state cannot confer permission "
                        + "to perform an unlicensed action.")),
                    Paragraph(Text("Under the stated linear and language hypotheses, the finite span determines "
                        + "statistics of all permitted potential tests. It supplies neither their simultaneous "
                        + "acquisition along one history nor exact probabilities from finitely many samples. "
                        + "It does not construct a native exact chart, a task-small or minimal controller, or a "
                        + "physical CP compression. Equality of test statistics alone establishes no equality of "
                        + "cost, time, disturbance or write service; each such conclusion needs its own "
                        + "permission-preserving realization and resource correspondence."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Parameters(Formula body, bool finite)
    {
        Formula k = F.Id("K"), e = F.Id("E"), i = F.Id("I");
        var items = new List<Formula> {
            Forall, Sp, k, Comma, Sp, e, Comma, Sp, i, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("DivisionRing", k), CloseBracket, Sp,
            OpenBracket, Call("AddCommGroup", e), CloseBracket, Sp,
            OpenBracket, Call("Module", k, e), CloseBracket, Sp };
        if (finite) items.AddRange([OpenBracket, Call("FiniteDimensional", k, e), CloseBracket, Sp]);
        items.AddRange([Forall, Sp, F.Id("A"), Colon, Sp, i, Sp, To, Sp, Call("End", k, e), Comma, Sp,
            F.Id("U"), Colon, Sp, Call("Submodule", k, e), Comma, Sp, body]);
        return Disp(Seq([.. items]));
    }

    private static Formula WordSpan(bool bounded)
    {
        var items = new List<Formula> { OpenBrace, F.Id("x"), Sp, Mid, Sp,
            Exists, Sp, F.Id("w"), Colon, Sp, Call("List", F.Id("I")), Comma, Sp };
        if (bounded) items.AddRange([Call("length", F.Id("w")), Sp, Leq, Sp, F.Id("n"), Sp, Land, Sp]);
        items.AddRange([Exists, Sp, F.Id("z"), Sp, InMacro, Sp, F.Id("U"), Comma, Sp,
            F.Id("x"), Sp, Eq, Sp, Call("apply", Call("prod", Call("map", F.Id("A"), F.Id("w"))),
                F.Id("z")), CloseBrace]);
        return Call("span", F.Id("K"), Seq([.. items]));
    }
}
