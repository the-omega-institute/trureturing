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
                        + "and literature novelty are separate questions."))),
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
