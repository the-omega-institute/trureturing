using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class RicoZyczkowskiMonotoneRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.";
    private const string Povm =
        "D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/ricozyczkowski2024measurements");
    private const string Conjecture =
        "Let P ∈ Δ_{n,d} and Q ∈ Δ_{n,d} be blockwise probability vectors. If there exists a blockwise bistochastsic matrix B ∈ B_{n,d} such that Q = B ∗ P, then for any ordering of {Q_i} there exists an ordering of {P_i} such that ‖Σ_{i=1}^{k}(P_i − 1/n)‖₂ ≥ ‖Σ_{i=1}^{k}(Q_i − 1/n)‖₂ for all 1 ≤ k ≤ n, where ‖A‖₂ = √tr[A†A] is the 2-norm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-outcome measurement on a two-dimensional complex space refutes the nonlinear 2-norm prefix inequality under commuting blockwise bistochastic dynamics.",
        H("Rico–Życzkowski nonlinear monotone refutation"),
        Blocks(
            Node("rz-block-bistoch", "Blockwise bistochastic matrices", BlockBistochFormula(),
                "Definition 5, p. 12, verbatim (equations rendered inline): Let B be a square matrix of size dn × dn composed of n² blocks B_ij of size d × d each. We call B blockwise bistochastic if (i) its entries B_ij are positive semidefinite matrices of size d ≥ 2 (ii) its blockwise columns and rows sum to identity, Σ_i B_ij = Σ_j B_ij = 1_d. BlockBistoch includes the dimension condition 2 ≤ d, positivity and both identity resolutions.",
                "BlockBistoch", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rz-block-product", "The blockwise product", BlockProductFormula(),
                "Definition 3 and Eq. (19), p. 8, verbatim (equation rendered inline): Let A and B be two matrices A = (A_ij) ∈ C^{dn} × C^{dn′} and B = (B_ij) ∈ C^{dn′} × C^{dn′′} composed of n × n′ and n′ × n′′ positive semidefinite blocks of size d, A_ij, B_ij ∈ C^d × C^d. We define the blockwise product, (A ∗ B)_ik = Σ_j √B_jk A_ij √B_jk ∈ C^{dn} × C^{dn′′}. For a probability column P the product is Q_i = Σ_j √P_j B_ij √P_j. CFC.sqrt is the principal positive semidefinite matrix square root, given by the continuous functional calculus for Hermitian matrices.",
                "IsBlockProduct", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rz-hs", "The 2-norm", HsFormula(),
                "Appendix C.1, p. 28, verbatim: where ‖A‖₂ = √tr[A†A] is the 2-norm. Matrix.conjTranspose is the conjugate transpose A†. The trace of Aᴴ A is real and nonnegative, so hs is the square root of its real part, the source's Hilbert–Schmidt 2-norm.",
                "hs", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rz-claim", "Conjecture 1", ClaimFormula(),
                "Appendix C.1, Conjecture 1, p. 28, verbatim: " + Conjecture +
                " Definition 1, p. 4, verbatim (equations rendered inline): A blockwise probability vector is a column vector P = (P_1, …, P_n)^T, with n components P_j being Hermitian, positive semidefinite matrices of order d, P_j ≥ 0, satisfying the identity resolution Σ_{j=1}^n P_j = 1_d. IsPOVM is D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM, specialized to Ω = Fin n. Matrix.PosSemidef includes Hermitian symmetry; 1 is the identity matrix." +
                " Lean uses zero-based Fin indices. The orderings σ and π are permutations of Fin n. Positions with i.val < k are exactly the first k positions; the range is 1 ≤ k ≤ n. Each occurrence of 1/n multiplies the d-dimensional identity matrix, with n cast to ℂ. The displayed formula compares 2-norms. BlockBistoch contains the source’s dimension restriction d ≥ 2. A centered dot between a complex scalar and a matrix denotes Lean’s scalar action •.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rz-result", "Refutation at n = 3, d = 2", Disp(Seq(Neg, Call("claim"))),
                "Take P₀ = diag(5/12, 1/6), P₁ = diag(1/6, 5/12), and P₂ = diag(5/12, 5/12). On the first diagonal coordinate, interchange outcomes 0 and 1; on the second, keep them fixed. Mix each of these permutations with the uniform three-outcome matrix using weights 9/10 and 1/10. All blocks are diagonal and positive semidefinite, and every block row and column sums to the identity. The principal positive semidefinite square roots give Q₀ = diag(11/60, 11/60) and Q₁ = Q₂ = diag(49/120, 49/120). The squared 2-norm values satisfy hs(P_j − (1/3) • 1)² ≤ 5/144 for every j and hs(Q₀ − (1/3) • 1)² = 9/200 > 5/144. Monotonicity of the square root makes k = 1 fail for every input ordering when the output ordering is the identity.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rico-zyczkowski-2024-nonlinear-majorization-monotone"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Op(string name)
    {
        var parts = name.Split('.');
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1))
            result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Op(name) : Seq(Op(name), Parenthesized(Arguments(arguments)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        Seq(function, Parenthesized(Arguments(arguments)));
    private static Formula Arguments(Formula[] arguments) =>
        Seq([.. arguments.SelectMany((value, index) => index == 0
            ? new[] { value } : new[] { Comma, Sp, value })]);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula All(Formula value, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Typed(value, type)), Comma, Sp, body);
    private static Formula Ex(Formula value, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Typed(value, type)), Comma, Sp, body);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, Parenthesized(right));
    private static Formula And(params Formula[] clauses) =>
        Seq([.. clauses.SelectMany((value, index) => index == 0
            ? new[] { Parenthesized(value) } : new[] { Sp, Land, Sp, Parenthesized(value) })]);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Parenthesized(premise), Sp, Rightarrow, Sp, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Matrix(Formula size) => Call("Matrix", Fin(size), Fin(size), Complex);
    private static Formula Family(Formula n, Formula d) => Arrow(Fin(n), Matrix(d));
    private static Formula BlocksType(Formula n, Formula d) => Arrow(Fin(n), Family(n, d));
    private static Formula One(Formula d) => Parenthesized(Typed(D(1), Matrix(d)));
    private static Formula Psd(Formula value) => Seq(Parenthesized(value), Dot, Op("PosSemidef"));
    private static Formula SumOver(Formula value, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Typed(value, type)), Sp, body);

    private static Formula BlockBistochFormula()
    {
        var n = F.Id("n"); var d = F.Id("d"); var b = F.Id("B");
        var i = F.Id("i"); var j = F.Id("j");
        return Disp(All(n, Nat, All(d, Nat, All(b, BlocksType(n, d),
            Equal(Call("BlockBistoch", b), And(
                Seq(D(2), Sp, Le, Sp, d),
                All(i, Fin(n), All(j, Fin(n), Psd(App(F.Id("B"), i, j)))),
                All(i, Fin(n), Equal(SumOver(j, Fin(n), App(F.Id("B"), i, j)), One(d))),
                All(j, Fin(n), Equal(SumOver(i, Fin(n), App(F.Id("B"), i, j)), One(d)))))))));
    }
    private static Formula BlockProductFormula()
    {
        var n = F.Id("n"); var d = F.Id("d"); var b = F.Id("B");
        var p = F.Id("P"); var q = F.Id("Q");
        var i = F.Id("i"); var j = F.Id("j");
        var sandwich = Seq(Call("CFC.sqrt", App(p, j)), Sp, Star, Sp,
            App(b, i, j), Sp, Star, Sp, Call("CFC.sqrt", App(p, j)));
        return Disp(All(n, Nat, All(d, Nat, All(b, BlocksType(n, d),
            All(p, Family(n, d), All(q, Family(n, d),
                Equal(Call("IsBlockProduct", b, p, q),
                    All(i, Fin(n), Equal(App(q, i), SumOver(j, Fin(n), sandwich))))))))));
    }
    private static Formula HsFormula()
    {
        var d = F.Id("d"); var a = F.Id("A");
        var norm = Seq(Sqrt, Grp(Call("Complex.re", Call("Matrix.trace",
            Seq(Call("Matrix.conjTranspose", a), Sp, Star, Sp, a)))));
        return Disp(All(d, Nat, All(a, Matrix(d), Equal(Call("hs", a), norm))));
    }
    private static Formula PrefixNorm(string family, Formula ordering, Formula n, Formula d, Formula k)
    {
        var i = F.Id("i");
        var bound = Seq(Typed(i, Fin(n)), Comma, Sp, Call("val", i), Sp, Lt, Sp, k);
        var scalar = Parenthesized(Typed(
            Seq(D(1), Sp, Slash, Sp, Parenthesized(Typed(n, Complex))), Complex));
        var term = Parenthesized(Seq(App(F.Id(family), App(ordering, i)), Sp, Minus, Sp,
            scalar, Sp, Seq(Cdot), Sp, One(d)));
        return Call("hs", Seq(Sum, Underscore, Grp(bound), Sp, term));
    }
    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var d = F.Id("d"); var p = F.Id("P"); var q = F.Id("Q");
        var b = F.Id("B"); var sigma = SigmaLower; var pi = Pi; var k = F.Id("k");
        var perm = Call("Equiv.Perm", Fin(n));
        var comparison = Seq(PrefixNorm("P", pi, n, d, k), Sp, Ge, Sp, PrefixNorm("Q", sigma, n, d, k));
        var prefixes = All(k, Nat, Imp(Seq(D(1), Sp, Le, Sp, k),
            Imp(Seq(k, Sp, Le, Sp, n), comparison)));
        var orderings = All(sigma, perm, Ex(pi, perm, prefixes));
        var assumptions = Imp(Call(Povm, p), Imp(Call(Povm, q),
            Imp(Call("BlockBistoch", b), Imp(Call("IsBlockProduct", b, p, q), orderings))));
        return Disp(Equal(Call("claim"), All(n, Nat, All(d, Nat,
            All(p, Family(n, d), All(q, Family(n, d), All(b, BlocksType(n, d), assumptions)))))));
    }
}
