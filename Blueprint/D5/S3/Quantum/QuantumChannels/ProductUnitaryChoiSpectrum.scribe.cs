using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ProductUnitaryChoiSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/garciavelo2026schwarz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For all positive n₁ and n₂, the Choi matrix of the unital map that acts on the four isotypic components of n₁n₂ × n₁n₂ matrices with weights 1, λ₀₁, λ₁₀ and λ₁₁ has its eigenvalues among four values given by explicit formulas, taken with multiplicities 1, n₁² − 1, n₂² − 1 and (n₁² − 1)(n₂² − 1); coinciding values add their multiplicities.",
        H("The Choi spectrum of unital product-unitary-equivariant maps"),
        Blocks(
            Node("depol", "The trace-to-identity map", "depol", Disp(
                For(V("n"), Nat(), For(V("X"), MatType(V("n")), Equal(
                    Seq(Call("depol", V("n")), Parenthesized(V("X"))),
                    Seq(Frac2(Call("tr", V("X")), Cast(V("n"))), Sp, V("I")))))),
                "On n × n complex matrices, D(X) = tr(X) I/n; cast denotes the inclusion of the natural numbers in ℂ. Its image is the multiples of the identity, and D is the identity there, so D is the projection onto the trivial component of the conjugation action of the unitary group.",
                DescribeRole.Definition, Lit()),
            Node("compl", "The complementary projection", "compl", Disp(
                For(V("n"), Nat(), For(V("X"), MatType(V("n")), Equal(
                    Seq(Call("compl", V("n")), Parenthesized(V("X"))),
                    Seq(V("X"), Sp, Minus, Sp, Call("depol", V("n")), Parenthesized(V("X"))))))),
                "Q(X) = X − D(X), the projection onto the trace-zero matrices.",
                DescribeRole.Definition, Lit()),
            Node("phi", "The unital product-unitary-equivariant map", "phi", Disp(
                For(Seq(N(1), Comma, Sp, N(2)), Nat(),
                    For(Seq(Lam(0, 1), Comma, Sp, Lam(1, 0), Comma, Sp, Lam(1, 1)), Cx(), Equal(
                        Call("phi", N(1), N(2), Lam(0, 1), Lam(1, 0), Lam(1, 1)),
                        Seq(Call("kron", Call("depol", N(1)), Call("depol", N(2))), Sp, Plus, Sp,
                            Lam(0, 1), Sp, Call("kron", Call("depol", N(1)), Call("compl", N(2))), Sp, Plus, Sp,
                            Lam(1, 0), Sp, Call("kron", Call("compl", N(1)), Call("depol", N(2))), Sp, Plus, Sp,
                            Lam(1, 1), Sp, Call("kron", Call("compl", N(1)), Call("compl", N(2)))))))),
                "The map Φ on n₁n₂ × n₁n₂ complex matrices with weight 1 on D ⊗ D and weights λ₀₁, λ₁₀, λ₁₁ on D ⊗ Q, Q ⊗ D and Q ⊗ Q. The tensor product of maps is the frozen kron of D5/S3/Quantum/Foundation/FiniteKrausChannel. Φ is unital, and it commutes with conjugation by U ⊗ V for unitary U and V; for n₁, n₂ ≥ 2 every unital map with this symmetry has this form, and it preserves Hermiticity exactly when the weights are real. On matrix units, with a = (1 − λ₀₁ − λ₁₀ + λ₁₁)/(n₁n₂), b = (λ₀₁ − λ₁₁)/n₁, c = (λ₁₀ − λ₁₁)/n₂ and d = λ₁₁, Φ(E_ij ⊗ F_kl) = a δ_ij δ_kl I + b δ_ij I ⊗ F_kl + c δ_kl E_ij ⊗ I + d E_ij ⊗ F_kl.",
                DescribeRole.Definition, Lit()),
            Node("omega", "The diagonal pair vector", "omega", Disp(
                For(V("n"), Nat(), For(Seq(V("i"), Comma, Sp, V("j")), Call("Fin", V("n")), Equal(
                    Seq(Call("omega", V("n")), Parenthesized(Seq(V("i"), Comma, Sp, V("j")))),
                    Seq(OpenBracket, V("i"), Sp, Eq, Sp, V("j"), CloseBracket))))),
                "The vector on the pairs (i, j) of indices in {0, …, n − 1} with entry 1 when i = j and 0 otherwise; the bracket [i = j] denotes this indicator. It is the unnormalized maximally entangled vector Σ_i e_i ⊗ e_i.",
                DescribeRole.Definition, Repo()),
            Node("omega-dot-omega", "The squared length of the diagonal pair vector", "omega_dot_omega", Disp(
                For(V("n"), Nat(),
                    Equal(Call("dotProduct", Call("omega", V("n")), Call("omega", V("n"))), Cast(V("n"))))),
                "ω has exactly n entries equal to 1 and the others 0, so ω · ω = n as a complex number.",
                DescribeRole.Theorem, Repo()),
            Node("kmat", "The Choi matrix of the identity map", "kmat", Disp(For(V("n"), Nat(), Equal(
                Call("kmat", V("n")),
                Call("vecMulVec", Call("omega", V("n")), Call("omega", V("n")))))),
                "K = ωωᵀ, the matrix on pairs with entry ω(x)ω(y) at (x, y); it is the Choi matrix Σ_{i,j} E_ij ⊗ E_ij of the identity map on n × n matrices.",
                DescribeRole.Definition, Repo()),
            Node("dmat", "The Choi matrix of the trace-to-identity map", "dmat", Disp(For(V("n"), Nat(), Equal(
                Call("dmat", V("n")),
                Seq(Frac2(D(1), Cast(V("n"))), Sp, V("I"))))),
                "I/n on pairs of indices: the Choi matrix of depol(n).",
                DescribeRole.Definition, Repo()),
            Node("qmat", "The Choi matrix of the complementary projection", "qmat", Disp(For(V("n"), Nat(), Equal(
                Call("qmat", V("n")),
                Seq(Call("kmat", V("n")), Sp, Minus, Sp, Call("dmat", V("n")))))),
                "K − I/n: the Choi matrix of compl(n).",
                DescribeRole.Definition, Repo()),
            Node("choi-reindex", "The Choi matrix grouped by factor", "choi_reindex", Disp(
                For(Seq(N(1), Comma, Sp, N(2)), Seq(Mathbb, Grp(V("N"))),
                    For(Seq(Lam(0, 1), Comma, Sp, Lam(1, 0), Comma, Sp, Lam(1, 1)), Seq(Mathbb, Grp(V("C"))),
                        Equal(
                            Call("reindex", V("prodProdProdComm"), V("prodProdProdComm"),
                                Seq(F.Sum, Underscore, Grp(V("p"), Comma, V("q")), Sp,
                                    Call("kron", Call("single", V("p"), V("q"), D(1)),
                                        Seq(Call("phi", N(1), N(2), Lam(0, 1), Lam(1, 0), Lam(1, 1)),
                                            Parenthesized(Call("single", V("p"), V("q"), D(1))))))),
                            Seq(Call("kron", Call("dmat", N(1)), Call("dmat", N(2))), Sp, Plus, Sp,
                                Lam(0, 1), Sp, Call("kron", Call("dmat", N(1)), Call("qmat", N(2))), Sp, Plus, Sp,
                                Lam(1, 0), Sp, Call("kron", Call("qmat", N(1)), Call("dmat", N(2))), Sp, Plus, Sp,
                                Lam(1, 1), Sp, Call("kron", Call("qmat", N(1)), Call("qmat", N(2)))))))),
                "The Choi matrix C_Φ = Σ_{p,q} E_pq ⊗ Φ(E_pq) is indexed by pairs ((p₁, p₂), (r₁, r₂)) of an input and an output index. Reindexing both sides by the regrouping prodProdProdComm, which sends ((p₁, p₂), (r₁, r₂)) to ((p₁, r₁), (p₂, r₂)), turns C_Φ into the weighted sum of Kronecker products of the single-factor Choi matrices dmat and qmat, with the weights of phi. Here kron is the Kronecker product of matrices. In the basis of I, I ⊗ K, K ⊗ I and K ⊗ K this is the Choi matrix a I + b (I ⊗ K₂) + c (K₁ ⊗ I) + d (K₁ ⊗ K₂) displayed in the source, with a = (1 − λ₀₁ − λ₁₀ + λ₁₁)/(n₁n₂), b = (λ₀₁ − λ₁₁)/n₁, c = (λ₁₀ − λ₁₁)/n₂ and d = λ₁₁.",
                DescribeRole.Theorem, Lit()),
            Node("claim", "The conjectured Choi spectrum", "claim", Disp(IffOf(V("claim"), Parenthesized(
                For(Seq(N(1), Comma, Sp, N(2)), Seq(Mathbb, Grp(V("N"))),
                    Imp(Seq(D(1), Sp, Leq, Sp, N(1), Comma, Sp, D(1), Sp, Leq, Sp, N(2)),
                        For(Seq(Lam(0, 1), Comma, Sp, Lam(1, 0), Comma, Sp, Lam(1, 1)), Seq(Mathbb, Grp(V("C"))),
                            Equal(
                                Call("charpoly", Seq(F.Sum, Underscore, Grp(V("p"), Comma, V("q")), Sp,
                                    Call("kron", Call("single", V("p"), V("q"), D(1)),
                                        Seq(Call("phi", N(1), N(2), Lam(0, 1), Lam(1, 0), Lam(1, 1)),
                                            Parenthesized(Call("single", V("p"), V("q"), D(1))))))),
                                Seq(Factor(EigOne()), Sp,
                                    Pow(Factor(EigTwo()), Seq(Sq(N(1)), Minus, D(1))), Sp,
                                    Pow(Factor(EigThree()), Seq(Sq(N(2)), Minus, D(1))), Sp,
                                    Pow(Factor(EigFour()), Seq(Parenthesized(Seq(Sq(N(1)), Minus, D(1))),
                                        Parenthesized(Seq(Sq(N(2)), Minus, D(1))))))))))))),
                "The conjecture of Remark V.2 of arXiv:2601.02282v1: for every n₁ and n₂, the eigenvalues of the Choi matrix C_Φ = Σ_{p,q} E_pq ⊗ Φ(E_pq) are the four values of Lemma V.8, with multiplicities 1, n₁² − 1, n₂² − 1 and (n₁² − 1)(n₂² − 1). The characteristic polynomial records the eigenvalues with their algebraic multiplicities; when two of the four values coincide their multiplicities add. The source states the formulas for n₁, n₂ ∈ {2, 3} and real weights; here n₁, n₂ ≥ 1 and the weights are complex. In the four roots the dimensions are cast to ℂ; the multiplicity exponents n₁² − 1, n₂² − 1 and (n₁² − 1)(n₂² − 1) are natural numbers.",
                DescribeRole.Definition, Lit()),
            Node("result", "The Choi spectrum in every dimension", "result", Disp(V("claim")),
                "Write ω for the vector of ℂ^n ⊗ ℂ^n with entry 1 at the pairs (i, i) and 0 elsewhere, and K = ωωᵀ. The Choi matrix of D is I/n and that of Q is K − I/n. Grouping the indices of C_Φ by factor turns it into a I + b (I ⊗ K₂) + c (K₁ ⊗ I) + d (K₁ ⊗ K₂). Let e₀ be the basis vector at the pair (0, 0) and u = ω − e₀; since e₀ᵀu = 0, the shear S = I + u e₀ᵀ has inverse I − u e₀ᵀ, sends e₀ to ω, and conjugates K to the matrix whose only nonzero row is the row of (0, 0), with diagonal entry n there. Conjugating by S₁ ⊗ S₂ makes the matrix block upper triangular for the blocks given by whether the first and the second index equals (0, 0). Each diagonal block is a multiple of the identity: of size 1 and value a + bn₂ + cn₁ + dn₁n₂, of size n₂² − 1 and value a + cn₁, of size n₁² − 1 and value a + bn₂, and of size (n₁² − 1)(n₂² − 1) and value a. Substituting a, b, c and d gives the four values of the claim.",
                DescribeRole.Theorem, Repo()))));

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Repo() => AssessedProvenance.FromRepo(Source);

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N(byte index) => Seq(V("n"), Underscore, D(index));
    private static Formula Lam(byte a, byte b) => Seq(LambdaLower, Underscore, Grp(D(a, b)));
    private static Formula Sq(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Pow(Formula x, Formula e) => Seq(x, Caret, Grp(e));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Factor(Formula root) => Parenthesized(Seq(V("X"), Sp, Minus, Sp, root));
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Cx() => Seq(Mathbb, Grp(V("C")));
    private static Formula Cast(Formula value) => Call("cast", value);
    private static Formula MatType(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Cx());
    private static Formula M(byte index) => Parenthesized(Seq(Sq(Cast(N(index))), Minus, D(1)));
    private static Formula Over(Formula numerator) => Frac2(numerator, Seq(Cast(N(1)), Sp, Cast(N(2))));
    private static Formula EigOne() => Over(Seq(D(1), Sp, Plus, Sp, M(2), Lam(0, 1),
        Sp, Plus, Sp, M(1), Lam(1, 0), Sp, Plus, Sp, M(1), M(2), Lam(1, 1)));
    private static Formula EigTwo() => Over(Seq(D(1), Sp, Plus, Sp, M(2), Lam(0, 1),
        Sp, Minus, Sp, Lam(1, 0), Sp, Minus, Sp, M(2), Lam(1, 1)));
    private static Formula EigThree() => Over(Seq(D(1), Sp, Minus, Sp, Lam(0, 1), Sp, Plus, Sp,
        M(1), Lam(1, 0), Sp, Minus, Sp, M(1), Lam(1, 1)));
    private static Formula EigFour() => Over(Seq(D(1), Sp, Minus, Sp, Lam(0, 1), Sp, Minus, Sp, Lam(1, 0), Sp, Plus, Sp,
        Lam(1, 1)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Frac2(Formula n, Formula d) => new Formula.Fraction(n, d);
}
