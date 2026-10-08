using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ProductUnitaryPPTSquaredDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/ProductUnitaryPPTSquared.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/garciavelo2026schwarz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For all n₁, n₂ ≥ 2 and real λ₀₁, λ₁₀, λ₁₁, if the unital map with weights 1, λ₀₁, λ₁₀ and λ₁₁ on the four isotypic components of n₁n₂ × n₁n₂ matrices has a positive semidefinite Choi matrix whose partial transpose is also positive semidefinite, then the Choi matrix of the map composed with itself is a finite sum of Kronecker products of positive semidefinite matrices across input and output.",
        H("PPT channels with product-unitary symmetry become entanglement breaking after one composition"),
        Blocks(
            Node("choi", "The Choi matrix", "choi", Disp(
                ForIota(For(Psi, Call("MatrixMap", Iota, Iota, Cx()), Equal(
                    Call("choi", Psi),
                    Seq(F.Sum, Underscore, Grp(V("p"), Comma, V("q")), Sp,
                        Call("kron", Call("single", V("p"), V("q"), D(1)),
                            Seq(Psi, Parenthesized(Call("single", V("p"), V("q"), D(1)))))))))),
                "For a finite type ι with decidable equality and a linear map ψ on square complex matrices indexed by ι, choi(ψ) = Σ_{p,q} E_pq ⊗ ψ(E_pq), a matrix indexed by pairs (input index, output index); kron is the Kronecker product of matrices and single(p, q, 1) is the matrix unit E_pq.",
                DescribeRole.Definition, Repo()),
            Node("flat", "Flattening the two tensor factors", "flat", Disp(
                For(Seq(N(1), Comma, Sp, N(2)), Nat(), Equal(
                    Call("flat", N(1), N(2)),
                    Call("prodCongr", V("finProdFinEquiv"), V("finProdFinEquiv"))))),
                "The equivalence that flattens the input pair (p₁, p₂) and the output pair (r₁, r₂) separately by Mathlib's finProdFinEquiv from Fin n₁ × Fin n₂ to Fin (n₁n₂). It turns a matrix indexed by ((p₁, p₂), (r₁, r₂)) into a matrix on Fin (n₁n₂) × Fin (n₁n₂) with the input factor first, the index type of separableCone.",
                DescribeRole.Definition, Repo()),
            Node("phi-comp", "Composition multiplies the weights", "phi_comp", Disp(
                For(Seq(N(1), Comma, Sp, N(2)), Nat(),
                    Imp(Seq(D(1), Sp, Leq, Sp, N(1)), Imp(Seq(D(1), Sp, Leq, Sp, N(2)),
                        For(Seq(V("a"), Comma, Sp, V("b"), Comma, Sp, V("c"), Comma, Sp,
                                Pr("a"), Comma, Sp, Pr("b"), Comma, Sp, Pr("c")), Cx(),
                            Equal(
                                Seq(Call("phi", N(1), N(2), V("a"), V("b"), V("c")), Sp, Circ, Sp,
                                    Call("phi", N(1), N(2), Pr("a"), Pr("b"), Pr("c"))),
                                Call("phi", N(1), N(2), Seq(V("a"), Sp, Pr("a")), Seq(V("b"), Sp, Pr("b")),
                                    Seq(V("c"), Sp, Pr("c"))))))))),
                "D and Q are complementary idempotents on each factor (D ∘ D = D, D ∘ Q = Q ∘ D = 0, Q ∘ Q = Q), and the tensor product of maps is multiplicative on Kronecker products, so composing two maps of the family multiplies their weights. In particular Φ ∘ Φ has the weights λ₀₁², λ₁₀² and λ₁₁².",
                DescribeRole.Theorem, Repo()),
            Node("claim", "PPT² for unital product-unitary-equivariant maps", "claim", Disp(IffOf(V("claim"), Parenthesized(
                For(Seq(N(1), Comma, Sp, N(2)), Nat(),
                    Imp(Seq(D(2), Sp, Leq, Sp, N(1), Comma, Sp, D(2), Sp, Leq, Sp, N(2)),
                        For(Seq(Lam(0, 1), Comma, Sp, Lam(1, 0), Comma, Sp, Lam(1, 1)), Seq(Mathbb, Grp(V("R"))),
                            Imp(Call("PosSemidef", Call("choi", PhiOf())),
                                Imp(Call("PosSemidef", Call("partialTranspose", Call("choi", PhiOf()))),
                                    Call("separableCone", Call("reindex", Call("flat", N(1), N(2)),
                                        Call("flat", N(1), N(2)),
                                        Call("choi", Parenthesized(Seq(PhiOf(), Sp, Circ, Sp, PhiOf()))))))))))))),
                "Here cast is the inclusion of ℝ in ℂ, and phi(n₁, n₂, λ₀₁, λ₁₀, λ₁₁) = D₁ ⊗ D₂ + λ₀₁ D₁ ⊗ Q₂ + λ₁₀ Q₁ ⊗ D₂ + λ₁₁ Q₁ ⊗ Q₂ is the unital map of D5/S3/Quantum/QuantumChannels/ProductUnitaryChoiSpectrum, with D(X) = tr(X) I/n and Q = id − D; for n₁, n₂ ≥ 2 these are exactly the unital, Hermiticity-preserving maps commuting with conjugation by U ⊗ V. partialTranspose transposes the output indices: (partialTranspose M)((p, r), (q, s)) = M((p, s), (q, r)). The two hypotheses say that Φ is completely positive and completely copositive (Φ is PPT). separableCone is the frozen cone of finite sums of Kronecker products A ⊗ B of positive semidefinite matrices, so the conclusion says that Φ ∘ Φ is entanglement breaking. The composition is needed: when n₁ ≠ n₂ there are PPT maps in this family that are not entanglement breaking.",
                DescribeRole.Definition, Repo()),
            Node("result", "PPT² in every dimension", "result", Disp(V("claim")),
                "Since D and Q are complementary idempotents, Φ ∘ Φ has weights λ₀₁², λ₁₀² and λ₁₁². Let ω be the vector of ℂⁿ ⊗ ℂⁿ with entry 1 at the pairs (i, i), K = ωωᵀ, and D = Σ_i E_ii ⊗ E_ii. Averaging vv* ⊗ v̄v̄* over the 4ⁿ vectors v = Σ_j θ_j e_j with θ_j ∈ {1, i, −1, −i} gives I + K − D, so I + K is separable; with v replaced on the output side by its twist by the characters m ↦ ζ^{km} of the n-th roots of unity, k = 1, …, n − 1, the same average gives (n − 1)I + D − K, so nI − K = that sum + Σ_{i≠j} E_ii ⊗ E_jj is separable. Grouped by factor, the Choi matrix of Φ ∘ Φ equals Σ_{r,s} N_rs S_r ⊗ S_s with S₀ = nI − K and S₁ = I + K on each factor, and the coefficients are n₁(n₁+1)n₂(n₂+1)·N₀₀ = 1 − (n₂+1)λ₀₁² − (n₁+1)λ₁₀² + (n₁+1)(n₂+1)λ₁₁², n₁(n₁+1)n₂(n₂+1)·N₀₁ = 1 + (n₂²−1)λ₀₁² − (n₁+1)λ₁₀² − (n₁+1)(n₂²−1)λ₁₁², the mirror image N₁₀, and N₁₁ with all signs positive. Testing the Choi matrix of Φ and its partial transpose on ω₁ ⊗ ω₂, ω ⊗ e₀₁, e₀₁ ⊗ e₀₁, e₀₀ ⊗ e₀₀ and the antisymmetric vectors e₀₁ − e₁₀ gives eight linear inequalities in λ. N₁₀ ≥ 0 and N₀₁ ≥ 0 follow from polynomial identities expressing 2n₁²n₂² N times the positive constant as a sum of products of two of these inequalities with nonnegative coefficients; N₀₀ ≥ 0 follows from |λ₀₁| ≤ 1/(n₂+1) and |λ₁₀| ≤ 1/(n₁+1), which are linear consequences of the inequalities. The source proves this property for (n₁, n₂) = (2, 2) and (2, 3).",
                DescribeRole.Theorem, Repo()))));

    private static AssessedProvenance Repo() => AssessedProvenance.FromRepo(Source);

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N(byte index) => Seq(V("n"), Underscore, D(index));
    private static Formula Lam(byte a, byte b) => Seq(LambdaLower, Underscore, Grp(D(a, b)));
    private static Formula PhiOf() =>
        Call("phi", N(1), N(2), Cast(Lam(0, 1)), Cast(Lam(1, 0)), Cast(Lam(1, 1)));
    private static Formula ForIota(Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(Iota, Colon, Sp, V("Type"))), Sp,
            OpenBracket, Call("Fintype", Iota), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", Iota), CloseBracket, Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Cx() => Seq(Mathbb, Grp(V("C")));
    private static Formula Cast(Formula value) => Call("cast", value);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pr(string name) => Seq(V(name), Apos);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
}
