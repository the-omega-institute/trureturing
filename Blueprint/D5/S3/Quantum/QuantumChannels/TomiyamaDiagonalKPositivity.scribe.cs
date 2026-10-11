using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class TomiyamaDiagonalKPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/bera2026tomiyama");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every 2 ≤ k ≤ d, the k-positive maps of the diagonal-perturbed Tomiyama family on d × d matrices are exactly those whose parameters lie in the quadrilateral spanned by the identity, the two extremal completely positive maps and the k-positive Tomiyama map.",
        H("The k-positive region of the diagonal-perturbed Tomiyama maps"),
        Blocks(
            Node("family", "The diagonal-perturbed Tomiyama family", "phi", Disp(Equal(
                Seq(Call("phi", V("d"), Alpha, Beta), Open, V("X"), Close),
                Seq(Parenthesized(Seq(D(1), Sp, Minus, Sp, Alpha, Sp, Minus, Sp, Beta)), Sp, V("X"), Sp, Plus, Sp,
                    Frac2(Alpha, V("d")), Sp, Call("tr", V("X")), Sp, V("I"), Sp, Plus, Sp,
                    Beta, Sp, Call("diag", V("X"))))),
                "Φ_{α,β} = (1 − α − β) id + α τ₀ + β Δ on d × d complex matrices, where τ₀(X) = tr(X) I/d and Δ keeps the diagonal of X, as in Eq. (6) of arXiv:2604.18600v1.",
                DescribeRole.Definition, Lit()),
            Node("k-positivity", "k-positivity", "KPositive", Disp(IffOf(
                Call("KPositive", V("k"), V("d"), Phi),
                For(V("Y"), Call("PSD", Times2(V("k"), V("d"))),
                    Seq(Call("kron", Call("id", V("k")), Phi), Open, V("Y"), Close, Sp, Geq, Sp, D(0))))),
                "A map Φ on d × d matrices is k-positive when id_k ⊗ Φ sends every positive semidefinite kd × kd matrix to a positive semidefinite matrix. The tensor product of maps is the frozen kron of D5/S3/Quantum/Foundation/FiniteKrausChannel, with the identity on k × k matrices as the first factor.",
                DescribeRole.Definition, Lit()),
            Node("quadrilateral", "The conjectured quadrilateral", "quadrilateral", Disp(Equal(
                Call("quadrilateral", V("d"), V("k")),
                Call("conv", Seq(OpenBrace,
                    Pair(D(0), D(0)), Comma, Sp,
                    Pair(D(0), Frac2(V("d"), Seq(V("d"), Minus, D(1)))), Comma, Sp,
                    Pair(Frac2(V("d"), Seq(V("d"), Minus, D(1))), Seq(Minus, Frac2(D(1), Seq(V("d"), Minus, D(1))))), Comma, Sp,
                    Pair(Frac2(Seq(V("k"), V("d")), Seq(V("k"), V("d"), Minus, D(1))), D(0)),
                    CloseBrace)))),
                "The convex hull in the (α, β) plane of the parameter points of Ψ₀ (the identity), Ψ₁ and Ψ₂ (the two completely positive vertices) and the Tomiyama map 𝒯_k, whose α is kd/(kd − 1).",
                DescribeRole.Definition, Lit()),
            Node("claim", "Conjecture 2.4 for 2 ≤ k ≤ d", "claim", Disp(IffOf(V("claim"), Parenthesized(
                For(Seq(V("d"), Comma, Sp, V("k")), Seq(Mathbb, Grp(V("N"))),
                    Imp(Seq(D(2), Sp, Leq, Sp, V("k"), Sp, Leq, Sp, V("d")),
                        For(Seq(Alpha, Comma, Sp, Beta), Seq(Mathbb, Grp(V("R"))),
                            IffOf(Call("KPositive", V("k"), V("d"), Call("phi", V("d"), Alpha, Beta)),
                                Member(Pair(Alpha, Beta), Call("quadrilateral", V("d"), V("k")))))))))),
                "Conjecture 2.4 of arXiv:2604.18600v1, \"A set of k-positive maps Φ_{α,β} forms a quadrilateral 𝒫_k = conv{Ψ₀, Ψ₁, Ψ₂, 𝒯_k}\", in the range 2 ≤ k ≤ d.",
                DescribeRole.Definition, Lit()),
            Node("fourier-rows", "Fourier rows", "fourierRows", Disp(
                For(Seq(V("d"), Comma, Sp, V("k")), Seq(Mathbb, Grp(V("N"))),
                    Imp(Seq(D(0), Sp, Lt, Sp, V("d"), Comma, Sp, V("k"), Sp, Leq, Sp, V("d")),
                        For(V("a"), Call("Fin", V("k")), For(V("j"), Call("Fin", V("d")),
                            Equal(Call("entry", Call("fourierRows", V("k"), V("d")), V("a"), V("j")),
                                Call("stdAddChar", Times2(Call("finEquiv", V("d"), V("j")),
                                    Call("finEquiv", V("d"), Call("castLE", V("a"))))))))))),
                "For positive d and k ≤ d, the k Fourier rows have entries χ_d(ja), where χ_d is the standard additive character on the residues modulo d and a is embedded from Fin k into Fin d.",
                DescribeRole.Definition, Repo()),
            Node("fourier-gram", "Orthogonality of Fourier rows", "fourierRows_gram", Disp(
                For(Seq(V("d"), Comma, Sp, V("k")), Seq(Mathbb, Grp(V("N"))),
                    Imp(Seq(D(0), Sp, Lt, Sp, V("d"), Comma, Sp, V("k"), Sp, Leq, Sp, V("d")),
                        Equal(Times2(Call("fourierRows", V("k"), V("d")),
                                Call("adjoint", Call("fourierRows", V("k"), V("d")))),
                            Times2(V("d"), Call("identity", V("k"))))))),
                "Distinct Fourier rows are orthogonal, and each has squared norm d. At k = d, division by the square root of d gives a unitary Fourier matrix; conjugation gives the negative-character convention.",
                DescribeRole.Theorem, Repo()),
            Node("result", "The k-positive region is the quadrilateral", "result", Disp(V("claim")),
                "Write ‖X‖² = Σ_{i,j} |X_ij|² for the squared Frobenius norm and Q(X) = (α/d)‖X‖² + β Σ_i |X_ii|² + (1 − α − β)|tr X|². For vectors u, w in ℂ^k ⊗ ℂ^d with coefficient matrices U, W, the value of (id_k ⊗ Φ_{α,β})(ww*) on u is Q(U*W), so k-positivity means Q ≥ 0 on every U*W. Four tests give the four edges: the matrix unit E₁₂ gives α ≥ 0; E₁₁ − E₂₂, which needs k ≥ 2, gives α/d + β ≥ 0; the coordinate projection onto k basis vectors gives (kd − 1)α + d(k − 1)β ≤ kd; and the Fourier projection AA*, with A the first k columns of the normalized d × d discrete Fourier matrix, has rank k and every diagonal entry k/d, so it gives (kd − 1)α + k(d − 1)β ≤ kd for every k ≤ d. Conversely the k-positive parameters form a convex set containing the four vertices, where Q ≥ 0 follows from Cauchy–Schwarz on the diagonal and from |tr(U*W)|² ≤ k‖U*W‖².",
                DescribeRole.Theorem, Repo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bera-2026-tomiyama-diagonal-k-positivity"),
                    ResolutionKind.Proved)))));

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Repo() => AssessedProvenance.FromRepo();

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Times2(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Frac2(Formula n, Formula d) => new Formula.Fraction(n, d);
}
