using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class EntanglementBreakingNormCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/kopel2026sharpnorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every dimension d ≥ 2, every Hermitian traceless basis λ₁, …, λ_{d²−1} with tr(λᵢλⱼ) = 2δᵢⱼ and every real B > d(d − 1)/2, some entanglement-breaking channel has Bloch data (A, c) with ‖A‖_*² + B|c|² > (d − 1)²; hence d(d − 1)/2 is the largest coefficient of |c|² for which the norm inequality for entanglement-breaking channels can hold.",
        H("Optimality of the coefficient in the entanglement-breaking norm inequality"),
        Blocks(
            Node("is-bloch-basis", "Generalised Bloch bases", "IsBlochBasis", Disp(BlochBasisFormula()),
                "A family λ of d² − 1 complex d × d matrices, indexed by Fin(d² − 1) with d² − 1 computed in the natural numbers, is a generalised Bloch basis when every member is Hermitian and traceless and tr(λᵢλⱼ) equals 2 for i = j and 0 otherwise; ite(p, x, y) denotes x when p holds and y otherwise. Together with the identity such a family spans the d × d matrices, and every density matrix is I/d + ½ Σᵢ rᵢλᵢ with real rᵢ = tr(λᵢρ). For d = 2 the Pauli matrices are an example and for general d the generalised Gell-Mann matrices.",
                DescribeRole.Definition, Lit()),
            Node("is-entanglement-breaking", "Entanglement-breaking maps in Holevo form",
                "IsEntanglementBreaking", Disp(EntanglementBreakingFormula()),
                "A linear map φ on complex d × d matrices is entanglement breaking when it has a Holevo form φ(X) = Σ_a tr(E_a X) σ_a with finitely many positive semidefinite E_a summing to the identity and positive semidefinite σ_a of trace 1. MatrixMap is the frozen type of linear maps between matrix spaces of D5/S3/Quantum/Foundation/FiniteKrausChannel, and IsPOVM is the frozen predicate of D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation: every E_a is positive semidefinite and Σ_a E_a = I. A map of this form is completely positive and trace preserving, and (id ⊗ φ)(ρ) is separable for every state ρ.",
                DescribeRole.Definition, Lit()),
            Node("bloch-a", "The linear part of the Bloch representation", "blochA", Disp(BlochAFormula()),
                "The real (d² − 1) × (d² − 1) matrix A with A_{ij} = ½ Re tr(λᵢ φ(λⱼ)). For a generalised Bloch basis λ and a trace-preserving, Hermiticity-preserving φ, the Bloch vector r of a state, rᵢ = tr(λᵢρ), is sent to Ar + c, with c the translation part defined next.",
                DescribeRole.Definition, Lit()),
            Node("bloch-c", "The translation part of the Bloch representation", "blochC", Disp(BlochCFormula()),
                "The real vector c with cᵢ = Re tr(λᵢ φ(I/d)), the Bloch vector of the image of the maximally mixed state; cast denotes the inclusion of the natural numbers in ℂ.",
                DescribeRole.Definition, Lit()),
            Node("claim", "The coefficient cannot be increased", "claim", Disp(ClaimFormula()),
                "Theorem 1 of arXiv:2609.27906v1 states that the Bloch data (A, c) of an entanglement-breaking channel on d × d matrices satisfy ‖A‖_*² + (d(d − 1)/2)|c|² ≤ (d − 1)², with ‖A‖_* the trace norm and |c| the Euclidean norm, and item 3 of its open questions asks whether the coefficient d(d − 1)/2 is optimal. The inequality with a coefficient κ in place of d(d − 1)/2 becomes stronger as κ grows, so the coefficient is optimal exactly when no larger κ is admissible. The claim states this: for every d ≥ 2, every generalised Bloch basis and every real B > d(d − 1)/2 there is an entanglement-breaking φ with (d − 1)² < ‖A‖_*² + B|c|². Theorem 1 itself is not part of the statement. traceNorm is the frozen trace norm tr √(AᵀA) of D5/S3/Quantum/Foundation/FiniteTraceDistance; here cast denotes the inclusion of the natural numbers in ℝ.",
                DescribeRole.Definition, Lit()),
            Node("result", "The coefficient d(d − 1)/2 is optimal", "result", Disp(V("claim")),
                "Let P be the matrix unit E₀₀ and φ(X) = tr(X) P. φ has the Holevo form with the one-element measurement {I} and the state P. Every λⱼ is traceless, so φ(λⱼ) = 0 and A = 0, whose trace norm is 0. Since φ(I/d) = P, cᵢ = Re tr(λᵢP) = Re (λᵢ)₀₀, and (λᵢ)₀₀ is real because λᵢ is Hermitian. The d² matrices I/√d and λᵢ/√2 are orthonormal for the Hilbert–Schmidt inner product ⟨M, N⟩ = tr(M†N), hence an orthonormal basis of the d²-dimensional space of d × d matrices, and Parseval's identity for P gives 1 = tr(P†P) = 1/d + ½ Σᵢ (λᵢ)₀₀². Therefore |c|² = 2(d − 1)/d and ‖A‖_*² + B|c|² = 2(d − 1)B/d, which exceeds (d − 1)² exactly when B > d(d − 1)/2.",
                DescribeRole.Theorem, Repo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kopel-2026-eb-norm-coefficient"),
                    ResolutionKind.Proved)))));

    private static Formula BlochBasisFormula()
    {
        Formula hermitian = Parenthesized(For(V("i"), Index(), Call("IsHermitian", Lam(V("i")))));
        Formula traceless = Parenthesized(For(V("i"), Index(), Equal(Call("tr", Lam(V("i"))), D(0))));
        Formula gram = Parenthesized(For(Seq(V("i"), Comma, Sp, V("j")), Index(), Equal(
            Call("tr", Seq(Lam(V("i")), Sp, Lam(V("j")))),
            Call("ite", Seq(V("i"), Sp, Eq, Sp, V("j")), D(2), D(0)))));
        Formula body = Parenthesized(Seq(hermitian, Sp, Land, Sp, traceless, Sp, Land, Sp, gram));
        return For(V("d"), Nat(), For(LambdaLower, BasisType(),
            IffOf(Call("IsBlochBasis", V("d"), LambdaLower), body)));
    }

    private static Formula EntanglementBreakingFormula()
    {
        Formula states = Parenthesized(For(V("a"), Call("Fin", V("k")), Seq(
            Call("PosSemidef", Sig(V("a"))), Sp, Land, Sp, Equal(Call("tr", Sig(V("a"))), D(1)))));
        Formula holevoSum = Seq(F.Sum, Underscore, Grp(V("a"), Colon, Call("Fin", V("k"))), Sp,
            Call("tr", Seq(V("E"), Parenthesized(V("a")), Sp, V("X"))), Sp, Sig(V("a")));
        Formula holevo = Parenthesized(For(V("X"), MatType(),
            Equal(Seq(F.Phi, Parenthesized(V("X"))), holevoSum)));
        Formula body = Parenthesized(Seq(
            Exists, Sp, V("k"), Colon, Sp, Nat(), Comma, Sp,
            Exists, Sp, V("E"), Comma, Sp, SigmaLower, Colon, Sp, Call("Fin", V("k")), Sp, To, Sp, MatType(),
            Comma, Sp, Call("IsPOVM", V("E")), Sp, Land, Sp, states, Sp, Land, Sp, holevo));
        return For(V("d"), Nat(), For(F.Phi, MapType(),
            IffOf(Call("IsEntanglementBreaking", F.Phi), body)));
    }

    private static Formula BlochAFormula()
    {
        Formula entry = Seq(Call("blochA", LambdaLower, F.Phi), Parenthesized(Seq(V("i"), Comma, Sp, V("j"))));
        Formula value = Seq(Frac2(D(1), D(2)), Sp,
            Call("re", Call("tr", Seq(Lam(V("i")), Sp, F.Phi, Parenthesized(Lam(V("j")))))));
        return For(V("d"), Nat(), For(LambdaLower, BasisType(), For(F.Phi, MapType(),
            For(Seq(V("i"), Comma, Sp, V("j")), Index(), Equal(entry, value)))));
    }

    private static Formula BlochCFormula()
    {
        Formula entry = Seq(Call("blochC", LambdaLower, F.Phi), Parenthesized(V("i")));
        Formula mixed = Parenthesized(Seq(Frac2(D(1), Cast(V("d"))), Sp, V("I")));
        Formula value = Call("re", Call("tr", Seq(Lam(V("i")), Sp, F.Phi, mixed)));
        return For(V("d"), Nat(), For(LambdaLower, BasisType(), For(F.Phi, MapType(),
            For(V("i"), Index(), Equal(entry, value)))));
    }

    private static Formula ClaimFormula()
    {
        Formula threshold = Seq(Frac2(Seq(Cast(V("d")), Sp, DMinusOne()), D(2)), Sp, Lt, Sp, V("B"));
        Formula violation = Seq(
            Sq(DMinusOne()), Sp, Lt, Sp,
            Sq(Call("traceNorm", Call("blochA", LambdaLower, F.Phi))), Sp, Plus, Sp,
            V("B"), Sp, F.Sum, Underscore, Grp(V("i"), Colon, Index()), Sp,
            Sq(Parenthesized(Seq(Call("blochC", LambdaLower, F.Phi), Parenthesized(V("i"))))));
        Formula witness = Seq(Exists, Sp, F.Phi, Colon, Sp, MapType(), Comma, Sp,
            Call("IsEntanglementBreaking", F.Phi), Sp, Land, Sp, violation);
        Formula body = For(V("d"), Nat(), Imp(Seq(D(2), Sp, Leq, Sp, V("d")),
            For(LambdaLower, BasisType(), Imp(Call("IsBlochBasis", V("d"), LambdaLower),
                For(V("B"), Real(), Imp(threshold, witness))))));
        return IffOf(V("claim"), Parenthesized(body));
    }

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Repo() => AssessedProvenance.FromRepo(Source);

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Sq(Formula x) => Seq(x, Caret, Grp(D(2)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Cx() => Seq(Mathbb, Grp(V("C")));
    private static Formula Cast(Formula value) => Call("cast", value);
    private static Formula MatType() => Call("Matrix", Call("Fin", V("d")), Call("Fin", V("d")), Cx());
    private static Formula MapType() => Call("MatrixMap", Call("Fin", V("d")), Call("Fin", V("d")), Cx());
    private static Formula Index() => Call("Fin", Seq(Sq(V("d")), Sp, Minus, Sp, D(1)));
    private static Formula BasisType() => Seq(Index(), Sp, To, Sp, MatType());
    private static Formula Lam(Formula i) => Seq(LambdaLower, Parenthesized(i));
    private static Formula Sig(Formula a) => Seq(SigmaLower, Parenthesized(a));
    private static Formula DMinusOne() => Parenthesized(Seq(Cast(V("d")), Sp, Minus, Sp, D(1)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Frac2(Formula n, Formula d) => new Formula.Fraction(n, d);
}
