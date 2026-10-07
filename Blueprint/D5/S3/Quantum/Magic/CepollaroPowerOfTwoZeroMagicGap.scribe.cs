using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class CepollaroPowerOfTwoZeroMagicGapDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/cepollaro2025stabilizer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every qudit dimension divisible by four, and so for every power of two at least four, some three-dimensional subspace has zero average stabilizer entropy gap.",
        H("Zero-magic-gap three-dimensional subspaces in every power-of-two dimension"),
        Blocks(
            Node("displacement-phase", "The displacement phase", "tau", Disp(Equal(Call("tau", V("d")),
                Seq(Minus, Call("exp", Frac2(Seq(Pi, Sp, V("i")), V("d")))))),
                "The phase τ = −e^{iπ/d} of the displacement operators, as in §II.A of arXiv:2512.23013v1.",
                DescribeRole.Definition, Lit()),
            Node("displacement", "The displacement operators", "paperDisplacement", Disp(For(V("a"),
                Times2(ZModD(), ZModD()), Equal(Call("paperDisplacement", V("d"), V("a")),
                    Dot2(Pow(Call("tau", V("d")), Times2(Sub(V("a"), D(1)), Sub(V("a"), D(2)))),
                        Call("displacement", V("d"), Sub(V("a"), D(1)), Sub(V("a"), D(2))))))),
                "D_a = τ^{a₁a₂} X^{a₁} Z^{a₂} for a = (a₁, a₂) in (ℤ/dℤ)². The word X^{a₁} Z^{a₂} is the frozen Weyl displacement of D5/S3/Quantum/Algebra/WeylDisplacement, built from the shift X|k⟩ = |k + 1⟩ and the clock Z|k⟩ = ω^k|k⟩, ω = e^{2πi/d}, of D5/S3/Observer/WindowRegister; the phase does not affect any quantity below because each operator occurs together with its adjoint.",
                DescribeRole.Definition, Lit()),
            Node("fourth-power", "The fourth tensor power", "power4", Disp(Equal(Call("power4", V("V")),
                Call("productMap", Seq(V("i"), Sp, Mapsto, Sp, V("V"))))),
                "V^{⊗4} for a rectangular matrix V, written with the frozen fourfold product productMap of D5/S3/Quantum/Recovery/PurifiedLocalPath, whose entry at (x, y) is the product over the four factors of the entries at (x_i, y_i).",
                DescribeRole.Definition, Repo()),
            Node("alternating-power", "The alternating fourfold product", "alt", Disp(Equal(Call("alt", V("A")),
                Call("productMap", Seq(V("A"), Comma, Sp, Dagger(V("A")), Comma, Sp, V("A"), Comma, Sp, Dagger(V("A")))))),
                "A ⊗ A† ⊗ A ⊗ A†, the summand of Q.",
                DescribeRole.Definition, Repo()),
            Node("permutation-operator", "The permutation operators", "T", Disp(Equal(
                App2(Call("T", V("H"), SigmaLower), V("x"), V("y")),
                Call("ite", Equal(V("x"), Seq(V("y"), Sp, Circ, Sp, Seq(SigmaLower, Caret, Grp(Seq(Minus, D(1)))))), D(1), D(0)))),
                "T_σ permutes the four tensor factors of a fourfold tensor power over a finite index type H (it is the permutation matrix of the induced permutation of index tuples); the paper writes T_σ = Σ |σ(i,j,k,l)⟩⟨ijkl|.",
                DescribeRole.Definition, Lit()),
            Node("q-operator", "The stabilizer entropy operator", "Q", Disp(Equal(Call("Q", V("d")),
                Dot2(Pow(V("d"), Seq(Minus, D(2))), Seq(Sum, Underscore, Grp(V("a")), Sp,
                    Call("alt", Call("paperDisplacement", V("d"), V("a"))))))),
                "Q = d^{-2} Σ_a (D_a ⊗ D_a†)^{⊗2}, so that the linear stabilizer entropy of a pure state is M(ψ) = 1 − d tr(Q ψ^{⊗4}).",
                DescribeRole.Definition, Lit()),
            Node("fourth-moment", "The Haar fourth moment in closed form", "A4", Disp(Equal(Call("A4", V("H")),
                Dot2(Pow(Call("binom", Plus2(Seq(Vert, Sp, V("H"), Sp, Vert), D(3)), D(4)), Seq(Minus, D(1))),
                    Dot2(Frac2(D(1), D(2, 4)), Seq(Sum, Underscore, Grp(Member(SigmaLower, V("S4"))), Sp,
                        Call("T", V("H"), SigmaLower)))))),
                "A₄ is the paper's closed form of the Haar average E_U[(UψU†)^{⊗4}], the normalized projector onto the symmetric subspace of four tensor factors. The module takes this closed form as the definition; the Schur–Weyl identity with the Haar integral is quoted from the paper and not formalized.",
                DescribeRole.Definition, Lit()),
            Node("extrinsic-score", "The average extrinsic term", "score", Disp(Equal(Call("score", V("V")),
                Times2(V("dB"), Call("tr", Seq(Call("Q", V("dB")), Sp, Call("power4", V("V")), Sp, Call("A4", Call("Fin", D(3))), Sp,
                    Dagger(Call("power4", V("V")))))))),
                "For an isometry V from ℂ³ into ℂ^{d_B}, the term d_B tr(Q_B E^{⊗4}(A₄)) of the gap, with E(ρ) = VρV†.",
                DescribeRole.Definition, Lit()),
            Node("ase-gap", "The average stabilizer entropy gap", "aseGap", Disp(Equal(Call("aseGap", V("V")),
                Seq(Times2(D(3), Call("tr", Seq(Call("Q", D(3)), Sp, Call("A4", Seq(Mathbb, Grp(V("Z")), Slash, D(3), Mathbb, Grp(V("Z"))))))), Sp, Minus, Sp, Call("score", V("V"))))),
                "ΔM(E) = d_S tr(Q_S A₄) − d_B tr(Q_B E^{⊗4}(A₄)) for d_S = 3, as in §III of the paper.",
                DescribeRole.Definition, Lit()),
            Node("claim", "The power-of-two observation", "claim", Disp(IffOf(V("claim"), Parenthesized(
                For(V("m"), Seq(Mathbb, Grp(V("N"))), Imp(Leq2(D(2), V("m")),
                    Seq(Exists, Sp, V("V"), Colon, Sp, Call("Matrix", Seq(Mathbb, Grp(V("Z")), Slash, Pow(D(2), V("m")), Mathbb, Grp(V("Z"))), Call("Fin", D(3)), Seq(Mathbb, Grp(V("C")))),
                        Comma, Sp, And(Equal(Times2(Dagger(V("V")), V("V")), D(1)), Equal(Call("aseGap", V("V")), D(0))))))))),
                "The observation of §V.A of arXiv:2512.23013v1, \"when d_B is a power of 2, a zero ASE subspace of dimension three is always achievable\": for every m ≥ 2 some isometry from ℂ³ into ℂ^{2^m} has zero gap (ℂ² has no three-dimensional subspace).",
                DescribeRole.Definition, Lit()),
            Node("result", "Every power of two at least four has a zero-gap three-dimensional subspace", "result", Disp(V("claim")),
                "The proof gives more: write d_B = 4r and take the subspace spanned by |r⟩, |3r⟩ and (|0⟩ − |2r⟩)/√2. Its vectors are supported on the subgroup rℤ_{4r}, so X^a Z^b compresses to zero unless r divides a, and for a = ur it compresses to the ququart operator X^u Z^{b mod 4}, each residue of b having r lifts; hence the extrinsic term equals that of the ququart subspace span{|1⟩, |3⟩, (|0⟩ − |2⟩)/√2} for every r. The sixteen compressed 3 × 3 operators have fourth moments 1 (once), 1/5 (three times) and 1/15 (twelve times), computed from the permutation sum over the 24 elements of S₄, so the extrinsic term is (1 + 3/5 + 12/15)/4 = 3/5; the qutrit term is (1 + 8/10)/3 = 3/5. The gap vanishes, and 2^m = 4 · 2^{m−2} for m ≥ 2.",
                DescribeRole.Theorem, Repo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cepollaro-2025-power-of-two-zero-magic-gap"),
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
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App2(Formula head, Formula first, Formula second) =>
        Seq(head, Open, first, Comma, Sp, second, Close);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Leq2(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Plus2(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Times2(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Dot2(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Sub(Formula b, Formula i) => Seq(b, Underscore, Grp(i));
    private static Formula Frac2(Formula n, Formula d) => new Formula.Fraction(n, d);
    private static Formula Dagger(Formula x) => Seq(Parenthesized(x), Caret, Grp(Star));
    private static Formula ZModD() => Seq(Mathbb, Grp(V("Z")), Slash, V("d"), Mathbb, Grp(V("Z")));
}
