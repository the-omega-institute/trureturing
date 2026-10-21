using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.DiagonalUnitary;

internal sealed class SamantaMondalSenDiagonalPowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/samantamondalsen2025diagonalpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal phase gates have equal multipartite entangling and disentangling powers.",
        H("Conjugation symmetry of diagonal-unitary powers"),
        Blocks(
            Paragraph(Text("Amplitudes are functions from Fin N → Fin 2 to ℂ. The source maxima are represented by suprema over normalized-state subtypes. The overlap is dotProduct (star φ) ψ, with star acting coordinatewise. A bipartition has two nonempty parts. This includes formal N = 0 and N = 1 cases; the multipartite interpretation concerns N ≥ 2.")),
            Node("IsFullySeparable", "Fully separable pure states", FullyFormula(),
                "Page 2, Eq. (1): “E_N(U) = max_{|ψ⟩_FS^N ∈ S_N} G(U|ψ⟩_FS^N)”, where |ψ⟩_FS^N = ⊗_{i=1}^{N} |ψ_i⟩ is fully separable and S_N is the set of fully separable states. The amplitudes factor as a product of local amplitudes p i (x i), and the sum of squared moduli is one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsBiseparable", "Pure states separable across a bipartition", BiseparableFormula(),
                "Page 6, Appendix A.1: “generalized geometric measure (GGM) which is defined as G(|ψ⟩) = 1 − max_{|ϕ⟩∈S_nG} |⟨ϕ|ψ⟩|², where S_nG denotes the set of all non-genuinely multipartite entangled states.” For pure states, this is factorization across some A and its complement with both parts nonempty. The functions a and b take the restricted computational-basis labels; val denotes subtype inclusion.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("G", "Generalized geometric measure", GFormula(),
                "Page 6, Appendix A.1: “generalized geometric measure (GGM) which is defined as G(|ψ⟩) = 1 − max_{|ϕ⟩∈S_nG} |⟨ϕ|ψ⟩|², where S_nG denotes the set of all non-genuinely multipartite entangled states.” Here iSup is the real supremum over the displayed subtype and Complex.normSq is the squared complex modulus.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("E", "Multipartite entangling power", EFormula(),
                "Page 2, Eq. (1): “E_N(U) = max_{|ψ⟩_FS^N ∈ S_N} G(U|ψ⟩_FS^N)”. The input family consists of normalized fully separable amplitudes. Matrix.mulVec is the matrix action, and iSup represents the maximum as a supremum.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("D", "Multipartite disentangling power", DFormula(),
                "Page 2, Eq. (2): “D_N(U) ≡ E_N(U†) = max_{|ψ⟩_FS^N ∈ S_N} G(U†|ψ⟩_FS^N)”. The adjoint is Matrix.conjTranspose.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Appendix B.3 expectation", Equivalence(X("claim"), ClaimBody()),
                "Page 8, Appendix B.3: “It also indicates that such an equivalence may hold for arbitrary diagonal unitary operators acted on arbitrary number of qubits.” The variable N is the number of qubits; θ assigns a real phase to every computational-basis label. The diagonal entries are Complex.exp (θ x * Complex.I).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Equality for every diagonal phase gate", ClaimBody(),
                "Coordinatewise conjugation preserves normalization and both product factorizations. It conjugates the overlap, preserving its squared modulus, and therefore preserves G. For diagonal U it satisfies U.conjTranspose.mulVec (star ψ) = star (U.mulVec ψ). Conjugation bijects the fully separable inputs, so the two families of values have the same supremum. No hypothesis about attainment or local phases is required.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("samanta-mondal-sen-2025-diagonal-unitary-entangling-power-appendix-b-3"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("sms-diagonal-" + (name switch { "IsFullySeparable" => "fully", "IsBiseparable" => "biseparable", "G" => "ggm", "E" => "entangling", "D" => "disentangling", _ => name })), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(Named(name), args);
    private static Formula C() => Seq(Mathbb, Grp(X("C")));
    private static Formula R() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(new Formula.TypeArrow(a, b));
    private static Formula Index() => Arrow(Call("Fin", X("N")), Call("Fin", D(2)));
    private static Formula Vector() => Arrow(Index(), C());
    private static Formula Matrix() => Call("Matrix", Index(), Index(), C());
    private static Formula Typed(Formula v, Formula t) => Parenthesized(Seq(v, Colon, Sp, t));
    private static Formula All(Formula v, Formula t, Formula body) => Seq(Forall, Sp, Typed(v, t), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula v, Formula t, Formula body) => Seq(Exists, Sp, Typed(v, t), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOver(Formula v, Formula t, Formula body) => Parenthesized(Seq(Typed(v, t), Sp, Mapsto, Sp, body));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula SumOver(Formula v, Formula t, Formula body) => Seq(new Formula.Subscript(Sum, Seq(v, Colon, Sp, t)), Sp, Parenthesized(body));
    private static Formula ProdOver(Formula v, Formula t, Formula body) => Seq(new Formula.Subscript(Prod, Seq(v, Colon, Sp, t)), Sp, Parenthesized(body));
    private static Formula Subtype(Formula v, Formula t, Formula p) => Seq(OpenBrace, v, Colon, Sp, t, Sp, Slash, Slash, Sp, p, CloseBrace);
    private static Formula Val(Formula v) => Call("val", v);
    private static Formula NormSq(Formula v) => At(Qualified("Complex", "normSq"), v);
    private static Formula Normalized(Formula v) => Equal(SumOver(X("x"), Index(), NormSq(At(v, X("x")))), D(1));
    private static Formula Complement(Formula a) => new Formula.Power(a, X("c"));
    private static Formula InPart(Formula a) => Subtype(X("i"), Call("Fin", X("N")), Seq(X("i"), Sp, InMacro, Sp, a));
    private static Formula Restricted(Formula a) => LambdaOver(X("i"), InPart(a), At(X("x"), Val(X("i"))));
    private static Formula Supremum(Formula v, Formula t, Formula b) => Call("iSup", LambdaOver(v, t, b));

    private static Formula FullyFormula()
    {
        var product = ProdOver(X("i"), Call("Fin", X("N")), At(X("p"), X("i"), At(X("x"), X("i"))));
        var factor = All(X("x"), Index(), Equal(At(Psi, X("x")), product));
        var localType = Arrow(Call("Fin", X("N")), Arrow(Call("Fin", D(2)), C()));
        var body = And(Normalized(Psi), Some(X("p"), localType, factor));
        return All(X("N"), Nat(), All(Psi, Vector(), Equivalence(Call("IsFullySeparable", Psi), body)));
    }

    private static Formula BiseparableFormula()
    {
        var a = X("A");
        var factor = Equal(At(Psi, X("x")), new Formula.Binary(At(X("a"), Restricted(a)), FormulaBinaryOperator.Multiply, At(X("b"), Restricted(Complement(a)))));
        var factors = Some(X("a"), Arrow(Arrow(InPart(a), Call("Fin", D(2))), C()),
            Some(X("b"), Arrow(Arrow(InPart(Complement(a)), Call("Fin", D(2))), C()), All(X("x"), Index(), factor)));
        var parts = Some(a, Call("Finset", Call("Fin", X("N"))),
            And(At(Qualified("Finset", "Nonempty"), a), And(At(Qualified("Finset", "Nonempty"), Complement(a)), factors)));
        return All(X("N"), Nat(), All(Psi, Vector(), Equivalence(Call("IsBiseparable", Psi), And(Normalized(Psi), parts))));
    }

    private static Formula GFormula() => All(X("N"), Nat(), All(Psi, Vector(), Equal(Call("G", Psi),
        new Formula.Binary(D(1), FormulaBinaryOperator.Subtract,
            Supremum(Phi, Subtype(X("v"), Vector(), Call("IsBiseparable", X("v"))), NormSq(Call("dotProduct", Call("star", Val(Phi)), Psi)))))));

    private static Formula EFormula() => All(X("N"), Nat(), All(X("U"), Matrix(), Equal(Call("E", X("U")),
        Supremum(Psi, Subtype(X("v"), Vector(), Call("IsFullySeparable", X("v"))), Call("G", At(Qualified("Matrix", "mulVec"), X("U"), Val(Psi)))))));

    private static Formula DFormula() => All(X("N"), Nat(), All(X("U"), Matrix(), Equal(Call("D", X("U")), Call("E", At(Qualified("Matrix", "conjTranspose"), X("U"))))));

    private static Formula ClaimBody()
    {
        var phase = LambdaOver(X("x"), Index(), At(Qualified("Complex", "exp"),
            new Formula.Binary(Typed(At(Theta, X("x")), C()), FormulaBinaryOperator.Multiply, Qualified("Complex", "I"))));
        var u = At(Qualified("Matrix", "diagonal"), phase);
        return All(X("N"), Nat(), All(Theta, Arrow(Index(), R()), Equal(Call("E", u), Call("D", u))));
    }
}
