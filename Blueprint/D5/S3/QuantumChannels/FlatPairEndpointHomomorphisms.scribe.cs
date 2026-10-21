using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class FlatPairEndpointHomomorphismsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/verhagen2025flatpairendpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint and negative tropical homomorphisms fail monotonicity on everywhere overlapping flat pairs.",
        H("Flat-pair endpoint homomorphisms"),
        Blocks(
            Node("flat-pair", "Finite block vectors", PairFormula(),
                "Section 4.1, Eq. (31), p. 9: “A = ⊕ᵢ |αᵢ⟩⟨αᵢ|, B = ⊕ᵢ |βᵢ⟩⟨βᵢ|”. The vectors may be zero. FlatPair stores the number of blocks, their dimensions and their two complex vectors.",
                "FlatPair", AssessedProvenance.FromLiterature(Source)),
            Node("matrix-a", "First block matrix", BlockMatrixFormula("A", Alpha),
                "Eq. (31), p. 9: “A = ⊕ᵢ |αᵢ⟩⟨αᵢ|, B = ⊕ᵢ |βᵢ⟩⟨βᵢ|”. The first matrix is the block diagonal sum of the unnormalized rank-one matrices.",
                "A", AssessedProvenance.FromLiterature(Source)),
            Node("matrix-b", "Second block matrix", BlockMatrixFormula("B", Beta),
                "Eq. (31), p. 9: “A = ⊕ᵢ |αᵢ⟩⟨αᵢ|, B = ⊕ᵢ |βᵢ⟩⟨βᵢ|”. The second matrix uses the second vector in each block.",
                "B", AssessedProvenance.FromLiterature(Source)),
            Node("overlap-domain", "Everywhere overlapping pairs", OverlapDomainFormula(),
                "Eqs. (33)–(34), p. 9: “Also, we define the set of everywhere overlapping pairs Vₑ.ₒ. ⊊ Vₘ.ᵣ. to be those (A, B) ∈ Vₘ.ᵣ. such that, for any i ∈ [n], we have either ⟨αᵢ|βᵢ⟩ ≠ 0 or |αᵢ⟩ = 0 = |βᵢ⟩.” Every block has nonzero cross dot product or both vectors vanish.",
                "IsEverywhereOverlapping", AssessedProvenance.FromLiterature(Source)),
            Node("weight-p", "First block weight", WeightFormula("p", Alpha),
                "Eq. (37), p. 10: “the vector |αᵢ⟩ is normalized when pᵢ > 0 and equal to the zero vector when pᵢ = 0, and similarly for the |βᵢ⟩, qᵢ.” In the unnormalized representation the first weight is the real part of the self dot product.",
                "p", AssessedProvenance.FromLiterature(Source)),
            Node("weight-q", "Second block weight", WeightFormula("q", Beta),
                "Eq. (37), p. 10: “the vector |αᵢ⟩ is normalized when pᵢ > 0 and equal to the zero vector when pᵢ = 0, and similarly for the |βᵢ⟩, qᵢ.” The second weight is the real part of the second self dot product.",
                "q", AssessedProvenance.FromLiterature(Source)),
            Node("normalized-overlap", "Squared normalized overlap", SquaredOverlapFormula(),
                "Eq. (37) normalizes the vectors in every nonzero block. Their squared overlap is the squared modulus of the cross dot product divided by the two weights. Division is real division.",
                "overlapSq", AssessedProvenance.FromLiterature(Source)),
            Node("majorizes", "One channel acts on both matrices", MajorizesFormula(),
                "Section 4.1, pp. 9–10: “(A, B) ≽ (C, D) if and only if there exists a quantum channel 𝒞 … such that 𝒞(A) = C and 𝒞(B) = D”. Majorizes x y uses a completely positive trace-preserving channel between the two sigma index types.",
                "Majorizes", AssessedProvenance.FromLiterature(Source)),
            Node("phi", "Scalar homomorphisms", PhiFormula(),
                "Eq. (84), p. 16: “Φ_{α,z}(A, B) := Σᵢ (pᵢ)^α (qᵢ)^{1−α} |⟨αᵢ|βᵢ⟩|^{2z}”. The formula uses the normalized form of Eq. (37). Blocks with zero cross dot product contribute zero.",
                "Phi", AssessedProvenance.FromLiterature(Source)),
            Node("phi-t", "Tropical homomorphisms", PhiTFormula(),
                "Eq. (85), p. 17: “Φ^𝕋_z(A, B) := max_{i=1,…,n} |⟨αᵢ|βᵢ⟩|^{2z}”. The formula takes the maximum of the real z-th powers of the squared normalized overlaps. The finite maximum is initialized at zero; zero blocks contribute zero.",
                "PhiT", AssessedProvenance.FromLiterature(Source)),
            Node("monotone", "Ordinary target order", MonotoneFormula(false),
                "Section 3.1, p. 7: “x ≼ y ⇒ Φ(x) ≼ Φ(y)”. With Majorizes x y, this target order requires the value at y to be at most the value at x.",
                "IsMonotone", AssessedProvenance.FromLiterature(Source)),
            Node("monotone-op", "Opposite target order", MonotoneFormula(true),
                "Section 3.1, p. 7: “x ≼ y ⇒ Φ(x) ≼ Φ(y)”. For the opposite real order the numerical inequality is reversed.",
                "IsMonotoneOp", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Endpoint and tropical nonmonotonicity", Disp(Equal(N("claim"), Parenthesized(ClaimBody()))),
                "Remark 15, p. 21: “We suspect that these additional homomorphisms are in fact not monotone either, since they correspond to parameters α, z for which the α-z relative entropy is known not to satisfy DPI for general pairs of quantum states (with some conditions on the support).” The endpoint parameters are a = 0 or a = 1 and z < 1, excluding the degenerate z = 0 trace maps; both real target orders are tested. The tropical statement uses z < 0 and the ordinary order.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Node("result", "The endpoint suspicion holds", Disp(ClaimBody()),
                "An orthogonally flagged two-outcome filter takes one squared overlap 1/2 to squared overlaps 1/4 and 3/4 with equal second weights. Strict concavity for 0 < z < 1 and strict convexity for z < 0 give opposite strict inequalities. Erasure gives the other failed order. Swapping the two matrices transfers a = 0 to a = 1. For negative z the tropical maximum increases from (1/2)^z to (1/4)^z. The tropical opposite order and monotone derivations remain separate questions.",
                "result", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("verhagen-tomamichel-haapasalo-2025-flat-pair-endpoint-homomorphisms-remark-15"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("flat-pair-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(N(owner), Dot, N(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula FP => N("FlatPair");
    private static Formula Fin(Formula n) => App(N("Fin"), n);
    private static Formula Field(Formula x, Formula f, params Formula[] args) =>
        args.Length == 0 ? Seq(x, Dot, f) : App(Seq(x, Dot, f), args);
    private static Formula Lam(Formula x, Formula body) => Seq(LambdaLower, Sp, x, Sp, Mapsto, Sp, body);
    private static Formula SigmaIndex(Formula x) => Seq(Sigma, Sp, V("i"), Colon, Sp,
        Fin(Field(x, V("n"))), Comma, Sp, Fin(Field(x, V("d"), V("i"))));
    private static Formula Vec(Formula x, Formula f, Formula i) => Field(x, f, i);
    private static Formula Inner(Formula x, Formula f, Formula g, Formula i) =>
        App(N("dotProduct"), App(N("star"), Vec(x, f, i)), Vec(x, g, i));
    private static Formula Power(Formula x, Formula z) => new Formula.Power(Parenthesized(x), z);
    private static Formula PairFormula() => Disp(Seq(N("FlatPair"), Sp, Colon, Sp, N("Type"), Sp,
        Eq, Sp, OpenBrace, Sp, V("n"), Colon, Sp, Nat, Semi, Sp,
        V("d"), Colon, Sp, Arrow(Fin(V("n")), Nat), Semi, Sp,
        Alpha, Colon, Sp, All(V("i"), Fin(V("n")), Arrow(Fin(App(V("d"), V("i"))), C)), Semi, Sp,
        Beta, Colon, Sp, All(V("i"), Fin(V("n")), Arrow(Fin(App(V("d"), V("i"))), C)), Sp, CloseBrace));
    private static Formula BlockMatrixFormula(string name, Formula vector)
    {
        var x = V("x"); var i = V("i");
        return Disp(All(x, FP, Equal(Field(x, V(name)),
            App(Seq(Qualified("Matrix", "blockDiagonal"), Apos),
                Lam(i, App(Qualified("Matrix", "vecMulVec"), Vec(x, vector, i), App(N("star"), Vec(x, vector, i))))))));
    }
    private static Formula OverlapDomainFormula()
    {
        var x = V("x"); var i = V("i");
        return Disp(All(x, FP, Equal(Field(x, V("IsEverywhereOverlapping")), Parenthesized(
            All(i, Fin(Field(x, V("n"))), Or(NotEqual(Inner(x, Alpha, Beta, i), D(0)),
                And(Equal(Vec(x, Alpha, i), D(0)), Equal(Vec(x, Beta, i), D(0)))))))));
    }
    private static Formula WeightFormula(string name, Formula vector)
    {
        var x = V("x"); var i = V("i");
        return Disp(All(x, FP, All(i, Fin(Field(x, V("n"))),
            Equal(Field(x, V(name), i), Seq(Parenthesized(Inner(x, vector, vector, i)), Dot, N("re"))))));
    }
    private static Formula SquaredOverlapFormula()
    {
        var x = V("x"); var i = V("i");
        return Disp(All(x, FP, All(i, Fin(Field(x, V("n"))), Equal(Field(x, V("overlapSq"), i),
            new Formula.Fraction(App(Qualified("Complex", "normSq"), Inner(x, Alpha, Beta, i)),
                Multiply(Field(x, V("p"), i), Field(x, V("q"), i)))))));
    }
    private static Formula MajorizesFormula()
    {
        var x = V("x"); var y = V("y"); var channel = V("C");
        Formula Image(Formula u, string matrix) => Field(channel, V("toCompletelyPositiveMap"),
            App(Qualified("CStarMatrix", "ofMatrix"), Field(u, V(matrix))));
        Formula Target(string matrix) => App(Qualified("CStarMatrix", "ofMatrix"), Field(y, V(matrix)));
        return Disp(All(x, FP, All(y, FP, Equal(App(N("Majorizes"), x, y), Parenthesized(
            Some(channel, App(N("QuantumChannel"), Parenthesized(SigmaIndex(x)), Parenthesized(SigmaIndex(y))),
                And(Equal(Image(x, "A"), Target("A")), Equal(Image(x, "B"), Target("B")))))))));
    }
    private static Formula IfOverlap(Formula x, Formula i, Formula body) => Seq(N("if"), Sp,
        Equal(Inner(x, Alpha, Beta, i), D(0)), Sp, N("then"), Sp, D(0), Sp, N("else"), Sp, body);
    private static Formula PhiFormula()
    {
        var a = V("a"); var z = V("z"); var x = V("x"); var i = V("i");
        var body = IfOverlap(x, i, Multiply(Multiply(Power(Field(x, V("p"), i), a),
            Power(Field(x, V("q"), i), Subtract(D(1), a))), Power(Field(x, V("overlapSq"), i), z)));
        return Disp(All(a, R, All(z, R, All(x, FP, Equal(App(N("Phi"), a, z, x),
            Seq(Sum, Underscore, Grp(i, Colon, Sp, Fin(Field(x, V("n")))), Sp, Parenthesized(body)))))));
    }
    private static Formula PhiTFormula()
    {
        var z = V("z"); var x = V("x"); var i = V("i");
        return Disp(All(z, R, All(x, FP, Equal(App(N("PhiT"), z, x),
            App(Qualified("Finset", "fold"), N("max"), D(0),
                Lam(i, IfOverlap(x, i, Power(Field(x, V("overlapSq"), i), z))),
                Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Sp,
                    App(N("Finset"), Fin(Field(x, V("n")))))))))));
    }
    private static Formula MonotoneFormula(bool opposite)
    {
        var f = V("f"); var x = V("x"); var y = V("y");
        return Disp(All(f, Arrow(FP, R), Equal(App(N(opposite ? "IsMonotoneOp" : "IsMonotone"), f),
            Parenthesized(All(x, FP, All(y, FP,
                Imp(Field(x, V("IsEverywhereOverlapping")), Imp(Field(y, V("IsEverywhereOverlapping")),
                    Imp(App(N("Majorizes"), x, y), new Formula.Relation(App(f, opposite ? x : y),
                        FormulaRelationOperator.LessThanOrEqual, App(f, opposite ? y : x)))))))))));
    }
    private static Formula ClaimBody()
    {
        var a = V("a"); var z = V("z");
        var bothOrders = And(Not(App(N("IsMonotone"), App(N("Phi"), a, z))),
            Not(App(N("IsMonotoneOp"), App(N("Phi"), a, z))));
        var endpoint = All(a, R, Imp(Or(Equal(a, D(0)), Equal(a, D(1))),
            All(z, R, Imp(new Formula.Relation(z, FormulaRelationOperator.LessThan, D(1)),
                Imp(NotEqual(z, D(0)), bothOrders)))));
        var tropical = All(z, R, Imp(new Formula.Relation(z, FormulaRelationOperator.LessThan, D(0)),
            Not(App(N("IsMonotone"), App(N("PhiT"), z)))));
        return And(endpoint, tropical);
    }
}
