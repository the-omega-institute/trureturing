using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class HypereclecticNonShorteningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/HypereclecticNonShortening.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ahn2022eclectic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powers of the one-wall hypereclectic Hamiltonian have maximal rank between levels.",
        H("Non-shortening in the one-wall hypereclectic spin chain"),
        Blocks(
            Node("level", "The inversion level", LevelFormula(),
                "A Boolean word records the letters before the fixed wall 3: false denotes 1 and true denotes 2. Its level counts a 2 before a 1. This is S = Σ_{j=1}^{M−1} j n_j in Eq. (3.18), printed p. 10: each 1 in the j-th gap has exactly j twos to its left. All indices are zero-based. Subtraction of natural numbers is truncated at zero throughout these formulas.",
                DescribeRole.Definition),
            Node("sector", "The static sector", SectorFormula(),
                "The K = 1 static sector has L−1 Boolean letters and M−1 twos, with the wall fixed at the right. The function ones is the binary-coordinate count Σ_i ite(w(i) = true, 1, 0), reused from its existing definition.",
                DescribeRole.Definition),
            Node("W", "The elementary-state level space", WFormula(),
                "Section 3.2, printed p. 10: “As before we define W_S^{L,M} to be spanned by elementary states with this level S.” Here basisFun(ℚ, Fin(L−1) → Bool)(w) is the delta function at w. The span retains these elementary states as independently specified generators over ℚ.",
                DescribeRole.Definition),
            Node("H", "The adjacent-move Hamiltonian", HFormula(),
                "Section 3.2, printed p. 10: “The Hamiltonian acts on (3.16) as” Eq. (3.19), summing the states with n_{j−1} increased by one and n_j decreased by one. A term with n_j = 0 vanishes. Equivalently, each adjacent input 21 becomes 12 with coefficient one. The displayed formula is on output coordinates, so it tests 12 and reads the swapped input. The notation val(p) regards p : Fin((L−1)−1) as a site of Fin(L−1), and val(p)+1 as its adjacent successor; swap exchanges those sites. Composition acts on word coordinates, not on coefficient vectors. M labels the sector and does not affect this operator.",
                DescribeRole.Definition),
            Node("restrict", "The map between level spaces", RestrictFormula(),
                "The restriction is the linear map H^k from W_S to W_{S−k}; coe includes a level space into the ambient rational word space. Its range dimension is the rank of the matrix A^(k) in the elementary bases, and d_S is finrank(ℚ, W(L,M,S)).",
                DescribeRole.Definition),
            Node("claim", "The non-shortening claim (A.4)", ClaimFormula(true),
                "Appendix A, printed p. 24: “We claim that the rank of A^(k) is always maximal:” followed by “rank(A^(k)) = min(d_{S−k}, d_S).” (A.4). The introduction of arXiv:2207.02885v1, printed p. 1, states: “They rest on a compelling and extensively checked but unfortunately still unproven non-shortening conjecture.” The encoding quantifies over all 1 ≤ M ≤ L and all k ≤ S, over ℚ. Only the K = 1 static-sector claim is asserted here; the multi-wall, cyclic and eclectic-universality statements are separate questions.",
                DescribeRole.Definition),
            Node("result", "Maximal rank at every level", ClaimFormula(false),
                "The quadratic reverse-move coefficients and the diagonal inversion weight give an sl₂ triple. Induction on the remaining raising length proves that a lowering power has zero kernel on the upper half of the weights. The contragredient representation gives surjectivity on the lower half. The two cases establish the minimum of the source and target dimensions, including the empty and one-site bins. This proves the K = 1 claim (A.4).",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("hypereclectic-" + (name == "W" ? "w" : name == "H" ? "h" : name)), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula),
        role == DescribeRole.Theorem ? AssessedProvenance.FromRepo() : AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable),
            domain is Formula.TypeArrow ? Parenthesized(domain) : domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Apply(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rats() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word(Formula n) => new Formula.TypeArrow(Fin(n), Call("Bool"));
    private static Formula Vectors(Formula n) => new Formula.TypeArrow(Word(n), Rats());
    private static Formula Sum(Formula n, Formula i, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(i, InMacro, Fin(n))), Sp, body);
    private static Formula At(Formula w, Formula i) => Apply(w, i);

    private static Formula LevelFormula()
    {
        var n = F.Id("N"); var w = F.Id("w"); var i = F.Id("i"); var j = F.Id("j");
        var condition = Parenthesized(Seq(i, Sp, Lt, Sp, j, Sp, Land, Sp,
            At(w, i), Sp, Eq, Sp, Call("true"), Sp, Land, Sp, At(w, j), Sp, Eq, Sp, Call("false")));
        return Disp(All("N", Nats(), All("w", Word(n),
            Equal(Call("level", w), Sum(n, i, Sum(n, j, Call("ite", condition, D(1), D(0))))))));
    }

    private static Formula SectorFormula()
    {
        var l = F.Id("L"); var m = F.Id("M"); var w = F.Id("w");
        var set = new Formula.SetBuilder(w, w, Seq(Parenthesized(Word(Sub(l, D(1)))), Sp, Land, Sp,
            Equal(Call("ones", w), Sub(m, D(1)))));
        return Disp(All("L", Nats(), All("M", Nats(), Equal(Call("sector", l, m), set))));
    }

    private static Formula WFormula()
    {
        var l = F.Id("L"); var m = F.Id("M"); var s = F.Id("S"); var w = F.Id("w");
        var basis = Apply(Call("basisFun", Rats(), Word(Sub(l, D(1)))), w);
        var generators = new Formula.SetBuilder(basis, w, Seq(Call("sector", l, m), Sp, Land, Sp,
            Equal(Call("level", w), s)));
        return Disp(All("L", Nats(), All("M", Nats(), All("S", Nats(),
            Equal(Call("W", l, m, s), Call("span", Rats(), generators))))));
    }

    private static Formula HFormula()
    {
        var l = F.Id("L"); var m = F.Id("M"); var v = F.Id("v"); var w = F.Id("w"); var p = F.Id("p");
        var n = Sub(l, D(1)); var a = Call("val", p); var b = Add(a, D(1));
        var condition = Parenthesized(Seq(At(w, a), Sp, Eq, Sp, Call("false"), Sp, Land, Sp,
            At(w, b), Sp, Eq, Sp, Call("true")));
        var input = Parenthesized(Seq(w, Sp, Circ, Sp, Call("swap", a, b)));
        var body = Sum(Sub(n, D(1)), p, Call("ite", condition, Apply(v, input), D(0)));
        return Disp(All("L", Nats(), All("M", Nats(), All("v", Vectors(n), All("w", Word(n),
            Equal(At(Apply(Call("H", l, m), v), w), body))))));
    }

    private static Formula RestrictFormula()
    {
        var l = F.Id("L"); var m = F.Id("M"); var s = F.Id("S"); var k = F.Id("k"); var v = F.Id("v");
        var value = Call("coe", Apply(Call("restrict", l, m, s, k), v));
        var rhs = Apply(new Formula.Power(Parenthesized(Call("H", l, m)), k), Call("coe", v));
        return Disp(All("L", Nats(), All("M", Nats(), All("S", Nats(), All("k", Nats(),
            All("v", Call("W", l, m, s), Equal(value, rhs)))))));
    }

    private static Formula ClaimFormula(bool definition)
    {
        var l = F.Id("L"); var m = F.Id("M"); var s = F.Id("S"); var k = F.Id("k");
        var rank = Call("finrank", Rats(), Call("range", Call("restrict", l, m, s, k)));
        var minimum = Call("min", Call("finrank", Rats(), Call("W", l, m, s)),
            Call("finrank", Rats(), Call("W", l, m, Sub(s, k))));
        var body = All("L", Nats(), All("M", Nats(), Parenthesized(Seq(D(1), Sp, Leq, Sp, m,
            Sp, Rightarrow, Sp, m, Sp, Leq, Sp, l, Sp, Rightarrow, Sp,
            All("S", Nats(), All("k", Nats(), Parenthesized(Seq(k, Sp, Leq, Sp, s,
                Sp, Rightarrow, Sp, Equal(rank, minimum)))))))));
        return Disp(definition ? Equal(Call("claim"), Parenthesized(body)) : body);
    }
}
