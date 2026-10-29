using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class BalaA363411Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/BalaA363411.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/bala2023sqrtminusthree");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer quadratic products and Bala's valuation conjectures.", H("BalaA363411"), Blocks(
            Node("P", "The quadratic integer product", ProductBody(),
                "OEIS A363411, NAME (revision 18, no page): \"a(n) = the real part of Product_{k = 0..n} 1 + k*sqrt(-3).\" The product includes k=0 and k=n. The pair in Zsqrtd (-3) denotes 1+k sqrt(-3).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The real coordinate", All("n", N(), Eqn(Call("a", V("n")), App(Q("Zsqrtd", "re"), Call("P", V("n"))))),
                "OEIS A363411, NAME (revision 18, no page): \"a(n) = the real part of Product_{k = 0..n} 1 + k*sqrt(-3).\" Here a is the integer real coordinate.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b", "The imaginary coordinate", All("n", N(), Eqn(Call("b", V("n")), App(Q("Zsqrtd", "im"), Call("P", V("n"))))),
                "OEIS A363412, NAME (revision 19, no page): \"a(n) = 1/sqrt(3) * the imaginary part of Product_{k = 0..n} 1 + k*sqrt(-3).\" The source sequence is called b here; it is the sqrt(-3) coordinate.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The five-adic conjecture", Eqn(Named("claim"), ClaimBody()),
                "OEIS A363411, FORMULA (revision 18, no page): \"Conjecture: the 5-adic valuation v_5(a(n+2)) = A079998(n) (checked up to n = 5000).\" OEIS A079998, NAME: \"The characteristic function of the multiples of five.\" All indices are natural numbers, including zero. The conditional has natural values 1 and 0.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seq", "Coordinate recursion in a commutative ring", SequenceBody(),
                "For any commutative ring R in any universe, seq starts at (1,0). Multiplication by 1+(n+1)sqrt(-3) gives the two displayed successor coordinates.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("real_one", "Real coordinates are one modulo three", RealOneBody(),
                "For any finite family of integer coefficients, the real coordinate of the product is one modulo three. The ring homomorphism to ZMod 3 sends sqrt(-3) to zero and each factor to one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("seq_cast", "The recursion equals the product coordinates", CommRing(All("n", N(), Eqn(S(V("n")), Pair(Cast(Call("a", V("n")), V("R")), Cast(Call("b", V("n")), V("R")))))),
                "The integer coordinates map into every commutative ring. Induction compares the coordinate multiplication formula with the recursion.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("seq_shift", "A scalar block controls every later block", ShiftBody(),
                "If q vanishes in R and the qth pair is (c,0), shifting an index by q multiplies both coordinates by c. This holds for every natural index.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("seq_period", "A unit block gives a period", PeriodBody(),
                "A block equal to (1,0) yields period q when q vanishes in the coefficient ring. The scalar-block identity gives the equality at every index.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("seq_mod", "Reduction of a periodic sequence", ModBody(),
                "A periodic coordinate sequence has the same value at n and at its natural remainder modulo q. The remainder is the Lean natural-number modulo operation.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Bala five-adic valuation formula", ClaimBody(),
                "The product block at 25 is (7,0) modulo 25. Four successive blocks give period 100. Modulo 5 the real coordinate vanishes exactly at indices congruent to 2, while modulo 25 it never vanishes. These two facts give exactly one factor of 5 at n+2 when 5 divides n, and none otherwise.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bala3634-valuations"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("bala-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula All(string variable, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Addn(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subn(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Rightarrow, Sp, Parenthesized(right));
    private static Formula Dvd(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Proj(Formula value, byte index) => Seq(Parenthesized(value), Dot, D(index));
    private static Formula CommRing(Formula body) => All("R", Named("Type"), Seq(OpenBracket, Call("CommRing", V("R")), CloseBracket, Sp, body));
    private static Formula S(Formula index) => Call("seq", V("R"), index);
    private static Formula ClaimBody() => All("n", N(), Eqn(Call("padicValInt", D(5), Call("a", Addn(V("n"), D(2)))),
        Seq(Named("if"), Sp, Dvd(D(5), V("n")), Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0))));
    private static Formula ProductBody()
    {
        var k = V("k");
        var factor = Cast(Seq(Langle, D(1), Comma, Sp, Cast(k, Z()), Rangle), Call("Zsqrtd", new Formula.Negate(D(3))));
        var product = Seq(Prod, Underscore, Grp(k, Sp, InMacro, Sp, App(Q("Finset", "range"), Addn(V("n"), D(1)))), Sp, factor);
        return All("n", N(), Eqn(Call("P", V("n")), product));
    }
    private static Formula RealOneBody()
    {
        var i = V("i"); var u = V("u");
        var factor = Cast(Seq(Langle, D(1), Comma, Sp, App(V("f"), i), Rangle), Call("Zsqrtd", new Formula.Negate(D(3))));
        var product = Seq(Prod, Underscore, Grp(i, Sp, InMacro, Sp, V("s")), Sp, factor);
        var equality = Eqn(App(Q("Zsqrtd", "re"), product), Addn(D(1), Mul(D(3), u)));
        return All("I", Named("Type"), All("s", Call("Finset", V("I")), All("f", new Formula.TypeArrow(V("I"), Z()),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("u"), Z(), equality))));
    }
    private static Formula SequenceBody()
    {
        var n = V("n"); var z = S(n); var next = Addn(Cast(n, V("R")), D(1));
        return CommRing(And(Eqn(S(D(0)), Pair(D(1), D(0))), All("n", N(), Eqn(S(Addn(n, D(1))),
            Pair(Subn(Proj(z, 1), Mul(Mul(D(3), next), Proj(z, 2))), Addn(Proj(z, 2), Mul(next, Proj(z, 1))))))));
    }
    private static Formula ShiftBody()
    {
        var n = V("n"); var q = V("q"); var c = V("c"); var z = S(n);
        var conclusion = All("n", N(), Eqn(S(Addn(n, q)), Pair(Mul(c, Proj(z, 1)), Mul(c, Proj(z, 2)))));
        var hypotheses = Imp(Eqn(Cast(q, V("R")), D(0)), Imp(Eqn(S(q), Pair(c, D(0))), conclusion));
        return CommRing(All("q", N(), All("c", V("R"), hypotheses)));
    }
    private static Formula PeriodBody() => CommRing(All("q", N(), Imp(Eqn(Cast(V("q"), V("R")), D(0)),
        Imp(Eqn(S(V("q")), Pair(D(1), D(0))), App(Q("Function", "Periodic"), Call("seq", V("R")), V("q"))))));
    private static Formula ModBody() => CommRing(All("q", N(), Imp(App(Q("Function", "Periodic"), Call("seq", V("R")), V("q")),
        All("n", N(), Eqn(S(V("n")), S(new Formula.Modulo(V("n"), V("q"))))))));
}
