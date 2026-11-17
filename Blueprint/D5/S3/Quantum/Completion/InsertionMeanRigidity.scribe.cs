using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class InsertionMeanRigidityDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/InsertionMeanRigidity.";
    private static Formula V(string x) => F.Id(x);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula GridIndex => Seq(Open, Nat, Sp, Times, Sp, Nat, Close);
    private static Formula Arr(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Open, Forall, Sp, V(x), Colon, Sp, t, Comma, Sp, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, Rightarrow, Sp, b, Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(Open, a, Sp, Eq, Sp, b, Close);
    private static Formula Leq(Formula a, Formula b) => Seq(Open, a, Sp, Le, Sp, b, Close);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Sp, Cdot, Sp, b, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Both(params Formula[] xs)
    {
        var b = xs[^1];
        for (var j = xs.Length - 2; j >= 0; --j)
            b = Seq(Open, xs[j], Sp, Land, Sp, b, Close);
        return b;
    }
    private static Formula SumT(Formula body) =>
        Seq(Sum, Underscore, Grp(V("k"), Sp, InMacro, Sp, V("t")), Sp, body);
    private static Formula Cost(Formula x, Formula y) => Call("c", x, y);
    private static Formula P(byte j, Formula x) => Call("P", V("U"), D(j), x);
    private static Formula Orbit(byte j) => Call("p", V("U"), D(j));
    private static Formula G(Formula m, Formula n) => Call("g", Pair(m, n));
    private static Formula ScalarStatement()
    {
        var m = V("m"); var n = V("n"); var r = V("r"); var s = V("s");
        var k = V("k"); var vk = Call("v", k);
        var recurrence = All("m", Nat, All("n", Nat, Eqn(
            Add(Add(Mul(D(2), G(Add(m, D(1)), Add(n, D(1)))), G(Add(m, D(1)), n)),
                G(m, Add(n, D(1)))), Mul(D(4), G(m, n)))));
        var spectral = All("r", Real, All("s", Real,
            Imp(Leq(D(0), r), Imp(Leq(D(0), s),
            Imp(Eqn(Add(Add(r, s), Mul(Mul(D(2), r), s)), D(4)),
                Leq(D(0), SumT(Mul(Mul(Call("a", k),
                    Pow(r, Call("fst", vk))), Pow(s, Call("snd", vk))))))))));
        return All("I", V("Type"), All("t", Call("Finset", V("I")),
            All("a", Arr(V("I"), Real), All("v", Arr(V("I"), GridIndex),
            All("g", Arr(GridIndex, Real),
            Imp(All("q", GridIndex, Leq(D(0), Call("g", V("q")))),
            Imp(recurrence, Imp(spectral,
                Leq(D(0), SumT(Mul(Call("a", k), Call("g", vk))))))))))));
    }
    private static Formula KernelStatement()
    {
        var m = V("M"); var x = V("x"); var y = V("y"); var c = V("c");
        var sc = Call("S", V("U"), c); var tc = Call("T", V("U"), c);
        var stc = Call("S", V("U"), tc);
        var result = Both(
            All("m", Nat, All("n", Nat, All("x", m, All("y", m,
                Eqn(Call("F", V("U"), c, V("m"), V("n"), x, y), Cost(x, y)))))),
            Eqn(sc, c), Eqn(tc, c), Eqn(stc, c), Eqn(Seq(Open, c, Minus, stc, Close), D(0)));
        return All("M", V("Type"), Seq(OpenBracket, Call("MulOneClass", m), CloseBracket, Sp,
            All("U", Arr(m, m), All("c", Arr(m, Arr(m, Real)),
            Imp(Call("RawCost", V("U"), c),
            Imp(All("x", m, All("y", m, Eqn(Cost(x, y), Cost(y, x)))),
            Imp(All("x", m, All("y", m, Eqn(Cost(P(3, x), y), Cost(x, y)))),
            Imp(All("x", m, All("y", m, Eqn(Cost(x, P(3, y)), Cost(x, y)))),
            Imp(Eqn(Cost(D(1), Orbit(1)), D(0)),
            Imp(Eqn(Cost(D(1), Orbit(2)), D(0)), result))))))))));
    }
    private static DocumentBlock Entry(string id, string name, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Gid + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scalar recurrence cone forces rigidity of every original insertion mean.",
        H("Insertion mean rigidity"), Blocks(
            Paragraph(Text("Let Grid be the real functions on all natural pairs. Recurrent means 2g(m+1,n+1)+g(m+1,n)+g(m,n+1)=4g(m,n) for every m,n. Indices include zero, and the grid need not have positive mass at (0,0). For an arbitrary finite index set t, a gives real coefficients and v gives the two natural exponents. Repeated exponents and empty sums are allowed.")),
            Entry("finite-polynomial-positive", "finite_polynomial_positive", "Finite polynomial positivity", ScalarStatement(),
                "The spectral set is K={(r,s): r>=0, s>=0, r+s+2rs=4}. It includes the two endpoints (0,4) and (4,0). Every finite real polynomial nonnegative on K has nonnegative evaluation on every nonnegative recurrent grid, replacing r^m*s^n by g(m,n). No measure representation is assumed."),
            Paragraph(Text("Nonnegativity and recurrence give both one-step bounds by four times the current entry, hence g(m,n)<=4^(m+n)g(0,0). Zero initial mass therefore forces the entire grid to vanish. At positive mass divide by g(0,0). The normalized grids form a nonempty closed subset of the product of the intervals [0,4^(m+n)], and are compact. A continuous finite linear functional attains its minimum at an extreme point, using the exposed minimizing face and the existing extreme-point existence theorem.")),
            Paragraph(Text("If a nonnegative recurrent h is bounded above by 4g for an extreme normalized g, the complementary grid 4g-h is also nonnegative and recurrent. At h(0,0)=0 or 4 the zero-mass argument applies. Otherwise normalize h and its complement to express g as a strict convex combination; extremality forces h(q)=h(0,0)g(q). Apply this to each coordinate shift. Both shifts are scalar multiples of g, so g(m,n)=r^m*s^n, with r,s>=0 and r+s+2rs=4. Evaluating the polynomial at this minimizing extreme grid proves the assertion and scaling returns the original mass.")),
            Paragraph(Text("For the original kernel let M have only a multiplication and a two-sided unit. U is any self-map. Kernel means M -> M -> R. Put p(U,j)=U^j(1), P(U,j,x)=x*p(U,j), S(U,g)(x,y)=(g(P(U,1,x),y)+g(P(U,2,x),y))/2, T(U,g)(x,y)=(g(x,P(U,1,y))+g(x,P(U,2,y)))/2, and F(U,c,m,n)=S(U)^m(T(U)^n(c)). Function differences and zero kernels below are pointwise.")),
            Paragraph(Text("RawCost requires c(a,b)>=0, c(a,a)=0, and c(a*u,b*v)+c(a*U(u),b*U(v))+c(a*U(U(u)),b*U(U(v)))=3c(a,b)+3c(u,v) for every a,b,u,v. The two return assumptions below are cost equalities at P(U,3), for every pair of endpoints. They are not identities between elements of M.")),
            Entry("full-original-insertion-mean-rigidity", "full_original_insertion_mean_rigidity", "All original insertion means are fixed", KernelStatement(),
                "This is the full original cost statement: all natural m,n, both universal P3 cost returns, symmetry and both zero unit-orbit costs are retained. There is no associativity, commutativity, U(1)=1, periodicity of U, multiplicativity, surjectivity, triangle inequality, Hilbert realization, topology on M, or assumed growth bound."),
            Paragraph(Text("The original single and unit_compare inequalities give c(x,y)<=3(q(x)+q(y)) and q(s*t)<=3(q(s)+q(t)), where q(x)=c(x,1). A zero q stays zero under each right insertion. Thus all T^n(c)(x,1) are bounded by 3q(x). Three original balance instances, symmetry and the P3 cost returns yield (2ST+S+T)c=4c. Separate endpoint averaging preserves this recurrence and nonnegativity; S and T commute without changing the order of operations at either endpoint.")),
            Paragraph(Text("The scalar theorem applied to a three-term square polynomial gives axis quadratic positivity. The existing quadratic-discriminant inequality gives log-convexity of both axes. A nonnegative bounded log-convex sequence cannot increase at its first step: otherwise the original positive_all and convex_ratio suppliers imply a geometric lower bound of ratio greater than one, contradicting the bound by power divergence. Applied at (x,1), this proves the two-anchor mean inequality.")),
            Paragraph(Text("The original sync_iter supplier and the right P3 return identify c(x,p1)=q(U^2(x)), c(x,p2)=q(U(x)) and q(U^3(x))=q(x). The three cyclic inequalities force these q values to agree. Hence T(c)(x,1)=q(x), and the recurrence gives (q(P1(x))+q(P2(x)))/2=q(x). Induction through the actual positive means now gives the uniform bound F(U,c,m,n)(x,y)<=3(q(x)+q(y)) at every finite m,n. This bound is derived from the raw assumptions, not supplied as a hypothesis.")),
            Paragraph(Text("Apply the bounded log-convex argument to every shifted axis. Both successors are at most the current entry. The recurrence then forces both successor deficits to vanish. Two inductions give every F(U,c,m,n)(x,y)=c(x,y), including zero indices. Function extensionality yields S(c)=T(c)=ST(c)=c and the zero difference kernel.")),
            Paragraph(Text("The statement source is C133 Unanchored Marker Bounded Orbits Continuation W, Sections 42 and 43.1. The proof reuses the original RawUnanchoredReplication suppliers and the original KarpZhangCatalanPower log-convexity suppliers, together with Mathlib compactness, exposed-face, discriminant and power-divergence results. These are algebraic and scalar analytic conclusions under the displayed assumptions. No physical realization or literature priority is asserted; Sections 43.2 and 43.3 require additional results.")))));
}
