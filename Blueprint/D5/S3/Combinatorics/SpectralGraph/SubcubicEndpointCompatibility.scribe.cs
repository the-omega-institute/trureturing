using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class SubcubicEndpointCompatibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility.";
    public DocumentDefinition Create()
    {
        Formula v = V("V"), g = V("G"), m = V("M"), o = V("o"), a = V("a"), c = V("c");
        Formula n = V("n"), j = V("J"), d = V("d"), r = V("r"), e = V("e"), k = V("k");
        Formula order = Add(n, D(1)), t = Call("uniformMatrix", g, a, c);
        Formula matches = Carrier(All("M", Mat(v), All("o", v, All("n", Nat(),
            All("J", Mat(Fin(order)), All("d", Nat(),
                Iff(Call("MatchesThrough", m, o, j, d), Moments(m, o, j, d))))))));
        Formula compatible = Carrier(All("M", Mat(v), All("o", v,
            Iff(Call("Compatible", m, o), Ex("n", Nat(), Ex("J", Mat(Fin(order)),
                And(Call("PositiveJacobi", j), All("k", Nat(),
                    Eqn(App(Pow(m, k), o, o), App(Pow(j, k), D(0), D(0)))))))))));
        Formula path = All("n", Nat(), All("a", Rat(), All("c", Rat(),
            Eqn(Call("pathMatrix", n, a, c), Call("uniformMatrix", Call("pathGraph", n), a, c)))));
        Formula h = Norm(t, o, a, c, r), endpoint = Call("EndpointPath", g, o);
        Formula initial = All("j", Nat(), Imp(Lt(V("j"), r), Eqn(Norm(t, o, a, c, V("j")), D(1))));
        Formula excluded = Imp(Neg(endpoint), All("n", Nat(), All("J", Mat(Fin(order)),
            Imp(Call("PositiveJacobi", j), Neg(Call("MatchesThrough", t, o, j, Mul(D(2), r)))))));
        Formula unique = All("n", Nat(), All("J", Mat(Fin(order)),
            Imp(Call("PositiveJacobi", j), Imp(Call("MatchesThrough", t, o, j, Mul(D(2), r)),
                And(Eqn(order, r), Eqn(j, Call("pathMatrix", order, a, c)))))));
        Formula permutation = Ex("e", Call("GraphIso", g, Call("pathGraph", r)), Conj(
            Eqn(App(e, o), D(0)),
            Eqn(Call("reindex", t, e, e), Call("pathMatrix", r, a, c)),
            Eqn(Call("transport", e, Call("unit", o)), Call("unit", D(0))),
            All("f", Fn(v, Rat()), Eqn(Call("mulVec", Call("pathMatrix", r, a, c),
                Call("transport", e, V("f"))), Call("transport", e, Call("mulVec", t, V("f"))))),
            All("k", Nat(), Eqn(App(Pow(t, k), o, o),
                App(Pow(Call("pathMatrix", r, a, c), k), D(0), D(0))))));
        Formula positive = Imp(endpoint, Conj(Eqn(r, Call("card", v)), permutation, unique));
        Formula result = Ex("r", Nat(), Conj(Lt(D(0), r), Le(r, Call("card", v)), initial,
            Ne(h, D(1)), Iff(Eqn(h, D(0)), endpoint),
            Or(Eqn(h, D(0)), Or(Eqn(h, D(2)), Eqn(h, D(3)))),
            Iff(Call("Compatible", t, o), endpoint), excluded, positive));
        Formula complete = Graph(Imp(Call("IsTree", g), Imp(
            All("x", v, Le(Call("degree", g, V("x")), D(3))), All("o", v,
                All("a", Rat(), All("c", Rat(), Imp(Lt(D(0), c), result)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Complete rational symmetric endpoint compatibility for an actual finite rooted subcubic tree.",
            H("Rational symmetric endpoint compatibility"), Blocks(
                Paragraph(Text("Fix an actual nonempty finite connected simple tree G, an actual selected vertex o, a rational shift a and a strictly positive rational link c. Its matrix is T = a Id + c Adj(G), with unit zero-diagonal adjacency in the original coordinates. Write h_j for chainNorm(T,o,a,c,j), using the fixed Chebyshev recurrence described in TreeEndpointMomentCertificates. The shift can be zero or negative; T need not be positive, contractive or cyclic.")),
                Node("prefix", "Exact finite moment agreement", "MatchesThrough", matches,
                    "This compares moments at the actual port with moments at coordinate zero. The upper index is inclusive. Every nonempty finite competitor order occurs uniquely as n+1; there is no hidden size bound.", DescribeRole.Definition),
                Node("compatible", "All moments and every order", "Compatible", compatible,
                    "A competitor has rational coefficients, symmetry, tridiagonality and strictly positive existing adjacent links. It must match every natural moment, including the zeroth moment. The link list is empty in order one.", DescribeRole.Definition),
                Node("pathmatrix", "The actual uniform path matrix", "pathMatrix", path,
                    "The argument n is the order itself. In contrast, existential competitor parameters use n+1 so that no empty competitor is admitted.", DescribeRole.Definition),
                Node("complete", "The complete endpoint criterion and both finite certificates", "complete78_3", complete,
                    "There is a first positive r with h_r different from one: all earlier nonnegative indices have norm one, and 1 <= r <= the actual number of vertices. Its value is zero, two or three, and zero is equivalent to G being a path with o at an endpoint. EndpointPath means a genuine rooted graph isomorphism to a nonempty path, so the singleton is included and a nontrivial path's interior port is excluded. Compatibility with a rational symmetric positive-link endpoint matrix is equivalent to precisely that same actual geometric condition. If it fails, moments zero through 2r exclude every such competitor of every finite order. If it holds, r equals the actual order, and the same finite prefix forces every matching competitor to have that order, every diagonal a, and every link c: its entire matrix is pathMatrix. The theorem also constructs an actual graph isomorphism e sending o to zero. In the display, transport(e,f) means f composed with the inverse coordinate equivalence. It sends the actual selected unit vector to the first path unit vector and intertwines T with the path matrix on every vector; reindexing both matrix coordinates gives exactly that path matrix. Consequently every moment agrees, not merely the finite certificate.", DescribeRole.Theorem),
                Paragraph(Text("The proof earns a maximal simple saturated rooted stem in the actual tree. Its fixed recurrence vectors are distinct actual unit coordinates until its terminal forward boundary, whose size is zero, two or three. Generic positive Jacobi rigidity forces any matching competitor to expose the same initial coordinates and coefficients. A shorter competitor contradicts a required unit norm; an exact terminating competitor has next norm zero; a larger competitor has next norm equal to the square of its next link divided by c. For a nonzero boundary, the exact rational-square theorem and primality of two and three exclude a rational competitor. For a zero boundary, connectedness exhausts the actual graph and a coordinate isomorphism produces the positive solution. Positive next links prohibit a larger order, and symmetry plus the band condition identify every matrix entry.")),
                Paragraph(Text("This is an algebraic classification. It supplies no installed scalar service, rights, preparation, reset implementation, paid backing or physical cost bound. The distinct installed-service consumer and its execution or horizon conditions are outside this theorem. No geometry oracle, other port or external advice is assumed.")))));
    }
    private static DocumentBlock Node(string id, string title, string name, Formula f, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("subcubic-endpoint-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? C(s) : App(C(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Neg(Formula a) => new Formula.Not(a);
    private static Formula Conj(params Formula[] a) => a.Length == 1 ? a[0] : And(a[0], Conj(a[1..]));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Norm(Formula t, Formula o, Formula a, Formula c, Formula j) => Call("chainNorm", t, o, a, c, j);
    private static Formula Fin(Formula p) => Call("Fin", p);
    private static Formula Mat(Formula v) => Call("Matrix", v, v, Rat());
    private static Formula Type() => C("Type");
    private static Formula Nat() => C("Nat");
    private static Formula Rat() => C("Rat");
    private static Formula Instance(string name, Formula arg, Formula body) => Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, body);
    private static Formula Carrier(Formula b) => All("V", Type(), Instance("Fintype", V("V"), Instance("DecidableEq", V("V"), b)));
    private static Formula Graph(Formula b) => Carrier(All("G", Call("SimpleGraph", V("V")), Instance("DecidableRel", Call("Adj", V("G")), b)));
    private static Formula Moments(Formula m, Formula o, Formula j, Formula d) => All("k", Nat(), Imp(Le(V("k"), d), Eqn(App(Pow(m, V("k")), o, o), App(Pow(j, V("k")), D(0), D(0)))));
}
