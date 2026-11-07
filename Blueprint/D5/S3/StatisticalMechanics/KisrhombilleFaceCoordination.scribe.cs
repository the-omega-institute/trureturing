using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class KisrhombilleFaceCoordinationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/sloane2018a298038");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coordination sequence of the simplex-inclusion graph of the triangular lattice, "
            + "centered at an upward face, satisfies Barker's formal generating-function identity.",
        H("Face-rooted kisrhombille coordination"),
        Blocks(
            Paragraph(Text("Coordinates i and j are integers. Products associate to the right: "
                + "a simplex is (t,(i,j)). The six values of t in Fin 6, numbered zero through five, "
                + "denote a vertex V, horizontal edge H, vertical edge B, diagonal edge D, upward "
                + "face U and downward face W, respectively. Integer pairs are lattice vertices. "
                + "The triangular lattice has difference vectors ±(1,0), ±(0,1), ±(1,−1). "
                + "Subset means inclusion of the finite vertex sets, including equality. "
                + "The graph also requires distinct simplex labels.")),
            Definition("simplex", "Simplex", "The nonempty simplices", Eq(V("Simplex"),
                Product(Call("Fin", D(6)), Product(Integers(), Integers()))),
                "Every edge and face occurs once in these coordinates. An edge has two vertices "
                    + "and a face has three. The support equations specify the literal simplices."),
            Definition("support", "support", "The six finite supports", SupportFormula(),
                "Each displayed brace is a Finset of integer pairs. U(i,j) has vertices "
                    + "(i,j), (i+1,j), (i,j+1); W(i,j) has vertices (i+1,j), (i,j+1), "
                    + "(i+1,j+1). All six kinds of support are nonempty."),
            Definition("graph", "graph", "The simplex-inclusion graph", GraphFormula(),
                "Any two distinct comparable simplices are adjacent. In particular, a vertex "
                    + "and a containing face are adjacent even without specifying an intermediate "
                    + "edge. This is the vertex-edge graph of the barycentric subdivision. "
                    + "An upward face is adjacent to its three vertices and its three edges."),
            Definition("root", "root", "The specified upward face",
                Eq(V("root"), Pair(D(4), Pair(D(0), D(0)))),
                "The root is U(0,0), a hexavalent node."),
            Definition("distance", "distance", "Minimum walk length", All("s", V("Simplex"),
                Eq(Call("distance", V("s")),
                    App(Q("SimpleGraph", "dist"), V("graph"), V("root"), V("s")))),
                "Distance is SimpleGraph.dist, the genuine shortest-walk distance. "
                    + "Paths from the root to every simplex are constructed in the proof, "
                    + "so no disconnected-distance convention contributes to a shell."),
            Definition("count", "a", "The literal coordination sequence", All("n", Naturals(),
                Eq(Call("a", V("n")), App(Q("Set", "ncard"),
                    SetOf("s", V("Simplex"), Eq(Call("distance", V("s")), V("n")))))),
                "Set.ncard is the natural cardinality of the displayed set. Every shell is "
                    + "proved finite by containment in a finite coordinate box. Radius zero is "
                    + "included and contains exactly the root."),
            Definition("polygon", "polygon", "Translated cut rectangles", PolygonFormula(),
                "The natural rectangle 0≤u≤A, 0≤v≤B is cut by deleting u+v<l and "
                    + "the reflected triangle obtained from natural pairs with sum less than r. "
                    + "Finset.range(n) contains the naturals less than n; "
                    + "Finset.HasAntidiagonal.antidiagonal(n) contains natural pairs summing to n. "
                    + "Finset.biUnion forms their finite union, Finset.product forms the rectangle, "
                    + "and Finset.sdiff removes the union of both corners. Subtraction in the "
                    + "reflection is truncated natural subtraction. The outer image map "
                    + "casts each natural coordinate to an integer and translates by (i0,j0). "
                    + "The projections p.1 and p.2 are the first and second components."),
            SharedTheorem("polygon-mem", "polygon_mem", "Six inequalities for polygon membership",
                PolygonMembershipFormula(), "Each corner fits in the rectangle when its size is "
                    + "at most A+1 and B+1. Under these four natural inequalities, membership is "
                    + "equivalent to the displayed six integer inequalities. The last two bounds "
                    + "remove the two triangular corners."),
            SharedTheorem("polygon-card", "polygon_card", "Polygon cardinality", PolygonCardFormula(),
                "When l+r≤A+B+1, the removed corners are disjoint. Their doubled sizes are "
                    + "l(l+1) and r(r+1). Subtracting them from twice the rectangle size gives "
                    + "the formula. The cardinality is cast to an integer before multiplication."),
            SharedTheorem("shell-finite", "shell_finite", "Finiteness of every distance shell",
                All("n", Naturals(), App(Q("Set", "Finite"), SetOf("s", V("Simplex"),
                    Eq(Call("distance", V("s")), V("n"))))),
                "Every shell is contained in the finite coordinate ball of the same radius. "
                    + "Here distance uses the upward-face root, and n is any natural number."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Barker's generating-function identity"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write R(i,j,p,q) for "
                        + "TeaCoordinationSequence.residual, the nonnegative horizontal excess "
                        + "beyond −q≤i,j,i+j≤p. The potential at V(i,j) is 1+2R(i,j,1,0), "
                        + "at U(i,j) it is 2R(i,j,0,0), and at W(i,j) it is "
                        + "2R(i+1,j+1,1,−1). The bound residual_le_iff gives the six "
                        + "coordinate inequalities for each of these three cases.")),
                    Paragraph(Text("For each simplex type the proof takes the maximum of six "
                        + "affine functions of i and j and a baseline zero or one. The affine "
                        + "functions measure violations of the bounding lattice-polygon inequalities. "
                        + "Every simplex inclusion changes this integer potential by at most one. "
                        + "The potential is nonnegative and vanishes exactly at the root. "
                        + "At any other simplex, an incident simplex has potential smaller by one. "
                        + "For a vertex one can choose a containing face; for a face one can choose "
                        + "one of its vertices; for an edge one can choose an endpoint or a containing "
                        + "face. Strong induction constructs a walk attaining the potential. "
                        + "The lower bound for every walk then identifies it with graph distance.")),
                    Paragraph(Text("The vertex and face slices reuse TeaCoordinationSequence.hexagon_mem "
                        + "and hexagon_card. For radius 2(k+1), the vertex slice is hexagon(k+1,k) "
                        + "and the upward-face slice is hexagon(k+1,k+1). At radius 2(k+1)+1 "
                        + "the vertex slice is hexagon(k+2,k+1), while the upward-face slice "
                        + "is unchanged. For either radius the downward-face slice maps bijectively "
                        + "to hexagon(k+2,k) by (i,j)↦(i+1,j+1). All endpoints are nonnegative, "
                        + "as required by the shared count 2|hexagon(p,q)|=p²+4pq+q²+3p+3q+2.")),
                    Paragraph(Text("For the horizontal-edge slice, translate to natural coordinates "
                        + "0≤u≤A, 0≤v≤B, l≤u+v and u+v+r≤A+B. The excluded corners contain "
                        + "l(l+1)/2 and r(r+1)/2 points by Finset.Nat.card_antidiagonal and "
                        + "Finset.sum_range_id_mul_two. They are disjoint under l+r≤A+B+1 "
                        + "and fit under l,r≤min(A+1,B+1). The vertical-edge slice has the same "
                        + "count by (i,j)↦(j,i); the diagonal-edge slice has the same count by "
                        + "(i,j)↦(i,−i−j). Summing the six slices gives 18k²+12k+1 points "
                        + "at distance at most 2k and 18k²+24k+7 at distance at most 2k+1, "
                        + "for every natural k. The distance lower bound directly uses the frozen "
                        + "VertexPositionRatioRefutation.potential_dist.")),
                    Paragraph(Text("Successive ball differences give a(0)=1, a(2k+1)=12k+6 "
                        + "and a(2k+2)=24(k+1). Comparing coefficients of the displayed formal "
                        + "product proves the identity over the integers. PowerSeries.mk assigns "
                        + "the integer cast of a(n) to coefficient n; all exponents and coefficient "
                        + "indices are natural numbers. Subtraction of such indices in coefficient "
                        + "calculations is truncated natural subtraction. The series requires no "
                        + "analytic convergence assumption. OEIS A298038 revision 45 names the "
                        + "hexavalent-root sequence and attributes the rational generating-function "
                        + "conjecture to Colin Barker."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("sloane298038"), ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string name, string title,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula SupportFormula()
    {
        var i = V("i"); var j = V("j");
        var p = Pair(i, j); var q = Pair(Add(i, D(1)), j);
        var r = Pair(i, Add(j, D(1))); var s = Pair(Add(i, D(1)), Add(j, D(1)));
        Formula At(byte t) => Call("support", Pair(D(t), Pair(i, j)));
        return All("i", Integers(), All("j", Integers(), And(
            Eq(At(0), FiniteSet(p)), And(Eq(At(1), FiniteSet(p, q)),
            And(Eq(At(2), FiniteSet(p, r)), And(Eq(At(3), FiniteSet(q, r)),
            And(Eq(At(4), FiniteSet(p, q, r)), Eq(At(5), FiniteSet(q, r, s)))))))));
    }

    private static Formula GraphFormula()
    {
        var s = V("s"); var t = V("t");
        var a = Call("support", s); var b = Call("support", t);
        return All("s", V("Simplex"), All("t", V("Simplex"),
            Iff(App(Q("SimpleGraph", "Adj"), V("graph"), s, t),
                And(Seq(s, Sp, Neq, Sp, t), Or(Subset(a, b), Subset(b, a))))));
    }

    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries", "X");
        var series = App(Q("PowerSeries", "mk"),
            Seq(LambdaLower, Sp, V("n"), Sp, Mapsto, Sp,
                Cast(Call("a", V("n")), Integers())));
        return Eq(Mul(Pow(Parenthesized(Sub(D(1), Pow(Cast(x,
                    Call("PowerSeries", Integers())), D(2)))), D(2)), series),
            Add(Add(Add(Add(D(1), Mul(D(6), x)), Mul(D(2, 2), Pow(x, D(2)))),
                Mul(D(6), Pow(x, D(3)))), Pow(x, D(4))));
    }

    private static DocumentBlock SharedTheorem(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula PolygonParameters(Formula body)
    {
        foreach (var name in new[] { "j0", "i0" }) body = All(name, Integers(), body);
        foreach (var name in new[] { "r", "l", "B", "A" }) body = All(name, Naturals(), body);
        return body;
    }

    private static Formula PolygonHypotheses(Formula body, bool disjoint)
    {
        if (disjoint) body = Implies(Le(Add(V("l"), V("r")), Add(Add(V("A"), V("B")), D(1))), body);
        foreach (var (c, bound) in new[] { ("r", "B"), ("r", "A"), ("l", "B"), ("l", "A") })
            body = Implies(Le(V(c), Add(V(bound), D(1))), body);
        return body;
    }

    private static Formula PolygonFormula()
    {
        var p = V("p");
        var map = Seq(LambdaLower, Sp, p, Sp, Mapsto, Sp,
            Pair(Add(V("i0"), Cast(Projection(p, 1), Integers())),
                Add(V("j0"), Cast(Projection(p, 2), Integers()))));
        var antidiagonal = Seq(Operatorname,
            Grp(V("Finset"), Dot, V("HasAntidiagonal"), Dot, V("antidiagonal")));
        Formula Triangle(Formula n) => App(Q("Finset", "biUnion"),
            App(Q("Finset", "range"), n), antidiagonal);
        var q = V("q");
        var reflection = Seq(LambdaLower, Sp, q, Colon, Sp, Product(Naturals(), Naturals()),
            Sp, Mapsto, Sp, Pair(Sub(V("A"), Projection(q, 1)), Sub(V("B"), Projection(q, 2))));
        var rectangle = App(Q("Finset", "product"),
            App(Q("Finset", "range"), Add(V("A"), D(1))),
            App(Q("Finset", "range"), Add(V("B"), D(1))));
        var corner = App(Q("Finset", "image"), Parenthesized(reflection), Triangle(V("r")));
        var cutRectangle = App(Q("Finset", "sdiff"), rectangle,
            App(Q("Finset", "union"), Triangle(V("l")), corner));
        return PolygonParameters(Eq(Polygon(), App(Q("Finset", "image"), Parenthesized(map),
            cutRectangle)));
    }

    private static Formula PolygonMembershipFormula()
    {
        var i = Projection(V("p"), 1); var j = Projection(V("p"), 2);
        var sum = Sub(Sub(Add(i, j), V("i0")), V("j0"));
        var conditions = And(Le(V("i0"), i), And(Le(i, Add(V("i0"), Cast(V("A"), Integers()))),
            And(Le(V("j0"), j), And(Le(j, Add(V("j0"), Cast(V("B"), Integers()))),
            And(Le(Cast(V("l"), Integers()), sum),
                Le(Add(sum, Cast(V("r"), Integers())), Add(Cast(V("A"), Integers()), Cast(V("B"), Integers()))))))));
        return PolygonParameters(PolygonHypotheses(All("p", Product(Integers(), Integers()),
            Iff(Seq(V("p"), Sp, InMacro, Sp, Polygon()), conditions)), false));
    }

    private static Formula PolygonCardFormula()
    {
        var a = Cast(V("A"), Integers()); var b = Cast(V("B"), Integers());
        var l = Cast(V("l"), Integers()); var r = Cast(V("r"), Integers());
        return PolygonParameters(PolygonHypotheses(Eq(Mul(D(2), Cast(App(Q("Finset", "card"), Polygon()), Integers())),
            Sub(Sub(Mul(Mul(D(2), Add(a, D(1))), Add(b, D(1))), Mul(l, Add(l, D(1)))), Mul(r, Add(r, D(1))))), true));
    }

    private static Formula Polygon() => Call("polygon", V("A"), V("B"), V("l"), V("r"), V("i0"), V("j0"));
    private static Formula Projection(Formula p, byte i) => Seq(p, Dot, D(i));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Implies(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Longrightarrow, Sp, Parenthesized(b));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, Parenthesized(b));
    private static Formula FiniteSet(params Formula[] values) =>
        Seq(OpenBrace, Seq(Separated(values)), CloseBrace);
    private static Formula[] Separated(Formula[] values) => values.SelectMany((v, i) =>
        i == 0 ? new[] { v } : new[] { Comma, Sp, v }).ToArray();
    private static Formula Cast(Formula f, Formula t) => Parenthesized(Seq(f, Colon, Sp, t));
    private static Formula SetOf(string name, Formula t, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, t, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Subset(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula t, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
}
