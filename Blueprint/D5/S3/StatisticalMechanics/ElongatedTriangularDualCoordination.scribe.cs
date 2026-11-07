using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ElongatedTriangularDualCoordinationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/ElongatedTriangularDualCoordination";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Geometry/sloane2018a298022");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The face adjacency graph of the elongated triangular tiling, centered at an upward triangle, "
            + "has the coordination generating function conjectured by Colin Barker.",
        H("Trivalent coordination in the elongated triangular dual"),
        Blocks(
            Definition("vertex", "Vertex", "The three face types", VertexFormula(),
                "Vertex is the free inductive type with constructors Vertex.S, Vertex.U and Vertex.D. "
                    + "Each constructor takes two integers m and k. The constructors are injective, "
                    + "their ranges are disjoint, and every vertex has exactly one such form. "
                    + "S denotes a square, U an upward triangle and D a downward triangle."),
            Definition("square", "Vertex.S", "The square constructor", ConstructorFormula("S"),
                "S(m,k) is the square in strip m at position k."),
            Definition("upward", "Vertex.U", "The upward triangle constructor", ConstructorFormula("U"),
                "U(m,k) is the upward triangle in triangular strip m at position k."),
            Definition("downward", "Vertex.D", "The downward triangle constructor", ConstructorFormula("D"),
                "D(m,k) is the downward triangle in triangular strip m at position k."),
            Definition("graph", "graph", "The face adjacency graph", GraphFormula(),
                "The displayed five edge families and their reversals are all the edges. "
                    + "Thus a square S(m,k) has square neighbours S(m,k−1) and S(m,k+1), "
                    + "and triangular neighbours U(m,k) and D(m−1,k). An upward triangle "
                    + "has neighbours S(m,k), D(m,k−1), D(m,k). A downward triangle "
                    + "has neighbours S(m+1,k), U(m,k), U(m,k+1)."),
            Definition("root", "root", "The upward triangular root",
                Eq(V("root"), Face("U", D(0), D(0))),
                "This node has degree three."),
            Definition("distance", "distance", "The genuine graph distance", All("v", V("Vertex"),
                Eq(Call("distance", V("v")), App(Q("SimpleGraph", "dist"), V("graph"), V("root"), V("v")))),
                "SimpleGraph.dist is the minimum walk length. The distance proof constructs "
                    + "a walk from the root to every vertex."),
            Definition("count", "a", "The finite distance-shell cardinality", All("n", Naturals(),
                Eq(Call("a", V("n")), App(Q("Set", "ncard"),
                    SetOf("v", V("Vertex"), Eq(Call("distance", V("v")), V("n")))))),
                "The radius n ranges over all natural numbers, including zero. The proof "
                    + "identifies each shell with a finite set of coordinates; Set.ncard "
                    + "therefore counts a proved-finite shell."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Barker's formal series identity"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For an integer interval [l,u], write its distance from k as "
                        + "max(0,l−k,k−u). At S(m,k) the potential is 1−3m plus the "
                        + "distance from k to [0,−m] when m≤0, and 3m−1 plus the distance "
                        + "to [−m,0] when m>0. At U(m,k), for m<0 use −3m and [0,−m]; "
                        + "for m>0 use 3m and [−m,0]. At U(0,k) use min(2|k|,|k|+2). "
                        + "At D(m,k), for m<0 use −3m−1 and [0,−m−1]; for m>0 use "
                        + "3m+1 and [−m−1,0]. At D(0,k) use min(|2k+1|,min(|k|,|k+1|)+3).")),
                    Paragraph(Text("The potential is nonnegative and is zero precisely at U(0,0). "
                        + "For every edge, either endpoint's potential is at most one plus the "
                        + "other's. At every positive-potential vertex one of the displayed "
                        + "neighbours decreases the potential by exactly one. Strong induction "
                        + "constructs an attaining walk. The potential bound on walk length gives "
                        + "the reverse inequality, so the potential equals the graph distance.")),
                    Paragraph(Text("Separate the vertices into six infinite strip families and "
                        + "the central U and D rows. For r≥0 the strip representatives are "
                        + "S(−r,j), S(r+1,j−r−1), U(−r−1,j), U(r+1,j−r−1), "
                        + "D(−r−1,j), D(r+1,j−r−2). Their pairs (c,L) are respectively "
                        + "(1,1), (2,2), (3,2), (3,2), (2,1), (4,3). Each has distance "
                        + "3r+c+max(0,−j,j−r−L+1). At radius 3r+c its j interval is "
                        + "[0,r+L−1], containing r+L points; at a larger radius it has "
                        + "exactly two points, one on each side. No point occurs at a smaller radius.")),
                    Paragraph(Text("Consequently a strip contributes 2⌊(n+2−c)/3⌋, with "
                        + "truncated natural subtraction before division, and an additional "
                        + "(n−c)/3+L when c≤n and n−c is divisible by three. This follows by "
                        + "summing the row cardinalities over 0≤r≤n. The central U row contributes "
                        + "one at n=0, two at n=2, and two at every n≥4. The central D row "
                        + "contributes two at n=1, two at n=3, and two at every n≥5.")),
                    Paragraph(Text("For n≥5 the total is 14⌊n/3⌋ plus zero, five or nine "
                        + "according as n modulo three is zero, one or two. The first nine "
                        + "coefficients and this all-radius formula give the coefficient identity "
                        + "for (1−X)(1−X³), equal to (1−X)²(1+X+X²). Equality of coefficients "
                        + "proves the displayed identity in integer formal power series.")))))));

    private static Formula VertexFormula() => Eq(V("Vertex"),
        Seq(OpenBrace, Face("S", V("m"), V("k")), Comma, Sp,
            Face("U", V("m"), V("k")), Comma, Sp, Face("D", V("m"), V("k")),
            Sp, Mid, Sp, V("m"), Comma, V("k"), Sp, InMacro, Sp, Integers(), CloseBrace));

    private static Formula ConstructorFormula(string tag) =>
        Seq(Q("Vertex", tag), Colon, Sp, Integers(), Sp, Rightarrow, Sp,
            Integers(), Sp, Rightarrow, Sp, V("Vertex"));

    private static Formula GraphFormula()
    {
        var v = V("v"); var w = V("w");
        return All("v", V("Vertex"), All("w", V("Vertex"),
            Iff(App(Q("SimpleGraph", "Adj"), V("graph"), v, w),
                Or(Forward(v, w), Forward(w, v)))));
    }

    private static Formula Forward(Formula v, Formula w)
    {
        var m = V("m"); var k = V("k");
        Formula Edge(Formula left, Formula right) => And(Eq(v, left), Eq(w, right));
        return Ex("m", Integers(), Ex("k", Integers(),
            Or(Edge(Face("S", m, k), Face("S", m, Add(k, D(1)))),
            Or(Edge(Face("S", m, k), Face("U", m, k)),
            Or(Edge(Face("S", Add(m, D(1)), k), Face("D", m, k)),
            Or(Edge(Face("U", m, k), Face("D", m, k)),
                Edge(Face("U", m, k), Face("D", m, Sub(k, D(1))))))))));
    }

    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries", "X");
        var series = App(Q("PowerSeries", "mk"),
            Seq(LambdaLower, Sp, V("n"), Sp, Mapsto, Sp, Cast(Call("a", V("n")), Integers())));
        var denominator = Mul(Pow(Parenthesized(Sub(D(1), x)), D(2)),
            Parenthesized(Add(Add(D(1), x), Pow(x, D(2)))));
        return Eq(Mul(denominator, series),
            Sub(Add(Add(Add(Add(Add(D(1), Mul(D(2), x)), Mul(D(4), Pow(x, D(2)))),
                Mul(D(4), Pow(x, D(3)))), Mul(D(3), Pow(x, D(4)))), Mul(D(2), Pow(x, D(5)))),
                Mul(D(2), Pow(x, D(8)))));
    }

    private static DocumentBlock Definition(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Face(string tag, Formula m, Formula k) => App(Q("Vertex", tag), m, k);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Cast(Formula f, Formula t) => Parenthesized(Seq(f, Colon, Sp, t));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula t, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula t, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula t, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, t, Sp, Mid, Sp, body, CloseBrace);
}
