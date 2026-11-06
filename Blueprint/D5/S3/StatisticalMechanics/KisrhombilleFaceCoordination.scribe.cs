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
                    Paragraph(Text("A coordinate slice of a ball is a rectangle cut by two diagonal "
                        + "inequalities. Translate it to natural coordinates 0≤u≤A, 0≤v≤B, "
                        + "l≤u+v and u+v+r≤A+B. The excluded corners contain l(l+1)/2 and "
                        + "r(r+1)/2 points. They are disjoint under l+r≤A+B+1, and both fit "
                        + "in the rectangle under l,r≤min(A+1,B+1). Counting the antidiagonals "
                        + "proves these triangular counts. The sum over all six simplex types "
                        + "gives 18k²+12k+1 points at distance at most 2k, and 18k²+24k+7 "
                        + "points at distance at most 2k+1, for every natural k.")),
                    Paragraph(Text("Successive ball differences give a(0)=1, a(2k+1)=12k+6 "
                        + "and a(2k+2)=24(k+1). Comparing coefficients of the displayed formal "
                        + "product proves the identity over the integers. PowerSeries.mk assigns "
                        + "the integer cast of a(n) to coefficient n; all exponents and coefficient "
                        + "indices are natural numbers. Subtraction of such indices in coefficient "
                        + "calculations is truncated natural subtraction. The series requires no "
                        + "analytic convergence assumption. OEIS A298038 revision 45 names the "
                        + "hexavalent-root sequence and attributes the rational generating-function "
                        + "conjecture to Colin Barker."))),
                DescribeRole.Theorem))));

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
