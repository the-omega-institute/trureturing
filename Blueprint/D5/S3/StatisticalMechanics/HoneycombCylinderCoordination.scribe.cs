using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class HoneycombCylinderCoordinationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/HoneycombCylinderCoordination";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/sloane2019a329512");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coordination sequence of every diagonal honeycomb cylinder satisfies the "
            + "generating-function identity conjectured in OEIS A329512.",
        H("Coordination sequences of diagonal honeycomb cylinders"),
        Blocks(
            Paragraph(Text("OEIS A329512, revision 40, calls row n the coordination sequence for "
                + "a cylinder formed by rolling up a strip of width 2n hexagons, cut perpendicular "
                + "to grid lines. The coordinate model identifies translation through "
                + "(n,n). All positive natural n are quantified. False labels A vertices and true "
                + "labels B vertices; each vertex is a nested pair (label,(i,j)). In the formulas, "
                + "fst and snd are the literal product projections. The formulas display the edge relation "
                + "and the diagonal translation explicitly.")),
            Definition("vertex", "Vertex", "The labeled integer lattice",
                Eq(V("Vertex"), Product(V("Bool"), Product(Integers(), Integers()))),
                "The coordinates i and j range independently over all integers."),
            Definition("honeycomb", "honeycombGraph", "The literal honeycomb graph", GraphFormula(),
                "The neighbours of A(i,j) are B(i,j), B(i−1,j) and B(i,j−1). "
                    + "The second disjunct supplies the reverse edges. The Boolean labels differ "
                    + "along every edge, so the graph has no loops."),
            Definition("translation", "translationSetoid", "Integral powers of the translation",
                TranslationFormula(),
                "The integer k may have either sign or be zero. The Boolean label is fixed. "
                    + "The cast of n to the integers is taken before multiplication by k."),
            Definition("quotient", "Cylinder", "The quotient vertex type",
                All("n", Naturals(), Eq(Call("Cylinder", V("n")),
                    Call("Quotient", Call("translationSetoid", V("n"))))),
                "The quotient is by precisely the displayed translation equivalence relation."),
            Definition("cylinder-graph", "cylinderGraph", "The quotient simple graph",
                All("n", Naturals(), Eq(Call("cylinderGraph", V("n")),
                    App(Q("SimpleGraph", "map"), Projection(V("n")), V("honeycombGraph")))),
                "SimpleGraph.map puts an edge between distinct quotient vertices when adjacent "
                    + "representatives exist. No honeycomb edge collapses, because translation "
                    + "preserves the Boolean label. The projection therefore maps walks to walks "
                    + "without changing their length."),
            Definition("origin", "origin", "The specified center",
                All("n", Naturals(), Eq(Call("origin", V("n")),
                    App(Projection(V("n")), Pair(V("false"), Pair(D(0), D(0)))))),
                "The center is the class of A(0,0)."),
            Definition("shell-count", "c", "The literal finite shell cardinality", CountFormula(),
                "SimpleGraph.dist is the minimum walk length. Every quotient vertex is reachable "
                    + "from the center. The proof identifies every shell with a finite sum of "
                    + "finite integer-coordinate fibers, proving finiteness for every positive "
                    + "n and every natural radius, including zero. Nat.card counts the subtype "
                    + "in the formula; no proposed shell formula is used in its definition."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("The all-width formal series identity"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write s=i+j. On A vertices the plane distance is twice the "
                        + "maximum of 0, i, j, s, −i, −j and −s. On B vertices it is one plus twice "
                        + "the maximum of 0, i, j, s, −i−1, −j−1 and −s−1. Each edge changes "
                        + "this nonnegative potential by at most one. An explicit adjacent vertex "
                        + "decreases every positive potential by one; strong induction constructs "
                        + "a walk attaining the bound. The generic potential bound supplies the "
                        + "opposite inequality, so these are genuine graph distances.")),
                    Paragraph(Text("Every quotient walk lifts from any chosen initial representative, "
                        + "with its length preserved. Thus quotient distance is the minimum of "
                        + "the plane distances of representatives. Every A class has a unique "
                        + "representative with −n<s≤n; every B class has a unique representative "
                        + "with −n≤s<n. Euclidean division constructs these representatives. "
                        + "The six inequalities in the potential prove that each is minimizing. "
                        + "Integer division uses a nonnegative remainder modulo the positive "
                        + "integer 2n.")),
                    Paragraph(Text("At plane A-radius 2k with k>0, each slice −k<s<k contributes "
                        + "two points, and each boundary slice s=k or s=−k contributes k+1. "
                        + "Intersecting with the A strip gives 6k when 0<k<n, 5n−1 when k=n, "
                        + "and 4n when k>n. At B-radius 2k+1, the interior slices −k≤s<k "
                        + "contribute two each, and the boundary slices s=k and s=−k−1 "
                        + "contribute k+1 and k+2. Intersecting with the B strip gives 6k+3 "
                        + "for k<n and 4n otherwise. The radius-zero count is one. Hence the "
                        + "count at positive radius m is 3m before 2n, 5n−1 at 2n, and 4n after it.")),
                    Paragraph(Text("PowerSeries.mk assigns the integer-cast shell count to each "
                        + "coefficient. Comparing second differences proves the displayed identity. "
                        + "C is the PowerSeries constant-series map. In C((n:ℤ)−2) and "
                        + "C((n:ℤ)−1), subtraction is in the integers; the first coefficient is "
                        + "−1 at n=1. Subtraction in 2n−2 is natural truncated subtraction and "
                        + "n≥1 makes it nonnegative. The source uses two factors of 1/(1−X). "
                        + "Since 1−X has constant coefficient one, it is a unit in the integer "
                        + "formal series ring. Multiplying by its square gives exactly the "
                        + "displayed equivalent cleared identity. No convergence hypothesis "
                        + "or statement about a physical nanotube is involved."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("sloane329512"), ResolutionKind.Proved))));

    private static DocumentBlock Definition(string id, string name, string title, Formula formula,
        string commentary) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(commentary))), DescribeRole.Definition);

    private static Formula GraphFormula()
    {
        var u = V("u"); var v = V("v");
        Formula Edge(Formula a, Formula b) => Or(
            And(Eq(I(a), I(b)), Eq(J(a), J(b))),
            Or(And(Eq(I(a), Add(I(b), D(1))), Eq(J(a), J(b))),
                And(Eq(I(a), I(b)), Eq(J(a), Add(J(b), D(1))))));
        Formula Directed(Formula a, Formula b) =>
            And(Eq(Color(a), V("false")), And(Eq(Color(b), V("true")), Edge(a, b)));
        return All("u", V("Vertex"), All("v", V("Vertex"),
            Iff(App(Q("SimpleGraph", "Adj"), V("honeycombGraph"), u, v),
                Or(Directed(u, v), Directed(v, u)))));
    }

    private static Formula TranslationFormula()
    {
        var n = V("n"); var u = V("u"); var v = V("v"); var k = V("k");
        var delta = Mul(Cast(n, Integers()), k);
        return All("n", Naturals(), All("u", V("Vertex"), All("v", V("Vertex"),
            Iff(App(Q("Setoid", "r"), Call("translationSetoid", n), u, v),
                Ex("k", Integers(), Eq(Pair(Color(u), Pair(Add(I(u), delta), Add(J(u), delta))), v))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var m = V("m"); var v = V("v");
        var predicate = Lambda("v", Call("Cylinder", n),
            Eq(App(Q("SimpleGraph", "dist"), Call("cylinderGraph", n), Call("origin", n), v), m));
        return All("n", Naturals(), All("m", Naturals(),
            Eq(Call("c", n, m), App(Q("Nat", "card"), Call("Subtype", predicate)))));
    }

    private static Formula ResultFormula()
    {
        var n = V("n"); var x = Q("PowerSeries", "X");
        var nn = Mul(D(2), n);
        var series = App(Q("PowerSeries", "mk"),
            Lambda("m", Naturals(), Cast(Call("c", n, V("m")), Integers())));
        Formula C(Formula a) => App(Q("PowerSeries", "C"), a);
        var bracket = Sub(Sub(Add(D(1), Mul(D(2), x)),
            Mul(C(Sub(Cast(n, Integers()), D(2))), Pow(x, nn))),
            Mul(C(Sub(Cast(n, Integers()), D(1))), Pow(x, Add(nn, D(1)))));
        var rhs = Add(Mul(Parenthesized(Sub(D(1), x)), Parenthesized(bracket)),
            Mul(Mul(D(3), Pow(x, D(2))), Parenthesized(Sub(D(1), Pow(x, Sub(nn, D(2)))))));
        return All("n", Naturals(), Imp(Le(D(1), n),
            Eq(Mul(Pow(Parenthesized(Sub(D(1), x)), D(2)), series), rhs)));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Projection(Formula n) =>
        App(Q("Quotient", "mk"), Call("translationSetoid", n));
    private static Formula Color(Formula v) => App(Q("Prod", "fst"), v);
    private static Formula I(Formula v) => App(Q("Prod", "fst"), App(Q("Prod", "snd"), v));
    private static Formula J(Formula v) => App(Q("Prod", "snd"), App(Q("Prod", "snd"), v));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, Parenthesized(b));
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula t, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula t, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula t, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
}
