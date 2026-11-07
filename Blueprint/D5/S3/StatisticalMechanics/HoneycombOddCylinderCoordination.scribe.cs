using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class HoneycombOddCylinderCoordinationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/HoneycombOddCylinderCoordination";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/StatisticalMechanics/sloane2019a329515");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coordination sequence of every odd-width honeycomb cylinder satisfies the generating-function identity in OEIS A329515.",
        H("Coordination sequences of odd-width honeycomb cylinders"),
        Blocks(
            Paragraph(Text("OEIS A329515, revision 32, gives the odd-width family with the half-hexagon seam offset. "
                + "The coordinate model identifies (i,j) with (i+n+1,j+n), so the translation changes i+j by 2n+1. "
                + "False labels A vertices and true labels B vertices; the formulas display the edge relation and the offset translation explicitly.")),
            Definition("vertex", "Vertex", "The labeled integer lattice",
                Eq(V("Vertex"), Product(V("Bool"), Product(Integers(), Integers()))),
                "The coordinates i and j range independently over all integers."),
            Definition("translation", "translationSetoid", "Integral powers of the offset translation",
                TranslationFormula(),
                "The integer k may have either sign or be zero. The Boolean label is fixed. The first coordinate receives n+1 and the second n."),
            Definition("quotient", "Cylinder", "The quotient vertex type",
                All("n", Naturals(), Eq(Call("Cylinder", V("n")),
                    Call("Quotient", Call("translationSetoid", V("n"))))),
                "The quotient is by precisely the displayed translation equivalence relation."),
            Definition("cylinder-graph", "cylinderGraph", "The quotient simple graph",
                All("n", Naturals(), Eq(Call("cylinderGraph", V("n")),
                    App(Q("SimpleGraph", "map"), Projection(V("n")), V("honeycombGraph")))),
                "SimpleGraph.map puts an edge between distinct quotient vertices when adjacent representatives exist."),
            Definition("origin", "origin", "The specified center",
                All("n", Naturals(), Eq(Call("origin", V("n")),
                    App(Projection(V("n")), Pair(V("false"), Pair(D(0), D(0))))),
                "The center is the class of A(0,0)."),
            Definition("shell-count", "c", "The literal finite shell cardinality", CountFormula(),
                "SimpleGraph.dist is the minimum walk length. Every quotient shell is finite, and c counts the subtype at the displayed distance."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("The all-width odd-cylinder formal series identity"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The imported honeycomb distance is twice the TeaCoordinationSequence residual on A vertices and one plus twice that residual on B vertices. "
                        + "The existing geodesic construction and plane-distance identity are reused directly.")),
                    Paragraph(Text("The offset translation changes s=i+j by 2n+1. Euclidean division gives a unique A representative with −n≤s≤n and a unique B representative with −n−1≤s≤n−1. "
                        + "The potential inequalities show these representatives minimize distance in each quotient class, including n=0.")),
                    Paragraph(Text("At A-radius 2k with k>0, the shell count is 6k for k<n, 6n for k=n, and 4n+2 for k>n. At B-radius 2k+1 it is 6k+3 for k<n, 5n+2 for k=n, and 4n+2 for k>n; the radius-zero count is one. "
                        + "Thus positive radii are 3m before 2n+1, 5n+2 at 2n+1, and 4n+2 afterwards.")),
                    Paragraph(Text("Comparing second differences of the integer-cast shell series gives exactly the displayed identity. No convergence or physical realization is asserted."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title, Formula formula, string commentary) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(commentary))), DescribeRole.Definition);

    private static Formula TranslationFormula()
    {
        var n = V("n"); var u = V("u"); var v = V("v"); var k = V("k");
        var deltaI = Mul(Add(Cast(n, Integers()), D(1)), k);
        var deltaJ = Mul(Cast(n, Integers()), k);
        return All("n", Naturals(), All("u", V("Vertex"), All("v", V("Vertex"),
            Iff(App(Q("Setoid", "r"), Call("translationSetoid", n), u, v),
                Ex("k", Integers(), Eq(Pair(Color(u), Pair(Add(I(u), deltaI), Add(J(u), deltaJ))), v))))));
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
        var series = App(Q("PowerSeries", "mk"), Lambda("m", Naturals(), Cast(Call("c", n, V("m")), Integers())));
        Formula C(Formula a) => App(Q("PowerSeries", "C"), a);
        var bracket = Sub(Sub(Add(D(1), Mul(D(2), x)),
            Mul(C(Sub(Cast(n, Integers()), D(2))), Pow(x, Add(Mul(D(2), n), D(1))))),
            Mul(C(Cast(n, Integers())), Pow(x, Add(Mul(D(2), n), D(2)))));
        var rhs = Add(Add(Mul(Parenthesized(Sub(D(1), x)), Parenthesized(bracket)),
            Mul(D(3), Pow(x, D(2)))),
            Sub(D(0), Mul(D(3), Pow(x, Add(Mul(D(2), n), D(1))))));
        return All("n", Naturals(), Eq(Mul(Pow(Parenthesized(Sub(D(1), x)), D(2)), series), rhs));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Projection(Formula n) => App(Q("Quotient", "mk"), Call("translationSetoid", n));
    private static Formula Color(Formula v) => App(Q("Prod", "fst"), v);
    private static Formula I(Formula v) => App(Q("Prod", "fst"), App(Q("Prod", "snd"), v));
    private static Formula J(Formula v) => App(Q("Prod", "snd"), App(Q("Prod", "snd"), v));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
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
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, Parenthesized(b));
}
