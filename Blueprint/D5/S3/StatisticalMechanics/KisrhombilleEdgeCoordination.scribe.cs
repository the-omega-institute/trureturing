using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class KisrhombilleEdgeCoordinationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/sloane2018a298040");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's formal generating-function identity for the tetravalent root of the kisrhombille tiling.",
        H("Edge-rooted kisrhombille coordination"),
        Blocks(
            Paragraph(Text("Use KisrhombilleFaceCoordination.Simplex, support and graph. A simplex is "
                + "(t,(i,j)), with t in Fin 6 and integer coordinates i,j. Types zero through five "
                + "are a vertex V, horizontal edge H, vertical edge B, diagonal edge D, upward face U "
                + "and downward face W. Two distinct simplices are adjacent exactly when their finite "
                + "vertex supports are comparable by inclusion. The triangular lattice has difference "
                + "vectors ±(1,0), ±(0,1), ±(1,−1). In particular, vertices are adjacent to containing "
                + "faces as well as containing edges. U(i,j) has vertices (i,j),(i+1,j),(i,j+1); "
                + "W(i,j) has vertices (i+1,j),(i,j+1),(i+1,j+1).")),
            Definition("root", "root", "The specified edge", Eq(V("root"), Pair(D(1), Pair(D(0), D(0)))),
                "This is H(0,0), whose support is {(0,0),(1,0)}. Its four neighbors are V(0,0), "
                    + "V(1,0), U(0,0) and W(0,−1)."),
            Definition("distance", "distance", "Minimum walk length", All("s", V("Simplex"),
                Eq(Call("distance", V("s")),
                    App(Q("SimpleGraph", "dist"), V("graph"), V("root"), V("s")))),
                "Distance is the genuine shortest-walk distance in the shared inclusion graph. "
                    + "The proof constructs a walk from this root to every simplex."),
            Definition("count", "a", "Finite distance shells", All("n", Naturals(),
                Eq(Call("a", V("n")), App(Q("Set", "ncard"),
                    SetOf("s", V("Simplex"), Eq(Call("distance", V("s")), V("n")))))),
                "Set.ncard gives the natural cardinality. Each shell is finite: the face-root distance "
                    + "is at most the edge-root distance plus one, so this shell lies in a finite union "
                    + "of the finite face-root shells. The radius-zero shell contains exactly the root."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Barker's generating-function identity"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("For a vertex at (i,j), take the maximum of 1, 1−2i, 2i−1, −2j, "
                        + "2j, 1−2(i+j), 2(i+j)−1. For U(i,j), take the maximum of 1, −2i, 2i, "
                        + "−2j−1, 2j+1, −2(i+j), 2(i+j). For W(i,j), replace the last two terms "
                        + "by −2(i+j)−2 and 2(i+j)+2. An edge other than the root has potential one "
                        + "plus the minimum potential of its two endpoints and two containing faces; "
                        + "the root has potential zero. Inclusion changes potential by at most one. "
                        + "Every positive-potential simplex has an incident simplex with potential "
                        + "one smaller. Induction builds a walk attaining this potential, and "
                        + "VertexPositionRatioRefutation.potential_dist gives the matching lower bound.")),
                    Paragraph(Text("At radius 2k+1 the six coordinate-slice counts, in type order, "
                        + "are 3k²+5k+2, 3k²+3k+1, 3k²+5k, 3k²+5k, 3k²+4k+1, 3k²+4k+1. "
                        + "At radius 2k+2 they are 3k²+7k+4, 3k²+9k+3, 3k²+7k+4, "
                        + "3k²+7k+4, 3k²+8k+5, 3k²+8k+5. These formulas hold for every natural k. "
                        + "The horizontal-edge slice at odd radius uses TeaCoordinationSequence.hexagon "
                        + "and its count. Other polygon counts use KisrhombilleFaceCoordination.polygon_mem "
                        + "and polygon_card. The even horizontal-edge slice and positive odd vertical-edge "
                        + "slice each adjoin two disjoint boundary rows to a polygon. Reflection gives "
                        + "equal vertical and diagonal counts, and equal upward and downward face counts.")),
                    Paragraph(Text("Summing gives ball sizes 18k²+26k+5 at radius 2k+1 and "
                        + "18k²+46k+25 at radius 2k+2. Successive differences give a(0)=1, a(1)=4, "
                        + "a(2k+2)=20(k+1) and a(2k+3)=16k+24. Coefficient comparison proves the "
                        + "displayed identity. PowerSeries.mk assigns coefficient n the integer cast "
                        + "of a(n); indices and powers are natural numbers, with truncated subtraction "
                        + "of indices. X denotes the formal indeterminate, and the cast on its first "
                        + "occurrence specifies PowerSeries ℤ. No convergence assumption is needed. "
                        + "OEIS A298040 revision 36 names the tetravalent-root sequence and attributes "
                        + "the rational generating-function conjecture to Colin Barker."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("sloane298040"), ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries", "X");
        var series = App(Q("PowerSeries", "mk"), Seq(LambdaLower, Sp, V("n"), Sp, Mapsto, Sp,
            Cast(Call("a", V("n")), Integers())));
        return Eq(Mul(Pow(Parenthesized(Sub(D(1), Pow(Cast(x, Call("PowerSeries", Integers())), D(2)))), D(2)), series),
            Sub(Add(Add(Add(Add(D(1), Mul(D(4), x)), Mul(D(1,8), Pow(x,D(2)))),
                Mul(D(1,6), Pow(x,D(3)))), Pow(x,D(4))), Mul(D(4), Pow(x,D(5)))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Cast(Formula f, Formula t) => Parenthesized(Seq(f, Colon, Sp, t));
    private static Formula SetOf(string name, Formula t, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, t, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula t, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
}
