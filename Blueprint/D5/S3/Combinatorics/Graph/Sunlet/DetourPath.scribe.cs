using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Sunlet;

internal sealed class DetourPathDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Sunlet/DetourPath.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/alsinai2026detour");
    private static readonly Formula N = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula n = F.Id("n");
    private static readonly Formula i = F.Id("i");
    private static readonly Formula j = F.Id("j");
    private static readonly Formula a = F.Id("a");
    private static readonly Formula b = F.Id("b");
    private static readonly Formula u = F.Id("u");
    private static readonly Formula v = F.Id("v");
    private static readonly Formula w = F.Id("w");
    private static readonly Formula s = F.Id("S");
    private static readonly Formula t = F.Id("T");
    private static readonly Formula ell = F.Id("L");
    private static readonly Formula Index = Call("Fin", n);
    private static readonly Formula Height = Call("Fin", D(2));
    private static readonly Formula Vertex = Seq(Index, Times, Height);
    private static readonly Formula Vertices = Call("Finset", Vertex);
    private static readonly Formula Orders = Call("maximalDDDOrders", n);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The lower and upper detour different-distance numbers of every sunlet are two.",
        H("Detour Different-Distance Numbers of Sunlets"),
        Blocks(
            Paragraph(DefinitionDsl.Text(
                "Alsinai and Ahmed state Problem 4.3 on page 13. “Determine ddD for lollipops, barbells "
                + "and tadpoles, and both numbers for grids, sunlets, snakes and generalized Petersen graphs.” "
                + "Their Theorem 2.14(i), applied to the triangle, gives both numbers for the three-index sunlet. "
                + "Their Lemma 3.4 gives the core–leaf pair at each index. "
                + "The result below gives both extrema for every cycle length n at least four.")),
            Node("sunlet", "The graph", "sunlet", Graph(),
                "The index lies in the cycle Cₙ. At each index, the vertex of height zero is on the cycle "
                + "and the vertex of height one has only the core vertex as its neighbor. "
                + "For n at least three this is the corona Cₙ ∘ K₁ of Section 2.8.",
                DescribeRole.Definition),
            Node("path-length-distinct", "Distinct indices", "sunlet_isGreatest_pathLength_of_index_ne",
                DistinctPath(),
                "Simple walks have no repeated vertices. Removing any leaf endpoint edges leaves one of "
                + "the two directed cycle arcs. Each arc extends to a simple path with the prescribed "
                + "leaf endpoints. The proof of Theorem 2.1 gives the longer-arc length in the bare cycle. "
                + "The block sum of Lemma 3.3 accounts for the endpoint edges. Subtraction of indices is "
                + "in Fin n and val gives the residue as a natural number.",
                DescribeRole.Theorem),
            Node("detour-distance", "Detour distance", "detourDistance", Detour(),
                "For n at least three the distinct-index path formula gives a greatest length. At a "
                + "single index, the trivial path gives the published zero diagonal. The pendant edge "
                + "is itself the unique simple path between the two heights, so their distance is one.",
                DescribeRole.Definition),
            Node("different-distance-set", "Detour different-distance sets", "IsDDD", DifferentDistance(),
                "The set is nonempty, proper, and distinguished in detour distance by every outside vertex, "
                + "as in Definition 1.1.",
                DescribeRole.Definition),
            Node("maximal-orders", "Orders of maximal sets", "maximalDDDOrders", MaximalOrders(),
                "Maximality uses inclusion among all detour different-distance sets.",
                DescribeRole.Definition),
            Node("sunlet-detour-numbers", "The lower and upper numbers", "sunlet_detour_numbers", Extrema(),
                "A detour tie from a third index forces both vertices there into the set. Color vertices "
                + "by height for odd n and by index plus height modulo two for even n. Two selected "
                + "vertices of one color at different indices force a full pair via the center of a "
                + "cycle arc. Any other selected index then forces a second full pair. If the closest "
                + "full indices are nonadjacent, an interior central vertex of a shortest arc has endpoint "
                + "distances differing by at most one. The two available heights allow a tie there, forcing "
                + "a closer full index. Adjacent full pairs force every index, violating properness. This bounds "
                + "every DDD set by two. Each singleton extends to its core–leaf pair, so the orders "
                + "of the inclusion-maximal sets form the singleton set containing two.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string decl, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(DefinitionDsl.Text(prose))), role);

    private static Formula Graph()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var xIndex = Call("fst", x);
        var yIndex = Call("fst", y);
        var xHeight = Call("snd", x);
        var yHeight = Call("snd", y);
        return All(n, N, All(x, Vertex, All(y, Vertex,
            Seq(Call("Adj", Call("sunlet", n), x, y), Sp, Iff, Sp,
                Paren(And(Equal(xIndex, yIndex), Unequal(xHeight, yHeight))), Sp, Lor, Sp,
                Paren(And(Equal(xHeight, D(0)), Equal(yHeight, D(0)),
                    Call("Adj", Call("cycleGraph", n), xIndex, yIndex)))))));
    }

    private static Formula DistinctPath() =>
        All(n, N, When(Seq(D(3), Sp, Leq, Sp, n),
            All(i, Index, All(j, Index, When(Unequal(i, j),
                All(a, Height, All(b, Height,
                    Call("IsGreatest", PathLengths(Tuple(i, a), Tuple(j, b)),
                        Seq(Call("max", Call("val", Seq(i, Minus, j)),
                            Call("val", Seq(j, Minus, i))), Plus, Call("val", a), Plus, Call("val", b))))))))));

    private static Formula Detour() =>
        All(n, N, All(u, Vertex, All(v, Vertex,
            Equal(Call("detourDistance", u, v), Call("sSup", PathLengths(u, v))))));

    private static Formula DifferentDistance()
    {
        var distinct = Unequal(Call("detourDistance", w, u), Call("detourDistance", w, v));
        var conditions = And(Seq(Neg, Sp, Paren(Member(w, s))), Member(u, s),
            Member(v, s), Unequal(u, v));
        return All(n, N, All(s, Vertices, Seq(Call("IsDDD", s), Sp, Iff, Sp,
            And(Unequal(s, Emptyset), Unequal(s, Call("univ", Vertex)),
                Paren(All(w, Vertex, All(u, Vertex, All(v, Vertex, When(conditions, distinct)))))))));
    }

    private static Formula MaximalOrders()
    {
        var size = F.Id("m");
        var maximal = All(t, Vertices, When(And(Call("IsDDD", t), Seq(s, Sp, Subseteq, Sp, t)),
            Seq(t, Sp, Subseteq, Sp, s)));
        return All(n, N, Equal(Orders, SetOf(size, N, Bind(Exists, s, Vertices,
            And(Call("IsDDD", s), Paren(maximal), Equal(Call("card", s), size))))));
    }

    private static Formula Extrema() =>
        All(n, N, When(Seq(D(4), Sp, Leq, Sp, n),
            And(Equal(Call("sInf", Orders), D(2)), Equal(Call("sSup", Orders), D(2)))));

    private static Formula PathLengths(Formula x, Formula y)
    {
        var p = F.Id("p");
        return SetOf(ell, N, Bind(Exists, p, Call("Walk", Call("sunlet", n), x, y),
            And(Call("IsPath", p), Equal(Call("length", p), ell))));
    }

    private static Formula SetOf(Formula x, Formula type, Formula condition) =>
        Seq(Operatorname, Grp(F.Id("Set"), Dot, F.Id("ofPred")),
            Paren(Bind(LambdaLower, x, type, condition)));
    private static Formula All(Formula x, Formula type, Formula body) => Bind(Forall, x, type, body);
    private static Formula Bind(Formula binder, Formula x, Formula type, Formula body) =>
        Seq(binder, Sp, Paren(Seq(x, Colon, type)), Comma, Sp, body);
    private static Formula When(Formula given, Formula body) => Seq(Paren(given), Sp, Implies, Sp, body);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Member(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Unequal(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);
    private static Formula And(params Formula[] terms) => Seq(
        terms.Skip(1).Aggregate(new[] { terms[0] }, (left, right) => [.. left, Sp, Land, Sp, right]));
    private static Formula Tuple(Formula x, Formula y) => Paren(Seq(x, Comma, y));
    private static Formula Paren(Formula contents) => Seq(Open, contents, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
