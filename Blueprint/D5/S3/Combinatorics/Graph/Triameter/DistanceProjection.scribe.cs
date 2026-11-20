using System;
using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Triameter.TriameterNotation;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Triameter;

internal sealed class DistanceProjectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Triameter/DistanceProjection";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/hakkozerenko2026triameter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective distance projections transfer distance-packing estimates to connected graphs.",
        H("Distance projection and packing comparison for triameter"),
        Blocks(
            DescribeNode("even-leg-vertex", "Vertex", "EvenLegTriangle.Vertex",
                Eqn(Vertex(Id("q")), LayerIndices(i =>
                    Seq(D(2), Cdot, Call("q", i), Plus, D(1)))),
                "For q : Fin 3 → ℕ, a vertex is a dependent pair of a leg i and a depth from zero through 2q(i).",
                DescribeRole.Definition),
            DescribeNode("even-leg-graph", "H", "EvenLegTriangle.H",
                Seq(Adj(Call("EvenLegTriangle.H", Id("q")), Id("x"), Id("y")), Sp, Leftrightarrow, Sp,
                    Parenthesized(Seq(SameLeg, Sp, Land, Sp, Parenthesized(Seq(
                        Step(Id("x"), Id("y")), Sp, Lor, Sp, Step(Id("y"), Id("x")))))),
                    Sp, Lor, Sp, Parenthesized(Seq(Leg(Id("x")), Neq, Leg(Id("y")), Sp, Land, Sp,
                        Eqn(Depth(Id("x")), D(0)), Sp, Land, Sp, Eqn(Depth(Id("y")), D(0))))),
                "For q : Fin 3 → ℕ, EvenLegTriangle.H q is a simple graph on EvenLegTriangle.Vertex q. "
                    + "Edges join consecutive depths on each leg and join every two distinct roots.",
                DescribeRole.Definition),
            DescribeNode("triameter-perimeter", "perimeter", "perimeter",
                Eqn(Call("perimeter", Id("G"), Id("a")), Seq(Dist(0, 1), Plus, Dist(0, 2), Plus, Dist(1, 2))),
                "For G : SimpleGraph V and a : Fin 3 → V, perimeter G a is a natural number. "
                    + "Each SimpleGraph.dist term counts the edges of a shortest walk when its endpoints are reachable.",
                DescribeRole.Definition),
            DescribeNode("graph-triameter", "triameter", "triameter",
                Eqn(Triameter, Call("Finset.sup", Qualified("Finset.univ"), Call("perimeter", Id("G")))),
                "For G : SimpleGraph V with [Fintype V], the supremum is over every function Fin 3 → V. "
                    + "Triples can contain repeated vertices. The supremum is zero on an empty vertex type.",
                DescribeRole.Definition),
            DescribeNode("triameter-upper-independence", "triameter_le_indepNum",
                "Independence upper bound for triameter",
                GraphForall(Seq(Connected, Sp, Longrightarrow, Sp,
                    Triameter, Plus, D(1), Sp, Le, Sp, D(4), Cdot, IndepNum)),
                "A maximizing triple admits a surjective distance projection onto three legs with a point "
                    + "or triangular centre. Lifting a packing of the model gives a packing of G. "
                    + "At distance threshold one, packings of G are independent sets.",
                DescribeRole.Theorem),
            DescribeNode("triameter-equality-projection", "k1_equality_projection",
                "Even-leg projection at independence equality",
                GraphForall(Seq(Connected, Sp, Longrightarrow, Sp, Parenthesized(Equality),
                    Sp, Longrightarrow, Sp, Exists, Sp, LegAndMapBinders, Comma, Sp,
                    Eqn(IndepNum, Seq(LegSum, Plus, D(1))), Sp, Land, Sp, Surjective, Sp, Land, Sp,
                    Parenthesized(EdgeMap), Sp, Land, Sp, Parenthesized(EdgeLift(ModelAdj(Id("u"), Id("v")))))),
                "Equality forces a triangular centre and even leg lengths. The projection is surjective. "
                    + "Its image of each edge either collapses to one vertex or lies on a model edge. "
                    + "Every ordered model edge also has a lift to an edge of G.",
                DescribeRole.Theorem),
            DescribeNode("triameter-even-leg-lower", "triameter_ge_of_evenLegTriangle",
                "Triameter lower bound from lifting the three feet",
                GraphForall(Seq(Connected, Sp, Longrightarrow, Sp, Forall, Sp, LegAndMapBinders, Comma, Sp,
                    Surjective, Sp, Longrightarrow, Sp, Parenthesized(EdgeMap), Sp, Longrightarrow, Sp,
                    D(4), Cdot, Parenthesized(LegSum), Plus, D(3), Sp, Le, Sp, Triameter)),
                "Choose preimages of the three feet under the surjective edge map. Walks between those "
                    + "preimages have length at least the distance between the corresponding feet. "
                    + "The sum of those three distances gives the displayed lower bound.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe DescribeNode(string id, string name, string title,
        Formula statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name), H(title),
            StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Dist(byte i, byte j) =>
        Call("SimpleGraph.dist", Id("G"), Call("a", D(i)), Call("a", D(j)));

    private static Formula ModelAdj(Formula x, Formula y) =>
        Adj(Call("EvenLegTriangle.H", Id("q")), x, y);

    private static Formula EdgeMap =>
        Seq(Forall, Sp, Id("x"), Sp, Id("y"), Comma, Sp, GraphAdj, Sp, Longrightarrow, Sp,
            Eqn(Image(Id("x")), Image(Id("y"))), Sp, Lor, Sp, ModelAdj(Image(Id("x")), Image(Id("y"))));
}

internal static class TriameterNotation
{
    internal static readonly Formula Nat = Seq(Mathbb, Grp(Id("N")));
    internal static readonly Formula QType = Seq(Call("Fin", D(3)), Sp, To, Sp, Nat);
    internal static readonly Formula Connected = Qualified("G.Connected");
    internal static readonly Formula Triameter = Call("triameter", Id("G"));
    internal static readonly Formula IndepNum = Call("SimpleGraph.indepNum", Id("G"));
    internal static readonly Formula Equality = Eqn(Triameter, Seq(D(4), Cdot, IndepNum, Minus, D(1)));
    internal static readonly Formula LegSum = Seq(Call("q", D(0)), Plus, Call("q", D(1)), Plus, Call("q", D(2)));
    internal static readonly Formula LegAndMapBinders =
        Seq(Bound("q", QType), Sp, Bound("f", Seq(Id("V"), Sp, To, Sp, Vertex(Id("q")))));
    internal static readonly Formula SameLeg = Eqn(Leg(Id("x")), Leg(Id("y")));
    internal static readonly Formula GraphAdj = Adj(Id("G"), Id("x"), Id("y"));
    internal static readonly Formula Surjective = Call("Function.Surjective", Id("f"));

    internal static Formula Qualified(string name)
    {
        var parts = new List<Formula>();
        foreach (var piece in name.Split('.'))
        {
            if (parts.Count != 0)
                parts.Add(Dot);
            parts.Add(Id(piece));
        }
        return Seq(Operatorname, Grp([.. parts]));
    }

    internal static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    internal static Formula Call(string name, params Formula[] args)
    {
        var arguments = new List<Formula>();
        foreach (var argument in args)
        {
            if (arguments.Count != 0)
                arguments.AddRange([Comma, Sp]);
            arguments.Add(argument);
        }
        return Seq(Qualified(name), Parenthesized(Seq([.. arguments])));
    }

    internal static Formula Bound(string name, Formula type) => Parenthesized(Seq(Id(name), Colon, Sp, type));
    internal static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    internal static Formula GraphForall(Formula body) =>
        Seq(Forall, Sp, Bound("V", Qualified("Type")), Sp,
            OpenBracket, Call("Fintype", Id("V")), CloseBracket, Sp,
            Bound("G", Call("SimpleGraph", Id("V"))), Comma, Sp, body);
    internal static Formula Vertex(Formula q) => Call("EvenLegTriangle.Vertex", q);
    internal static Formula Leg(Formula x) => Call("Sigma.fst", x);
    internal static Formula Depth(Formula x) => Call("Fin.val", Call("Sigma.snd", x));
    internal static Formula Step(Formula x, Formula y) => Eqn(Seq(Depth(x), Plus, D(1)), Depth(y));
    internal static Formula Adj(Formula graph, Formula x, Formula y) => Call("SimpleGraph.Adj", graph, x, y);
    internal static Formula Image(Formula x) => Call("f", x);
    internal static Formula LayerIndices(Func<Formula, Formula> size) =>
        Seq(Sigma, Sp, Bound("i", Call("Fin", D(3))), Sp, Call("Fin", size(Id("i"))));
    internal static Formula EdgeLift(Formula condition) =>
        Seq(Forall, Sp, Id("u"), Sp, Id("v"), Comma, Sp, condition, Sp, Longrightarrow, Sp,
            Exists, Sp, Id("x"), Sp, Id("y"), Comma, Sp, GraphAdj, Sp, Land, Sp,
            Eqn(Image(Id("x")), Id("u")), Sp, Land, Sp, Eqn(Image(Id("y")), Id("v")));
}
