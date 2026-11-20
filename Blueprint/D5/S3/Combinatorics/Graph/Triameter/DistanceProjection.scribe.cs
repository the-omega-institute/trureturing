using System;
using System.Collections.Generic;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Triameter;

internal sealed class DistanceProjectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Triameter/DistanceProjection";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/hakkozerenko2026triameter");

    private static readonly AssessedProvenance Literature = AssessedProvenance.FromLiterature(Source);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective distance projections transfer distance-packing estimates to connected graphs.",
        H("Distance projection and packing comparison for triameter"),
        Blocks(
            DescribeNode("even-leg-vertex", "Vertex", "EvenLegTriangle.Vertex",
                ForAll(Eqn(Vertex(F.Id("q")), LayerIndices(i =>
                    Seq(D(2), Cdot, ApplyName("q", i), Plus, D(1)))), Bound("q", QType)),
                "This gives leg and depth coordinates for the vertices of U(2q₀, 2q₁, 2q₂) in §2.1. "
                    + "A vertex is a dependent pair of a leg i and a depth from zero through 2q(i).",
                DescribeRole.Definition, Literature),
            DescribeNode("even-leg-graph", "H", "EvenLegTriangle.H",
                ForAll(Seq(Adj(ApplyName("EvenLegTriangle.H", F.Id("q")), F.Id("x"), F.Id("y")), Sp, Leftrightarrow, Sp,
                    Parenthesized(Seq(SameLeg, Sp, Land, Sp, Parenthesized(Seq(
                        Step(F.Id("x"), F.Id("y")), Sp, Lor, Sp, Step(F.Id("y"), F.Id("x")))))),
                    Sp, Lor, Sp, Parenthesized(Seq(Leg(F.Id("x")), Sp, Neq, Sp, Leg(F.Id("y")), Sp, Land, Sp,
                        Eqn(Depth(F.Id("x")), D(0)), Sp, Land, Sp, Eqn(Depth(F.Id("y")), D(0))))),
                    Bound("q", QType), ModelVertex("x"), ModelVertex("y")),
                "This is the triangle with attached paths U(2q₀, 2q₁, 2q₂) from §2.1. "
                    + "Edges join consecutive depths on each leg and join every two distinct roots.",
                DescribeRole.Definition, Literature),
            DescribeNode("triameter-perimeter", "perimeter", "perimeter",
                ForAll(Eqn(ApplyName("perimeter", F.Id("G"), F.Id("a")),
                    Seq(Dist(0, 1), Plus, Dist(0, 2), Plus, Dist(1, 2))),
                    Bound("V", Qualified("Type")), GraphBinder,
                    Bound("a", Seq(ApplyName("Fin", D(3)), Sp, To, Sp, F.Id("V")))),
                "This is the perimeter of an ordered triple from §2.2. "
                    + "Each SimpleGraph.dist term counts the edges of a shortest walk when its endpoints are reachable.",
                DescribeRole.Definition, Literature),
            DescribeNode("graph-triameter", "triameter", "triameter",
                GraphForall(Eqn(TriameterValue, ApplyName("Finset.sup",
                    Qualified("Finset.univ"), ApplyName("perimeter", F.Id("G"))))),
                "This is the triameter of §2.2, with the supremum taken over every function Fin 3 → V. "
                    + "Triples can contain repeated vertices. The supremum is zero on an empty vertex type.",
                DescribeRole.Definition, Literature),
            DescribeNode("triameter-upper-independence", "triameter_le_indepNum",
                "Independence upper bound for triameter",
                GraphForall(Seq(Connected, Sp, Longrightarrow, Sp,
                    TriameterValue, Plus, D(1), Sp, Le, Sp, D(4), Cdot, IndepNum)),
                "Corollary 5.1, inequality (5), gives this bound at orders at least three. "
                    + "At connected orders one and two, the triameters are zero and two respectively, "
                    + "and both independence numbers are one. "
                    + "A maximizing triple admits a surjective distance projection onto three legs with a point "
                    + "or triangular centre. Lifting a packing of the model gives a packing of G. "
                    + "At distance threshold one, packings of G are independent sets.",
                DescribeRole.Theorem, Literature),
            DescribeNode("triameter-equality-projection", "k1_equality_projection",
                "Even-leg projection at independence equality",
                GraphForall(Seq(Connected, Sp, Longrightarrow, Sp, Parenthesized(Equality),
                    Sp, Longrightarrow, Sp, Exists, Sp, LegAndMapBinders, Comma, Sp,
                    Eqn(IndepNum, Seq(LegSum, Plus, D(1))), Sp, Land, Sp, Surjective, Sp, Land, Sp,
                    Parenthesized(EdgeMap), Sp, Land, Sp, Parenthesized(EdgeLift(ModelAdj(F.Id("u"), F.Id("v")))))),
                "The equality part of the proof of Theorem 1.1 at k = 1 forces a triangular centre "
                    + "and leg lengths 2q(i) in the canonical model of §3. "
                    + "Lemma 3.2 supplies the surjective non-expanding projection and the lift of every model edge. "
                    + "Section 2.1 expresses non-expansion as the edge-or-collapse condition. "
                    + "Equality cannot occur at connected orders one and two.",
                DescribeRole.Theorem, Literature),
            DescribeNode("triameter-even-leg-lower", "triameter_ge_of_evenLegTriangle",
                "Triameter lower bound from lifting the three feet",
                GraphForall(Seq(Connected, Sp, Longrightarrow, Sp, Forall, Sp, LegAndMapBinders, Comma, Sp,
                    Surjective, Sp, Longrightarrow, Sp, Parenthesized(EdgeMap), Sp, Longrightarrow, Sp,
                    D(4), Cdot, Parenthesized(LegSum), Plus, D(3), Sp, Le, Sp, TriameterValue)),
                "Choose preimages of the three feet under the surjective edge map. Walks between those "
                    + "preimages have length at least the distance between the corresponding feet. "
                    + "The sum of the foot distances from Lemma 2.5(2) gives the displayed lower bound "
                    + "for an arbitrary surjection satisfying the stated edge condition.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock.Describe DescribeNode(string id, string name, string title,
        Formula statement, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name), H(title),
            StatementSource.FromAuthor(F.Disp(statement)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Dist(byte i, byte j) =>
        ApplyName("SimpleGraph.dist", F.Id("G"), ApplyName("a", D(i)), ApplyName("a", D(j)));

    private static Formula ModelAdj(Formula x, Formula y) =>
        Adj(ApplyName("EvenLegTriangle.H", F.Id("q")), x, y);

    private static Formula EdgeMap =>
        Seq(Forall, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp, GraphAdj, Sp, Longrightarrow, Sp,
            Eqn(Image(F.Id("x")), Image(F.Id("y"))), Sp, Lor, Sp, ModelAdj(Image(F.Id("x")), Image(F.Id("y"))));
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula QType = Seq(ApplyName("Fin", D(3)), Sp, To, Sp, Nat);
    private static readonly Formula Connected = Qualified("G.Connected");
    private static readonly Formula TriameterValue = ApplyName("triameter", F.Id("G"));
    private static readonly Formula IndepNum = ApplyName("SimpleGraph.indepNum", F.Id("G"));
    private static readonly Formula Equality = Eqn(TriameterValue, Seq(D(4), Cdot, IndepNum, Minus, D(1)));
    private static readonly Formula LegSum = Seq(ApplyName("q", D(0)), Plus, ApplyName("q", D(1)), Plus, ApplyName("q", D(2)));
    private static readonly Formula LegAndMapBinders =
        Seq(Bound("q", QType), Sp, Bound("f", Seq(F.Id("V"), Sp, To, Sp, Vertex(F.Id("q")))));
    private static readonly Formula SameLeg = Eqn(Leg(F.Id("x")), Leg(F.Id("y")));
    private static readonly Formula GraphAdj = Adj(F.Id("G"), F.Id("x"), F.Id("y"));
    private static readonly Formula Surjective = ApplyName("Function.Surjective", F.Id("f"));

    private static Formula Qualified(string name)
    {
        var parts = new List<Formula>();
        foreach (var piece in name.Split('.'))
        {
            if (parts.Count != 0)
                parts.Add(Dot);
            parts.Add(F.Id(piece));
        }
        return Seq(Operatorname, Grp([.. parts]));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula ApplyName(string name, params Formula[] args) =>
        Seq(Qualified(name), Parenthesized(Separated(Seq(Comma, Sp), args)));

    private static Formula Separated(Formula separator, Formula[] items) =>
        Seq([.. items.SelectMany((item, index) => index == 0 ? new[] { item } : [separator, item])]);

    private static Formula Bound(string name, Formula type) => Parenthesized(Seq(F.Id(name), Colon, Sp, type));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula ForAll(Formula body, params Formula[] binders) =>
        Seq(Forall, Sp, Separated(Sp, binders), Comma, Sp, body);

    private static Formula ModelVertex(string name) => Bound(name, Vertex(F.Id("q")));
    private static Formula GraphBinder => Bound("G", ApplyName("SimpleGraph", F.Id("V")));

    private static Formula GraphForall(Formula body) =>
        Seq(Forall, Sp, Bound("V", Qualified("Type")), Sp,
            OpenBracket, ApplyName("Fintype", F.Id("V")), CloseBracket, Sp,
            Bound("G", ApplyName("SimpleGraph", F.Id("V"))), Comma, Sp, body);
    private static Formula Vertex(Formula q) => ApplyName("EvenLegTriangle.Vertex", q);
    private static Formula Leg(Formula x) => ApplyName("Sigma.fst", x);
    private static Formula Depth(Formula x) => ApplyName("Fin.val", ApplyName("Sigma.snd", x));
    private static Formula Step(Formula x, Formula y) => Eqn(Seq(Depth(x), Plus, D(1)), Depth(y));
    private static Formula Adj(Formula graph, Formula x, Formula y) => ApplyName("SimpleGraph.Adj", graph, x, y);
    private static Formula Image(Formula x) => ApplyName("f", x);
    private static Formula LayerIndices(Func<Formula, Formula> size) =>
        Seq(Sigma, Sp, Bound("i", ApplyName("Fin", D(3))), Sp, ApplyName("Fin", size(F.Id("i"))));
    private static Formula EdgeLift(Formula condition) =>
        Seq(Forall, Sp, F.Id("u"), Sp, F.Id("v"), Comma, Sp, condition, Sp, Longrightarrow, Sp,
            Exists, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp, GraphAdj, Sp, Land, Sp,
            Eqn(Image(F.Id("x")), F.Id("u")), Sp, Land, Sp, Eqn(Image(F.Id("y")), F.Id("v")));
}
