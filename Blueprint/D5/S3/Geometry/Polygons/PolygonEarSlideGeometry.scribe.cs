using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideGeometryFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.";
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("polygon-ear-slide-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual polygon ear slide geometry",
        H("Actual carrier and cyclic crossing geometry"), Blocks(
            Node("IsSegment", "Segments", Scope(All("e", Chord, IffF(C("IsSegment", X("e")), Not(C("IsDiag", X("e")))))),
                "A segment has distinct endpoints in the symmetric square.", DescribeRole.Definition),
            Node("IsSide", "Boundary sides", Scope(All("e", Chord, IffF(C("IsSide", X("e")), ExistsF("i", Vertex, EqF(X("e"), Pair(X("i"), AddF(X("i"), N(1)))))))),
                "An unordered boundary side joins successive cyclic vertices. symPair denotes the unordered pair s(a,b).", DescribeRole.Definition),
            Node("IsDiagonal", "Internal diagonals", Scope(All("e", Chord, IffF(C("IsDiagonal", X("e")), AndF(C("IsSegment", X("e")), Not(C("IsSide", X("e"))))))),
                "Internal diagonals are segments that are not boundary sides.", DescribeRole.Definition),
            Node("Cross", "Actual cyclic crossing", Scope(All("e", Chord, All("f", Chord,
                IffF(C("Cross", X("e"), X("f")), ExistsF("a", Vertex, ExistsF("b", Vertex, ExistsF("c", Vertex, ExistsF("d", Vertex,
                    AndF(EqF(X("e"), Pair(X("a"), X("b"))), AndF(EqF(X("f"), Pair(X("c"), X("d"))),
                        AndF(C("sbtw", X("a"), X("c"), X("b")), C("sbtw", X("b"), X("d"), X("a"))))))))))))),
                "Crossing uses strict cyclic betweenness witnesses.", DescribeRole.Definition),
            Node("IsTriangulation", "Maximal noncrossing finite diagonal carrier", Scope(All("T", Chords,
                IffF(Tri(X("T")), AndF(Diagonals(X("T")), AndF(
                    All("e", Chord, All("f", Chord, Imp(InF(X("e"), X("T")), Imp(InF(X("f"), X("T")), Not(C("Cross", X("e"), X("f"))))))),
                    All("e", Chord, Imp(C("IsDiagonal", X("e")), Imp(Not(InF(X("e"), X("T"))),
                        ExistsF("f", Chord, AndF(InF(X("f"), X("T")), C("Cross", X("e"), X("f")))))))))))),
                "The carrier contains every maximal noncrossing finite set of internal diagonals; no completion is selected.", DescribeRole.Definition),
            Node("ear", "Ear diagonal at a cyclic centre", Scope(All("i", Vertex,
                EqF(C("ear", X("i")), Pair(Sub(X("i"), N(1)), AddF(X("i"), N(1)))))),
                "The local names sEar, tEar, uEar denote ear(1), ear(2), ear(3).", DescribeRole.Definition),
            Node("vertexSwap", "Exchange the two local vertices", Scope(All("i", Vertex,
                EqF(C("vertexSwap", X("n"), X("i")), C("swap", N(1), N(2), X("i"))))),
                "The vertex permutation exchanges 1 and 2 and fixes every other vertex.", DescribeRole.Definition),
            Node("chordSwap", "Induced unordered-chord exchange", Scope(All("e", Chord,
                EqF(C("chordSwap", X("e")), C("map", C("vertexSwap", X("n")), X("e"))))),
                "Symmetric-square map transports each unordered pair.", DescribeRole.Definition),
            Node("AvoidTwo", "Avoid the deleted centre", Scope(All("e", Chord,
                IffF(C("AvoidTwo", X("e")), All("x", Vertex, Not(EqF(X("e"), Pair(N(2), X("x")))))))),
                "Every endpoint avoids vertex 2.", DescribeRole.Definition),
            Node("cross_chordSwap_of_avoidTwo", "Crossing transport away from centre 2", Scope(All("e", Chord, All("f", Chord,
                Imp(Lower(6), Imp(C("AvoidTwo", X("e")), Imp(C("AvoidTwo", X("f")),
                    IffF(C("Cross", C("chordSwap", X("e")), C("chordSwap", X("f"))), C("Cross", X("e"), X("f"))))))))),
                "Crossing is transported in both directions, including across the cyclic seam.")), []));

}

internal static class PolygonEarSlideGeometryFormula
{
    internal static Formula X(string name) => F.Id(name);
    internal static Formula N(int n) => n == 14 ? D(1,4) : D((byte)n);
    internal static Formula C(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    internal static Formula Vertex => C("ZMod", X("n"));
    internal static Formula Chord => new Formula.Apply(Seq(Operatorname, Grp(X("Sym"), D(2))), [Vertex]);
    internal static Formula Sets => C("Finset", Vertex);
    internal static Formula Chords => C("Finset", Chord);
    internal static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    internal static Formula ExistsF(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    internal static Formula Scope(Formula body) => All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
    internal static Formula SetsAll(Formula body, params string[] names) { for (int i = names.Length - 1; i >= 0; i--) body = All(names[i], Sets, body); return body; }
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open, f, Close) : f;
    internal static Formula R(Formula a, Formula op, Formula b) => Seq(Open, Operand(a), Sp, op, Sp, Operand(b), Close);
    internal static Formula EqF(Formula a, Formula b) => R(a, F.Eq, b);
    internal static Formula IffF(Formula a, Formula b) => R(a, F.Iff, b);
    internal static Formula AndF(Formula a, Formula b) => R(a, Land, b);
    internal static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Open, a, Close);
    internal static Formula InF(Formula a, Formula b) => R(a, InMacro, b);
    internal static Formula SubF(Formula a, Formula b) => R(a, Subseteq, b);
    internal static Formula AddF(Formula a, Formula b) => R(a, Plus, b);
    internal static Formula Sub(Formula a, Formula b) => R(a, Minus, b);
    internal static Formula Union(Formula a, Formula b) => R(a, Cup, b);
    internal static Formula Inter(Formula a, Formula b) => C("inter", a, b);
    internal static Formula Erase(Formula a, Formula b) => C("erase", a, b);
    internal static Formula Insert(Formula a, Formula b) => C("insert", a, b);
    internal static Formula Pair(Formula a, Formula b) => C("symPair", a, b);
    internal static Formula Ear(int i) => C("ear", N(i));
    internal static Formula Ears(Formula t) => C("EarCenters", t);
    internal static Formula Tri(Formula t) => C("IsTriangulation", t);
    internal static Formula Diagonals(Formula t) => All("e", Chord, Imp(InF(X("e"), t), C("IsDiagonal", X("e"))));
    internal static Formula Fibre(Formula j, Formula r) => C("ConditionFiber", X("P"), X("Q"), j, r);
    internal static Formula Lower(int n) => R(N(n), Leq, X("n"));
    internal static Formula Pos(bool cyclic, int i) => cyclic ? (i == 0 ? X("a") : AddF(X("a"), N(i))) : N(i);
    internal static Formula Reduced(bool cyclic) => Erase(Erase(X("J"), Pos(cyclic, 2)), Pos(cyclic, 3));
    internal static Formula LocalHyp(bool cyclic, Formula body) => Imp(Not(InF(Pos(cyclic, 0), X("J"))),
        Imp(InF(Pos(cyclic, 1), X("J")), Imp(InF(Pos(cyclic, 2), X("J")),
            Imp(SubF(X("R"), Erase(Erase(Erase(X("J"), Pos(cyclic, 1)), Pos(cyclic, 2)), Pos(cyclic, 3))), body))));
}
