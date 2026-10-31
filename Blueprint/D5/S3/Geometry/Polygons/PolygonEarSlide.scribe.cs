using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarSlideFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarSlide.";
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("polygon-ear-slide-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual polygon condition preserving ear slide",
        H("Actual polygon carrier and complete conditioned fibres"), Blocks(
            Node("IsSegment", "Segments", Scope(All("e", Chord, IffF(C("IsSegment", X("e")), Not(C("IsDiag", X("e")))))),
                "A segment has distinct endpoints in the symmetric square.", DescribeRole.Definition),
            Node("IsSide", "Boundary sides", Scope(All("e", Chord, IffF(C("IsSide", X("e")), ExistsF("i", Vertex, EqF(X("e"), Pair(X("i"), AddF(X("i"), N(1)))))))),
                "An unordered boundary side joins successive cyclic vertices.", DescribeRole.Definition),
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
            Node("EarCenters", "All ears of the actual chord set", Scope(All("T", Chords, All("i", Vertex,
                IffF(InF(X("i"), Ears(X("T"))), InF(C("ear", X("i")), X("T")))))),
                "Every ear of the complete finite chord set is observed.", DescribeRole.Definition),
            Node("E_K", "Common compatible ear carrier", Scope(All("K", Sets, All("i", Vertex,
                IffF(InF(X("i"), C("EK", X("K"))), AndF(Not(InF(X("i"), X("K"))),
                    All("k", Vertex, Imp(InF(X("k"), X("K")), Not(C("Cross", C("ear", X("i")), C("ear", X("k"))))))))))),
                "EK denotes E_K: centres outside K whose ears cross no ear of K.", DescribeRole.Definition),
            Node("ConditionFiber", "Complete conditioned exact-trace fibre", Scope(SetsAll(EqF(
                Fibre(X("J"), X("X")), Seq(OpenBrace, X("T"), Colon, Sp, Chords, Sp, Bar, Sp,
                    AndF(Tri(X("T")), AndF(SubF(X("P"), Ears(X("T"))),
                        AndF(C("Disjoint", X("Q"), Ears(X("T"))), EqF(Inter(Ears(X("T")), X("J")), X("X"))))), CloseBrace)), "P", "Q", "J", "X")),
                "P is forced, Q is forbidden, and the entire observed J trace equals X. The subtype includes infeasible empty fibres.", DescribeRole.Definition),
            Node("vertexSwap", "Exchange the two local vertices", Scope(All("i", Vertex,
                EqF(C("vertexSwap", X("n"), X("i")), C("swap", N(1), N(2), X("i"))))),
                "The vertex permutation exchanges 1 and 2 and fixes every other vertex.", DescribeRole.Definition),
            Node("chordSwap", "Induced unordered-chord exchange", Scope(All("e", Chord,
                EqF(C("chordSwap", X("e")), C("map", C("vertexSwap", X("n")), X("e"))))),
                "Symmetric-square map transports each unordered pair.", DescribeRole.Definition),
            Node("AvoidTwo", "Avoid the deleted centre", Scope(All("e", Chord,
                IffF(C("AvoidTwo", X("e")), All("x", Vertex, Not(EqF(X("e"), Pair(N(2), X("x")))))))),
                "Every endpoint avoids vertex 2.", DescribeRole.Definition),
            Node("isTriangulation_map_add", "Cyclic translation of all triangulations", Scope(All("T", Chords, All("a", Vertex,
                Imp(Tri(X("T")), Tri(C("shiftChords", X("T"), X("a"))))))),
                "shiftChords(T,a) is the finite image of T under the chord map x -> x+a. Diagonal, noncrossing, and maximality conditions are preserved."),
            Node("cross_chordSwap_of_avoidTwo", "Crossing transport away from centre 2", Scope(All("e", Chord, All("f", Chord,
                Imp(Lower(6), Imp(C("AvoidTwo", X("e")), Imp(C("AvoidTwo", X("f")),
                    IffF(C("Cross", C("chordSwap", X("e")), C("chordSwap", X("f"))), C("Cross", X("e"), X("f"))))))))),
                "Crossing is transported in both directions, including across the cyclic seam."),
            Node("avoidTwo_of_mem_triangulation", "Ear-centre exclusion", Scope(All("T", Chords, All("e", Chord,
                Imp(Lower(6), Imp(Tri(X("T")), Imp(InF(Ear(2), X("T")), Imp(InF(X("e"), X("T")), C("AvoidTwo", X("e"))))))))),
                "A triangulation containing t has no internal diagonal incident with its centre 2."),
            Node("phi", "Forward complete chord map", MapFormula(true),
                "Erase t, exchange vertices 1 and 2 in every retained chord, and insert s.", DescribeRole.Definition),
            Node("psi", "Inverse complete chord map", MapFormula(false),
                "Erase s, apply the same vertex exchange, and insert t.", DescribeRole.Definition),
            Node("phi_isTriangulation", "Forward actual triangulation preservation", Preserve(true),
                "Diagonal and crossing preservation use ear-centre exclusion; maximality handles the fresh s separately."),
            Node("psi_isTriangulation", "Inverse actual triangulation preservation", Preserve(false),
                "The inverse preserves the full maximal diagonal carrier."),
            Node("psi_phi", "Left inverse on complete chord sets", Inverse(true),
                "The inverse law requires only diagonal membership and the stated included and excluded ears."),
            Node("phi_psi", "Right inverse on complete chord sets", Inverse(false),
                "This equality holds for the entire finite chord set."),
            Node("trace_phi", "Forward exact observed-ear trace", Trace(true),
                "J omits 0 and includes 1,2. R is supported on J with 1,2,3 erased. The output retains exactly R and centre 1 on J with 2,3 erased."),
            Node("trace_psi", "Inverse exact observed-ear trace", Trace(false),
                "The same complete J-origin, membership and R-support hypotheses recover exactly R and centre 2 on the original J."),
            Node("condition_fibre_equiv", "Normalized complete conditioned fibre equivalence", Equivalence(false),
                "J lies in E_K(P union Q), omits 0 and contains 1,2; R lies in J with 1,2,3 erased. All forced and forbidden conditions are preserved. No cardinality, P/Q disjointness or compatibility premise is needed for this local equivalence."),
            Node("condition_fibre_equiv_at", "Complete fibre equivalence at every cyclic origin", Equivalence(true),
                "Conjugation by cyclic translation includes every origin a, the cyclic seam, and empty fibres. The cardinality theorem in PolygonEarSlideCardinality consumes this equivalence on its live proof path.")), []));

    private static Formula MapFormula(bool forward) => Scope(All("T", Chords,
        EqF(C(forward ? "phi" : "psi", X("T")), Insert(Ear(forward ? 1 : 2),
            C("image", X("chordSwap"), Erase(X("T"), Ear(forward ? 2 : 1)))))));
    private static Formula Preserve(bool forward) => Scope(All("T", Chords,
        Imp(Lower(6), Imp(Tri(X("T")), Imp(InF(Ear(forward ? 2 : 1), X("T")),
            Tri(C(forward ? "phi" : "psi", X("T"))))))));
    private static Formula Inverse(bool forward) => Scope(All("T", Chords,
        Imp(Lower(6), Imp(Diagonals(X("T")), Imp(InF(Ear(forward ? 2 : 1), X("T")),
            Imp(Not(InF(Ear(forward ? 1 : 2), X("T"))),
                EqF(C(forward ? "psi" : "phi", C(forward ? "phi" : "psi", X("T"))), X("T"))))))));
    private static Formula Trace(bool forward) => Scope(All("T", Chords, SetsAll(
        Imp(Lower(14), Imp(Tri(X("T")), Imp(InF(Ear(forward ? 2 : 1), X("T")),
            LocalHyp(false, Imp(EqF(Inter(Ears(X("T")), forward ? X("J") : Reduced(false)),
                Insert(N(forward ? 2 : 1), X("R"))),
                EqF(Inter(Ears(C(forward ? "phi" : "psi", X("T"))), forward ? Reduced(false) : X("J")),
                    Insert(N(forward ? 1 : 2), X("R")))))))), "J", "R")));
    private static Formula Equivalence(bool cyclic) => Scope(SetsAll(cyclic ? All("a", Vertex, EquivBody(true)) : EquivBody(false), "P", "Q", "J", "R"));
    private static Formula EquivBody(bool cyclic) => Imp(Lower(14), Imp(SubF(X("J"), C("EK", Union(X("P"), X("Q")))),
        LocalHyp(cyclic, C("Equiv", Fibre(X("J"), Insert(Pos(cyclic, 2), X("R"))), Fibre(Reduced(cyclic), Insert(Pos(cyclic, 1), X("R")))))));
}

internal static class PolygonEarSlideFormula
{
    internal static Formula X(string name) => F.Id(name);
    internal static Formula N(int n) => n == 14 ? D(1,4) : D((byte)n);
    internal static Formula C(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    internal static Formula Vertex => C("ZMod", X("n"));
    internal static Formula Chord => C("SymTwo", Vertex);
    internal static Formula Sets => C("Finset", Vertex);
    internal static Formula Chords => C("Finset", Chord);
    internal static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    internal static Formula ExistsF(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    internal static Formula Scope(Formula body) => All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
    internal static Formula SetsAll(Formula body, params string[] names) { for (int i = names.Length - 1; i >= 0; i--) body = All(names[i], Sets, body); return body; }
    internal static Formula R(Formula a, Formula op, Formula b) => Seq(Open, a, Sp, op, Sp, b, Close);
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
