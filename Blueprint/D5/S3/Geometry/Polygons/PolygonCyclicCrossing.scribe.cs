using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;
internal sealed class PolygonCyclicCrossingDocument : IScribeDocumentDefinition
{
    private static Formula X(string n) => F.Id(n);
    private static Formula C(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(n))), [.. args]);
    private static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open, a, Sp, op, Sp, b, Close);
    private static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    private static Formula V(string i) => C("vertex", X("p"), X(i));
    private static Formula Pair(string a, string b) => C("pair", X(a), X(b));
    private static Formula Setup(Formula body)
    {
        body = Imp(C("BoundaryModel", X("p")), body);
        body = All("p", C("Polygon", X("E"), X("n")), body);
        body = Imp(R(D(3), Leq, X("n")), body);
        body = Imp(R(C("finrank", X("Real"), X("E")), F.Eq, D(2)), body);
        body = All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
        return All("E", X("Type"), Seq(
            OpenBracket, C("NormedAddCommGroup", X("E")), CloseBracket, Sp,
            OpenBracket, C("NormedSpace", X("Real"), X("E")), CloseBracket, Comma, Sp, body));
    }
    private static Formula Labels(Formula body)
    {
        foreach (var i in new[] { "d", "c", "b", "a" }) body = All(i, C("ZMod", X("n")), body);
        return body;
    }
    private static Formula ArcSign()
    {
        Formula g(string i) => R(C("f", V(i)), Minus, C("f", V("a")));
        Formula body = R(R(g("c"), Times, g("d")), Gt, D(0));
        body = Imp(R(C("f", V("b")), F.Eq, C("f", V("a"))), body);
        body = Imp(R(X("f"), Neq, D(0)), body);
        body = All("f", C("ContinuousLinearMap", X("Real"), X("E"), X("Real")), body);
        body = Imp(C("sbtw", X("a"), X("d"), X("b")), body);
        body = Imp(C("sbtw", X("a"), X("c"), X("b")), body);
        body = Imp(R(X("a"), Neq, X("b")), body);
        return Setup(Labels(body));
    }
    private static Formula OppositeSide()
    {
        Formula body = R(C("SOppSide", C("line", X("Real"), V("a"), V("b")), V("c"), V("d")),
            Iff, C("Cross", Pair("a", "b"), Pair("c", "d")));
        foreach (var pair in new[] { ("d", "b"), ("d", "a"), ("c", "b"), ("c", "a"), ("a", "b") })
            body = Imp(R(X(pair.Item1), Neq, X(pair.Item2)), body);
        return Setup(Labels(body));
    }
    private static Formula Crossing() => Setup(All("e", C("Sym2", C("ZMod", X("n"))),
        All("f", C("Sym2", C("ZMod", X("n"))),
            R(C("Cross", X("e"), X("f")), Iff, C("ProperCross", X("p"), X("e"), X("f")))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic arcs and proper crossing of actual polygon chords", H("The same polygon and all labelled chords"), Blocks(
            Paragraph(Text("Let p be an actual real normed plane polygon satisfying BoundaryModel, with n at least three. Use precisely its existing ZMod.finEquiv relabelling and successor edges. Pair(a,b) is the native unordered pair, and Cross is its existing cyclic alternation predicate. ProperCross(p,e,f) instead requires representatives of e and f whose actual endpoints are distinct within each chord, whose two endpoint sets are disjoint, and whose actual open segments have a common point. It contains no cyclic-order or native-Cross condition. Thus loops, shared endpoints and coincident chords are explicitly excluded even though Mathlib's open segment from a point to itself is nonempty.")),
            Describe.Lean(DescribeId.Create("polygon-cyclic-arc-sign"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCyclicCrossing.same_arc_sign"),
                H("Strict side constancy on each actual cyclic open arc"),
                StatementSource.FromAuthor(Disp(ArcSign())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Choose any nonzero continuous linear functional with equal values at the distinct chord endpoints. No third extreme vertex can have that value in a plane. If the functional changed sign across an actual successor edge away from the chord endpoints, its zero level would meet that edge in an open-segment point. The chord line intersects the hull only in the chord segment by endpoint extremality. G4 makes every open diagonal point interior, contradicting boundary coverage; the supporting-functional argument handles the side case using the existing G4 maximal-endpoint and common-level results.")),
                    Paragraph(Text("Write L=(b-a).val and w(k)=a+k. The existing basePos circular-order supplier identifies sbtw(a,x,b) exactly with 0<(x-a).val<L. Finite induction over successive k propagates the strict sign along this actual chain. This includes wraparound without changing the polygon or replacing the cyclic order. An adjacent chord has an empty short open arc, so no strict-side assertion is imposed on that absent chain."))
                )),
            Describe.Lean(DescribeId.Create("polygon-cyclic-opposite-side"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCyclicCrossing.sOppSide_iff_cross"),
                H("Actual opposite sides and cyclic alternation"),
                StatementSource.FromAuthor(Disp(OppositeSide())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("If two nonempty open arcs had the same strict sign, constancy and the exact two-arc partition would put all vertices in the same closed functional halfplane. Convex-hull minimality extends this bound to the hull. The existing supporting_pair_is_side theorem forces the chord endpoints to be cyclic successors, contrary to nonemptiness of the short arc. The two arcs therefore have opposite signs.")),
                    Paragraph(Text("The one-dimensional span of the chord difference is proper in the plane. Apply Mathlib's nonzero annihilator theorem and finite-dimensional continuity to obtain the required chord functional. Its level is exactly the chord line. Strict opposite scalar signs are equivalent to SOppSide: scalar interpolation produces an actual open-segment point on the line, and conversely the SOppSide betweenness witness maps into the scalar interval. Combining this equivalence with the two actual arc signs gives precisely native Cross. The conclusion allows c=d, for which both sides are false; four distinct labels are included."))
                )),
            Describe.Lean(DescribeId.Create("polygon-native-proper-crossing"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonCyclicCrossing.cross_iff_properCross"),
                H("The complete native chord universe"),
                StatementSource.FromAuthor(Disp(Crossing())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For alternating labels, SOppSide gives an actual intersection point of the second open chord with the first chord line. Hull convexity and extremality of the first endpoints put that point in the first open chord. Conversely, a proper open-chord intersection gives strict betweenness through the first line. No third extreme vertex lies on this line, so the second endpoints are strictly on opposite sides and the preceding theorem gives native Cross. The theorem quantifies over every unordered vertex pair, with no ear-only or nondegeneracy restriction on the input universe. Loops, either side orientation, the seam, shared endpoints, coincident chords and non-ear diagonals are all covered.")),
                    Paragraph(Text("Under the ordinary filled-convex genuine-corners convention for the fixed labelled fourteen-gon in the original source, PolygonFilledBoundary.boundaryModel_of_filled supplies BoundaryModel for the very same p and C. Apply this crossing theorem to the original ears e_i=pair(i-1,i+1), and apply PolygonCompressionTrace.cross_ear_iff_adjacent with n=14. It follows that these actual original ear chords properly geometrically cross exactly when j=i+1 or i=j+1 modulo fourteen. This is the literal first sentence of the existing section 40.2. It is a direct application, with no retained ear specialization or new theory clause.")),
                    Paragraph(Text("This correspondence does not establish the equivalence from a merely simple no-reflex predicate, whole geometric triangulations or maximality, complete-ear transports, arbitrary-family transports, witness conditions, completion fibres or counting. The remaining clauses of the mixed source atom and the broader original C0 and FIB objectives remain separate obligations."))
                ))
        ), []));
}
