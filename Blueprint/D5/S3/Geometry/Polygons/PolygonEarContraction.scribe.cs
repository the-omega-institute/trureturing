using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarContractionFormula;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarContraction.";
    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("polygon-ear-contraction-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deletion and insertion of an actual polygon ear",
        H("Whole triangulation carriers"), Blocks(
            Paragraph(Text("Let V(k)=ZMod(k), C(k)=Sym2(V(k)), and F(k)=Finset(C(k)). A(k) denotes the subtype of all U in F(k) satisfying Carrier.IsTriangulation U: all chords are internal diagonals, no two cross, and every excluded internal diagonal crosses a member. B(k,i) is the subtype of all T in F(k) satisfying IsTriangulation T and ear(i) in T. These carriers contain all such chord sets. Strict betweenness uses the cyclic order of the labelled vertices.")),
            Node("vertexLift", "Insert vertex 1", Scope(All("x", V(X("m")),
                Eq(C("vertexLift", X("x")), C("natCast", C("ite", Eq(C("val", X("x")), N(0)), N(0), Add(C("val", X("x")), N(1))), Succ)))),
                "The natural representative zero stays zero; each positive representative increases by one. The cast lands in ZMod(m+1).", DescribeRole.Definition),
            Node("vertexDrop", "Relabel after deletion", Scope(All("x", V(Succ),
                Eq(C("vertexDrop", X("x")), C("natCast", C("natSub", C("val", X("x")), N(1)), X("m"))))),
                "Drop uses truncated natural subtraction followed by reduction modulo m. Its value at the removed vertex is never used on a retained chord.", DescribeRole.Definition),
            Node("chordLift", "Lift surviving chords", Scope(All("e", Ch(X("m")),
                Eq(C("chordLift", X("e")), C("map", X("e"), C("vertexLift"))))),
                "Apply vertexLift to both endpoints of an unordered chord.", DescribeRole.Definition),
            Node("chordDrop", "Drop surviving chords", Scope(All("e", Ch(Succ),
                Eq(C("chordDrop", X("e")), C("map", X("e"), C("vertexDrop"))))),
                "Apply vertexDrop to both endpoints.", DescribeRole.Definition),
            Node("boundary_lift_iff", "Exact boundary correspondence", Scope(All("e", Ch(X("m")),
                Imp(Bound, Iff(C("IsSide", X("e")), Or(C("IsSide", Lift(X("e"))), Eq(Lift(X("e")), Ear))))))),
                "The reduced boundary lifts precisely to original boundary sides with surviving endpoints together with the forced ear. The two original sides incident to the deleted centre are absent."),
            Node("reduce", "Delete the forced ear", Scope(All("T", Fs(Succ),
                Eq(C("reduce", X("T")), C("image", C("erase", X("T"), Ear), C("chordDrop")))))),
                "Remove ear(1) and retain every other original chord, with its exact surviving endpoints relabelled.", DescribeRole.Definition),
            Node("expand", "Insert the ear triangle", Scope(All("U", Fs(X("m")),
                Eq(C("expand", X("U")), C("insert", Ear, C("image", X("U"), C("chordLift"))))))),
                "Lift every chord of the reduced polygon and add exactly the forced ear.", DescribeRole.Definition),
            Node("reduce_isTriangulation", "Deletion preserves full maximality", Original(
                Tri(C("reduce", X("T"))))),
                "A diagonal incident to centre 1 crosses the forced ear, so every retained chord avoids the centre. Cyclic order preserves crossing. For a missing reduced diagonal, maximality upstairs supplies a crossing original chord; it cannot be the ear and therefore survives deletion."),
            Node("expand_isTriangulation", "Insertion preserves full maximality", Reduced(
                Tri(C("expand", X("U"))))),
                "A missing original internal diagonal either crosses the forced ear or avoids its centre and descends to a missing reduced internal diagonal. In the latter case full reduced maximality supplies a crossing chord."),
            Node("expand_reduce", "Recover every original chord", Original(
                Eq(C("expand", C("reduce", X("T"))), X("T")))),
                "The inverse recovers the entire original finite chord set, including its forced ear."),
            Node("reduce_expand", "Recover every reduced chord", Reduced(
                Eq(C("reduce", C("expand", X("U"))), X("U")))),
                "Every internal reduced diagonal lifts to an original internal diagonal distinct from the forced ear, and dropping its lift recovers it."),
            Node("earOneEquiv", "All completions at centre 1", Scope(Imp(Bound,
                EqType(C("B", Succ, N(1)), C("A", X("m")))))),
                "Deletion and insertion are mutually inverse on the full subtypes B(m+1,1) and A(m). The result permits m=5 and hence every original polygon size at least six.", DescribeRole.Definition),
            Node("earEquiv", "Arbitrary original ear centre", Scope(All("i", V(Succ), Imp(Bound,
                EqType(C("B", Succ, X("i")), C("A", X("m"))))))),
                "Translate by 1-i, apply earOneEquiv, and invert the translation on insertion. This gives an actual unbounded ear-deletion correspondence at every cyclic placement. It is the geometric deletion step used in the B-32 containing-event count. The count consumer uses the repeated correspondence below. Positivity, strictness and normalized equality are separate statements.", DescribeRole.Definition)
,
            Node("Compatible", "Pairwise compatible original ears",
                All("n", X("Nat"), All("P", C("Finset", V(X("n"))),
                    Iff(C("Compatible", X("P")),
                        All("i", V(X("n")), All("j", V(X("n")),
                            Imp(In(X("i"), X("P")), Imp(In(X("j"), X("P")),
                                Imp(C("ne", X("i"), X("j")), C("notCross", C("ear", X("i")), C("ear", X("j")))))))))),
                "Compatible means pairwise noncrossing on distinct selected centres; it assumes no triangulation or recursive count.", DescribeRole.Definition),
            Node("reducedCenters", "Relabel all remaining forced centres",
                Scope(All("P", C("Finset", V(Succ)), Eq(C("reducedCenters", X("P")),
                    C("image", C("erase", X("P"), N(1)), C("vertexDrop"))))),
                "The selected centre is erased, then every remaining selected centre is relabelled.", DescribeRole.Definition),
            Node("forcedOneEquiv", "All remaining compatible ears survive",
                Scope(All("P", C("Finset", V(Succ)), Imp(R(N(6), Leq, X("m")),
                    Imp(C("Compatible", X("P")), Imp(In(N(1), X("P")),
                        EqType(C("H", Succ, X("P")), C("H", X("m"), C("reducedCenters", X("P"))))))))),
                "H(k,P) is the subtype of all T in F(k) satisfying IsTriangulation T and P subset EarCenters T. Compatibility with ear(1) excludes the neighbouring centres 0 and 2. For each other selected centre, all three original vertices survive and its ear lifts exactly to the original ear. This preservation is derived, with no added survival premise.", DescribeRole.Definition),
            Node("forcedEquiv", "Iterate actual deletion over any compatible forced set",
                NScope(All("P", C("Finset", V(X("n"))),
                    Imp(R(N(6), Leq, C("natSub", X("n"), C("card", X("P")))),
                        Imp(C("Compatible", X("P")), EqType(C("H", X("n"), X("P")),
                            C("A", C("natSub", X("n"), C("card", X("P"))))))))),
                "Induction deletes one forced original centre at a time, composes the full correspondences, and reduces the forced-set cardinality by one. The result is a bijection onto all triangulations of the polygon with n-card(P) vertices. The size premise is exactly six remaining vertices and is preserved by each step.", DescribeRole.Definition),
            Node("compatible_card_bound", "Independent centres occupy at most half the boundary",
                NScope(All("P", C("Finset", V(X("n"))), Imp(R(N(6), Leq, X("n")),
                    Imp(C("Compatible", X("P")), R(C("mul", N(2), C("card", X("P"))), Leq, X("n")))))),
                "Adjacent ear centres have crossing ears. Hence a compatible selected set is disjoint from its translate by one, which has the same cardinality. Their union lies in the n boundary vertices. In particular, n at least fourteen leaves at least seven vertices after all compatible forced centres are deleted.")
        ), []));
}

internal static class PolygonEarContractionFormula
{
    internal static Formula X(string n) => F.Id(n);
    internal static Formula N(byte n) => D(n);
    internal static Formula C(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(n))), [.. args]);
    internal static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    internal static Formula R(Formula a, Formula op, Formula b) => Seq(Open, a, Sp, op, Sp, b, Close);
    internal static Formula Eq(Formula a, Formula b) => R(a, F.Eq, b);
    internal static Formula Iff(Formula a, Formula b) => R(a, F.Iff, b);
    internal static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    internal static Formula Or(Formula a, Formula b) => R(a, Lor, b);
    internal static Formula In(Formula a, Formula b) => R(a, InMacro, b);
    internal static Formula Add(Formula a, Formula b) => R(a, Plus, b);
    internal static Formula EqType(Formula a, Formula b) => C("Equiv", a, b);
    internal static Formula V(Formula k) => C("ZMod", k);
    internal static Formula Ch(Formula k) => C("Symtwo", V(k));
    internal static Formula Fs(Formula k) => C("Finset", Ch(k));
    internal static Formula Tri(Formula t) => C("IsTriangulation", t);
    internal static Formula Lift(Formula e) => C("chordLift", e);
    internal static Formula Succ => Add(X("m"), N(1));
    internal static Formula Ear => C("ear", N(1));
    internal static Formula Bound => R(N(5), Leq, X("m"));
    internal static Formula NScope(Formula body) => All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
    internal static Formula Scope(Formula body) => All("m", X("Nat"), Seq(OpenBracket, C("NeZero", X("m")), CloseBracket, Comma, Sp, body));
    internal static Formula Original(Formula body) => Scope(All("T", Fs(Succ), Imp(Bound, Imp(Tri(X("T")), Imp(In(Ear, X("T")), body)))));
    internal static Formula Reduced(Formula body) => Scope(All("U", Fs(X("m")), Imp(Bound, Imp(Tri(X("U")), body))));
}
