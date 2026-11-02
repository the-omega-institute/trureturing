using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonEarContractionFormula;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;
internal sealed class PolygonEarContractionDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("polygon-ear-contraction-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonEarContraction." + name),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deletion and insertion of actual polygon ears", H("Whole triangulation carriers"), Blocks(
            Paragraph(Text("V(k)=ZMod(k), C(k)=Sym2(V(k)), F(k)=Finset(C(k)). A(k) is the subtype of every U in F(k) satisfying Carrier.IsTriangulation U: internal-diagonal validity, pairwise noncrossing, and a crossing member for every missing internal diagonal. B(k,i) is the subtype of every T in F(k) satisfying IsTriangulation T and ear(i) in T. H(k,P) is the subtype of every T in F(k) satisfying IsTriangulation T and P subset EarCenters(T). Equiv means an actual bijection of these full subtypes. ne denotes inequality, notCross negates Carrier.Cross, and natSub is natural subtraction. Symtwo denotes Sym2. hasType(e,Equiv(A,B)) means e is the displayed equivalence from A to B; app, symm and val give application, inverse and the underlying full chord set. sub denotes subtraction in the cyclic vertex group. image(S,f) is the image of S under f, and map(e,f) maps both endpoints. choice is Classical.choice, and forcedequivexists denotes the private constructed Nonempty equivalence proof forced_equiv_exists. All natural casts in the vertex maps have the displayed modulus.")),
            Node("vertexLift", "Insert vertex 1",
                PlainScope(All("x", V(X("m")), Eq(C("vertexLift", X("x")), C("natCast", C("ite", Eq(C("val", X("x")), N(0)), N(0), AddF(C("val", X("x")), N(1))), Succ)))),
                "The natural representative zero stays zero; each positive representative increases by one. The cast lands in ZMod(m+1).", DescribeRole.Definition),
            Node("vertexDrop", "Relabel after deletion",
                PlainScope(All("x", V(Succ), Eq(C("vertexDrop", X("x")), C("natCast", C("natSub", C("val", X("x")), N(1)), X("m"))))),
                "Drop uses natural subtraction and casting into ZMod(m). Its value at the deleted vertex is never used on a retained chord.", DescribeRole.Definition),
            Node("chordLift", "Map both endpoints",
                PlainScope(All("e", Ch(X("m")), Eq(C("chordLift", X("e")), C("map", X("e"), C("vertexLift"))))),
                "The unordered chord is mapped endpoint by endpoint.", DescribeRole.Definition),
            Node("chordDrop", "Map both endpoints",
                PlainScope(All("e", Ch(Succ), Eq(C("chordDrop", X("e")), C("map", X("e"), C("vertexDrop"))))),
                "The unordered chord is mapped endpoint by endpoint.", DescribeRole.Definition),
            Node("boundary_lift_iff", "Exact boundary correspondence",
                Scope(All("e", Ch(X("m")), Imp(Bound, Iff(C("IsSide", X("e")), Or(C("IsSide", Lift(X("e"))), Eq(Lift(X("e")), Ear)))))),
                "The reduced boundary lifts precisely to original boundary sides with surviving endpoints together with the forced ear. The two original sides incident to the removed centre are absent."),
            Node("reduce", "Delete the forced ear",
                PlainScope(All("T", Fs(Succ), Eq(C("reduce", X("T")), C("image", C("erase", X("T"), Ear), C("chordDrop"))))),
                "Erase ear(1), keep every other original chord, and relabel its surviving endpoints.", DescribeRole.Definition),
            Node("expand", "Insert the ear triangle",
                PlainScope(All("U", Fs(X("m")), Eq(C("expand", X("U")), C("insert", Ear, C("image", X("U"), C("chordLift")))))),
                "Lift every reduced chord and add exactly the forced ear.", DescribeRole.Definition),
            Node("reduce_isTriangulation", "Deletion preserves full maximality",
                Original(Tri(C("reduce", X("T")))),
                "A diagonal incident to centre 1 crosses the forced ear, so every retained chord avoids that centre. Strict cyclic order preserves crossing. For a missing reduced diagonal, original maximality supplies a crossing chord distinct from the ear, which therefore survives deletion."),
            Node("expand_isTriangulation", "Insertion preserves full maximality",
                Reduced(Tri(C("expand", X("U")))),
                "A missing original internal diagonal either crosses the ear or avoids its centre and descends to a reduced internal diagonal. Reduced maximality then supplies an actual crossing chord. Boundary classification handles the new reduced boundary exactly."),
            Node("expand_reduce", "Recover every original chord",
                Original(Eq(C("expand", C("reduce", X("T"))), X("T"))),
                "The inverse recovers the entire original finite chord set, including the forced ear."),
            Node("reduce_expand", "Recover every reduced chord",
                Reduced(Eq(C("reduce", C("expand", X("U"))), X("U"))),
                "Every internal reduced diagonal lifts to an original diagonal distinct from the ear, and dropping its lift recovers it."),
            Node("earOneEquiv", "Every completion at centre 1",
                Scope(All("h", Bound, AndF(C("hasType", C("earOneEquiv", X("h")), EqType(C("B", Succ, N(1)), C("A", X("m")))), All("T", C("B", Succ, N(1)), Eq(C("val", C("app", C("earOneEquiv", X("h")), X("T"))), C("reduce", C("val", X("T"))))), All("U", C("A", X("m")), Eq(C("val", C("app", C("symm", C("earOneEquiv", X("h"))), X("U"))), C("expand", C("val", X("U")))))))),
                "Deletion and insertion are inverse on the full carriers. The smaller polygon may have five vertices, so the original size may be any size at least six.", DescribeRole.Definition),
            Node("earEquiv", "Arbitrary original ear centre",
                Scope(All("i", V(Succ), All("h", Bound, AndF(C("hasType", C("earEquiv", X("h"), X("i")), EqType(C("B", Succ, X("i")), C("A", X("m")))), All("T", C("B", Succ, X("i")), Eq(C("val", C("app", C("earEquiv", X("h"), X("i")), X("T"))), C("reduce", C("shiftChords", C("val", X("T")), C("sub", N(1), X("i")))))), All("U", C("A", X("m")), Eq(C("val", C("app", C("symm", C("earEquiv", X("h"), X("i"))), X("U"))), C("shiftChords", C("expand", C("val", X("U"))), C("sub", X("i"), N(1))))))))),
                "Translate by 1-i, apply earOneEquiv, and undo the translation on insertion. This constructs the correspondence for every cyclic placement.", DescribeRole.Definition),
            Node("Compatible", "Pairwise compatible original ears",
                All("n", X("Nat"), All("P", C("Finset", V(X("n"))), Iff(C("Compatible", X("P")), All("i", V(X("n")), All("j", V(X("n")), Imp(In(X("i"), X("P")), Imp(In(X("j"), X("P")), Imp(C("ne", X("i"), X("j")), C("notCross", C("ear", X("i")), C("ear", X("j"))))))))))),
                "Distinct selected centres have noncrossing ears. This definition assumes neither a triangulation nor a recursive count.", DescribeRole.Definition),
            Node("reducedCenters", "Relabel all remaining forced centres",
                PlainScope(All("P", C("Finset", V(Succ)), Eq(C("reducedCenters", X("P")), C("image", C("erase", X("P"), N(1)), C("vertexDrop"))))),
                "Erase the selected centre and relabel every other forced centre.", DescribeRole.Definition),
            Node("reduced_centres_card", "Exact number of remaining prescribed centres",
                Scope(All("P", C("Finset", V(Succ)), Imp(R(N(6), Leq, X("m")), Imp(In(N(1), X("P")), Eq(C("card", C("reducedCenters", X("P"))), C("natSub", C("card", X("P")), N(1))))))),
                "Dropping a vertex is injective on the retained centres. Erasing the selected centre therefore decreases the cardinality by exactly one."),
            Node("reduced_centres_compatible", "Compatibility after deletion",
                Scope(All("P", C("Finset", V(Succ)), Imp(R(N(6), Leq, X("m")), Imp(C("Compatible", X("P")), Imp(In(N(1), X("P")), C("Compatible", C("reducedCenters", X("P")))))))),
                "The other compatible forced ears avoid the deleted centre and its two neighbours. Their chords lift to the original ears, so a crossing after deletion would give an original crossing."),
            Node("forcedOneEquiv", "All other forced ears survive",
                Scope(All("P", C("Finset", V(Succ)), All("h", R(N(6), Leq, X("m")), All("g", C("Compatible", X("P")), All("b", In(N(1), X("P")), AndF(C("hasType", C("forcedOneEquiv", X("h"), X("P"), X("g"), X("b")), EqType(C("H", Succ, X("P")), C("H", X("m"), C("reducedCenters", X("P"))))), All("T", C("H", Succ, X("P")), Eq(C("val", C("app", C("forcedOneEquiv", X("h"), X("P"), X("g"), X("b")), X("T"))), C("reduce", C("val", X("T"))))), All("U", C("H", X("m"), C("reducedCenters", X("P"))), Eq(C("val", C("app", C("symm", C("forcedOneEquiv", X("h"), X("P"), X("g"), X("b"))), X("U"))), C("expand", C("val", X("U"))))))))))),
                "Compatibility with ear(1) excludes neighbouring centres 0 and 2. For every other selected centre, all three original vertices survive and the relabelled ear lifts to exactly the original ear. Survival is derived from compatibility.", DescribeRole.Definition),
            Node("forcedEquiv", "Iterated actual deletion",
                NScope(All("P", C("Finset", V(X("n"))), All("h", R(N(6), Leq, C("natSub", X("n"), C("card", X("P")))), All("g", C("Compatible", X("P")), AndF(C("hasType", C("forcedEquiv", X("P"), X("h"), X("g")), EqType(C("H", X("n"), X("P")), C("A", C("natSub", X("n"), C("card", X("P")))))), Eq(C("forcedEquiv", X("P"), X("h"), X("g")), C("choice", C("forcedequivexists", X("n"), X("P"), X("h"), X("g"))))))))),
                "Induction deletes one forced original centre at a time and composes full correspondences. The forced-set cardinality decreases by one. This gives every triangulation of the polygon with n-card(P) vertices, under precisely the displayed remaining-size premise.", DescribeRole.Definition),
            Node("compatible_card_bound", "Compatible centres occupy at most half the boundary",
                NScope(All("P", C("Finset", V(X("n"))), Imp(R(N(6), Leq, X("n")), Imp(C("Compatible", X("P")), R(C("mul", N(2), C("card", X("P"))), Leq, X("n")))))),
                "Adjacent ear centres have crossing ears. A compatible set is disjoint from its translate by one, which has the same cardinality. Their union is contained in the n boundary vertices. For n at least fourteen, deleting a compatible forced set leaves at least seven vertices.")
        ), []));
}
internal static class PolygonEarContractionFormula
{
    internal static Formula X(string n) => F.Id(n);
    internal static Formula N(byte n) => D(n);
    internal static Formula C(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(n))), [.. args]);
    internal static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open,f,Close) : f;
    internal static Formula R(Formula a, Formula op, Formula b) => Seq(Open, Operand(a), Sp, op, Sp, Operand(b), Close);
    internal static Formula Eq(Formula a, Formula b) => R(a, F.Eq, b);
    internal static Formula Iff(Formula a, Formula b) => R(a, F.Iff, b);
    internal static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    internal static Formula AndF(params Formula[] a) { var b=a[^1]; for(int i=a.Length-2;i>=0;i--) b=R(a[i],Land,b); return b; }
    internal static Formula Or(Formula a, Formula b) => R(a, Lor, b);
    internal static Formula In(Formula a, Formula b) => R(a, InMacro, b);
    internal static Formula AddF(Formula a, Formula b) => R(a, Plus, b);
    internal static Formula EqType(Formula a, Formula b) => C("Equiv", a, b);
    internal static Formula V(Formula k) => C("ZMod", k);
    internal static Formula Ch(Formula k) => C("Symtwo", V(k));
    internal static Formula Fs(Formula k) => C("Finset", Ch(k));
    internal static Formula Tri(Formula t) => C("IsTriangulation", t);
    internal static Formula Lift(Formula e) => C("chordLift", e);
    internal static Formula Succ => AddF(X("m"), N(1));
    internal static Formula Ear => C("ear", N(1));
    internal static Formula Bound => R(N(5), Leq, X("m"));
    internal static Formula NScope(Formula body) => All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
    internal static Formula PlainScope(Formula body) => All("m", X("Nat"), body);
    internal static Formula Scope(Formula body) => All("m", X("Nat"), Seq(OpenBracket, C("NeZero", X("m")), CloseBracket, Comma, Sp, body));
    internal static Formula Original(Formula body) => Scope(All("T", Fs(Succ), Imp(Bound, Imp(Tri(X("T")), Imp(In(Ear, X("T")), body)))));
    internal static Formula Reduced(Formula body) => Scope(All("U", Fs(X("m")), Imp(Bound, Imp(Tri(X("U")), body))));
}
