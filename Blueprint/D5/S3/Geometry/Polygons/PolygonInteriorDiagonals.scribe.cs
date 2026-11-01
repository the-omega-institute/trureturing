using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;
internal sealed class PolygonInteriorDiagonalsDocument : IScribeDocumentDefinition
{
    private static Formula X(string n) => F.Id(n);
    private static Formula C(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(n))), [.. args]);
    private static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula R(Formula a, Formula op, Formula b) => Seq(Open, a, Sp, op, Sp, b, Close);
    private static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    private static Formula V(Formula i) => C("vertex", X("p"), i);
    private static Formula Statement()
    {
        Formula body = R(C("IsDiagonal", C("pair", X("i"), X("j"))), Iff,
            R(R(V(X("i")), Neq, V(X("j"))), Land,
                R(C("openSegment", X("Real"), V(X("i")), V(X("j"))), Subset,
                    C("interior", C("hull", X("p"))))));
        body = All("i", C("ZMod", X("n")), All("j", C("ZMod", X("n")), body));
        body = Imp(C("BoundaryModel", X("p")), body);
        body = All("p", C("Polygon", X("E"), X("n")), body);
        body = Imp(R(D(3), Leq, X("n")), body);
        body = Imp(R(C("finrank", X("Real"), X("E")), F.Eq, D(2)), body);
        body = All("n", X("Nat"), Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
        return All("E", X("Type"), Seq(
            OpenBracket, C("NormedAddCommGroup", X("E")), CloseBracket, Sp,
            OpenBracket, C("NormedSpace", X("Real"), X("E")), CloseBracket, Comma, Sp, body));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interior diagonals from an actual polygon boundary", H("Extreme vertices and the filled hull"), Blocks(
            Paragraph(Text("Let E be a real normed vector space of real dimension two and let p be a Polygon E n with n at least three. Put hull(p)=convexHull over the reals of the range of p.vertices. BoundaryModel(p) states precisely that the vertices are injective, every vertex is an extreme point of hull(p), and p.boundary over the reals equals the topological frontier of hull(p). The native boundary is the union of p.edgeSet over Fin(n); each edge joins p(k) to p(finRotate n k). The vertex map on ZMod(n) is p composed with the inverse of ZMod.finEquiv n. The notation pair(i,j) denotes the unordered pair s(i,j). IsDiagonal is the existing native predicate: distinct endpoints and absence from the cyclic successor sides.")),
            Describe.Lean(DescribeId.Create("polygon-interior-diagonals"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonInteriorDiagonals.isDiagonal_iff_openSegment_subset_interior"),
                H("Every native diagonal and only those diagonals"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Three distinct extreme vertices cannot be collinear: one would lie between the other two and extremality would make it an endpoint. Such a triple spans the plane, so the finite convex hull has nonempty interior. The affine-span and interior implications use the corresponding Mathlib results directly.")),
                    Paragraph(Text("Suppose two distinct listed vertices maximize one nonzero continuous linear functional. Their midpoint belongs to the hull and cannot be interior: a nonzero functional maps every open neighborhood to an open interval, whereas the hull stays below its maximum. Boundary coverage puts that midpoint on an actual cyclic edge. It cannot be an edge endpoint by extremality. Both edge endpoints therefore attain the same maximum. Three distinct listed vertices on this level would span the plane and force the functional to be constant and hence zero. The two endpoint pairs coincide, proving actual successor adjacency.")),
                    Paragraph(Text("Now take any point of the open chord of a native diagonal. Convexity puts it in the hull. If it were not interior, the nonempty-interior supporting-functional theorem would supply a nonzero functional maximizing there; both chord endpoints would maximize it. The preceding adjacency conclusion contradicts the diagonal predicate. Conversely, a cyclic side lies on the frontier and its midpoint cannot lie in the interior. The explicit distinctness conjunct excludes loops, including the convention that an open segment from a point to itself contains that point. Both successor orientations and the cyclic seam are included.")),
                    Paragraph(Text("This result assumes the explicit extreme-vertex boundary model. It requires no strict convexity of the filled set, regularity, metric angle data, alternation condition or orientation theorem. It does not identify a simple polygon with no reflex angles with this model, establish the alternating-arc or proper-crossing characterization, or transport whole triangulations, maximality, complete ears, families, witnesses or completion counts. Those geometric correspondences require further theorems."))
                ))
        ), []));
}
