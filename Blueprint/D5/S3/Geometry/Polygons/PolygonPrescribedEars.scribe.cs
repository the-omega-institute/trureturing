using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonPrescribedEarsFormula;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;
internal sealed class PolygonPrescribedEarsDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        Formula body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("T"),
            Fs(X("n")), AndF(Tri(X("T")), Eq(C("EarCenters", X("T")), X("P"))));
        body = Imp(R(N(6), Leq, C("natSub", X("n"), C("card", X("P")))), body);
        body = Imp(R(N(3), Leq, C("card", X("P"))), body);
        body = Imp(C("Compatible", X("P")), body);
        body = All("P", C("Finset", V(X("n"))), body);
        return NScope(Imp(R(D(1,4), Leq, X("n")), body));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prescribed complete ears of a cyclic triangulation", H("Exact native realization"), Blocks(
            Paragraph(Text("The vertices are ZMod(n), chords are unordered pairs Sym2(ZMod(n)), and a triangulation is a finite set of internal diagonals that is pairwise noncrossing and maximal: each missing internal diagonal crosses a member. EarCenters(T) is the complete set of i for which the chord joining i-1 to i+1 belongs to T. Compatible(P) means that the distinct prescribed ear chords do not cross. V(n)=ZMod(n), F(n)=Finset(Sym2(V(n))), and natSub is natural subtraction.")),
            Describe.Lean(DescribeId.Create("polygon-prescribed-complete-ears"),
                DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonPrescribedEars.prescribed_complete_ears"),
                H("Every compatible prescribed complete ear set"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Rotate one prescribed centre to 1. For two prescribed nonadjacent centres 1 and k+1, use the integer interval double fan with chords (0,j), 2<=j<=k, and (k,j), k+2<=j<=n-1. The two sets do not interleave. Every missing diagonal interleaves one of these chords, so their union is maximal. Its only ear centres are 1 and k+1, including the cyclic seam case k=n-2. The interval-to-cyclic triangulation bijection transports this construction to the native chord carrier.")),
                    Paragraph(Text("For more prescribed centres, delete one prescribed ear and relabel the others through forcedOneEquiv. Their cardinality decreases by one and they remain compatible. Apply the construction recursively while the number of remaining vertices minus the number of prescribed centres stays at least six. Inserting the ear gives every prescribed original ear. Applying the same deletion map to the entire ear set of the inserted triangulation bounds its cardinality by that of P; containment therefore gives equality. Undoing the rotation restores the original labels.")),
                    Paragraph(Text("For a path trace P=M_i union {x} contained in the six-ear set D and disjoint from another matching M_j, this triangulation has no ear in common with a triangulation V whose exact D trace is M_j. Indeed EarCenters(T)=P is contained in D, so its intersection with EarCenters(V) is P intersect M_j, which is empty. If V lies in an intersecting family, T is absent from that same family and the whole exact path-trace fibre is not filled. Together with the strict complementary-pair bound, the two path pairs give t_i<=2w3-2 and path loss at least two per group. Uniform omitted-capacity bounds and the final strong twenty-vertex estimate require separate inputs. The construction assumes only cyclic labels and does not assert an affine or Euclidean realization."))
                ))
        ), []));
}

internal static class PolygonPrescribedEarsFormula
{
    internal static Formula X(string n) => F.Id(n);
    internal static Formula N(byte n) => D(n);
    internal static Formula C(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(n))), [.. args]);
    internal static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open, f, Close) : f;
    internal static Formula R(Formula a, Formula op, Formula b) =>
        Seq(Open, Operand(a), Sp, op, Sp, Operand(b), Close);
    internal static Formula Eq(Formula a, Formula b) => R(a, F.Eq, b);
    internal static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    internal static Formula AndF(Formula a, Formula b) => R(a, Land, b);
    internal static Formula V(Formula n) => C("ZMod", n);
    internal static Formula Fs(Formula n) => C("Finset", C("Symtwo", V(n)));
    internal static Formula Tri(Formula t) => C("IsTriangulation", t);
    internal static Formula NScope(Formula body) => All("n", X("Nat"),
        Seq(OpenBracket, C("NeZero", X("n")), CloseBracket, Comma, Sp, body));
}
