using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class OriginalDataSymplecticSplitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive Hamiltonian with a closed surjective observation map determines complementary symplectic subspaces through the original energy lift.",
        H("The original observation lift and its symplectic complement"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-data-symplectic-retract"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/OriginalDataSymplecticSplit.original_data_symplectic_retract"),
            H("The positive lift, its inverse, and the two restricted forms"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let E be the real functions on Fin n plus Fin n and F the real functions on Fin r. The canonical matrix J is [[0,I],[-I,0]], the negative of Mathlib's Matrix.J. Let S be positive definite, O map E onto F, and O(JS)=KO. Set P=OS-inverse O-transpose, L=S-inverse O-transpose P-inverse, U=range L, V=ker O, and w(x,y)=x-transpose J y. In the displayed formula these definitions are bound by equalities; they are not additional independent assumptions.")),
                Paragraph(Text("Surjectivity of O makes its transpose injective. Positive congruence therefore makes P positive definite and OL=I. Restricting O to U gives a linear equivalence whose inverse is exactly L. Every vector z decomposes as LOz plus z-LOz. The two summands lie in U and V respectively, and their intersection is zero. The identity L-transpose S=P-inverse O gives energy orthogonality.")),
                Paragraph(Text("The kernel V is invariant under A=JS by the observation closure. If x in V lies in the radical of the restricted symplectic form, test it against Ax, which is again in V. The resulting equality w(x,Ax)=-x-transpose S x contradicts positive energy unless x=0. Thus the restriction to V is nondegenerate. Since A is injective, its restriction to finite-dimensional V is surjective. Expressing v in V as Az shows that w(u,v)=-u-transpose S z vanishes for u in U. Complement dimensions identify U with the symplectic orthogonal of V; taking the orthogonal again gives exactly V as the orthogonal of U. The existing restriction criterion then gives nondegeneracy on U.")),
                Paragraph(Text("Both alternating forms and both positive energy forms restrict to these same subspaces. The existing finite-dimensional Darboux theorem supplies bases b and c on U and V. Their cardinalities give r=2k and n=k+h. No nonempty index or positive dimension is required: r=0, r=2n, and the zero ambient space remain included.")),
                Paragraph(Text("Surjectivity of A and O makes K surjective, hence invertible. The identity KP=OJO-transpose then proves invertibility of the reduced skew matrix. The symplectic orthogonal characterization and energy orthogonality make U invariant under A; applying the inverse observation on U gives AL=LK for the original lift.")),
                Paragraph(Text("These bases belong to the original range L and kernel O. Constructing their ambient coordinate maps, the global position-momentum permutation, and a common final map for the two Williamson congruences requires further coordinate identities. The present statement asserts the retract and the two bases; it does not assert that complete coordinate normal form."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var n = V("n"); var r = V("r"); var s = V("S"); var o = V("O");
        var k = V("K"); var j = V("J"); var p = V("P"); var l = V("L");
        var u = V("U"); var v = V("V"); var w = V("w");
        var ambient = Vectors(Modes(n)); var visible = Vectors(Call("Fin", r));
        var wu = Call("restrict", w, u); var wv = Call("restrict", w, v);
        var inverse = Ex(V("e"), Call("LinearEquiv", Real, u, visible), And(
            All(V("x"), u, Equal(Call("e", V("x")), Call("mulVec", o, Call("val", V("x"))))),
            All(V("y"), visible, Equal(Call("val", Call("symmApply", V("e"), V("y"))),
                Call("mulVec", l, V("y"))))));
        var bases = Ex(V("k"), Nat, Ex(V("h"), Nat,
            Ex(V("b"), Call("Basis", Modes(V("k")), Real, u),
            Ex(V("c"), Call("Basis", Modes(V("h")), Real, v), And(
                Call("IsSymplecticBasis", wu, V("b")),
                Call("IsSymplecticBasis", wv, V("c")),
                Equal(r, Multiply(D(2), V("k"))),
                Equal(n, Seq(V("k"), Sp, Plus, Sp, V("h"))))))));
        var conclusion = And(
            Call("PosDef", p), Equal(Multiply(o, l), D(1)), inverse,
            Call("IsCompl", u, v), Equal(Call("orthogonal", w, u), v),
            Call("IsAlt", wu), Call("IsAlt", wv),
            Call("Nondegenerate", wu), Call("Nondegenerate", wv),
            All(V("x"), u, All(V("y"), v, Equal(
                Call("pair", s, Call("val", V("x")), Call("val", V("y"))), D(0)))),
            Call("PosDef", Call("toQuadraticMap", Call("restrict", Call("toBilin", s), u))),
            Call("PosDef", Call("toQuadraticMap", Call("restrict", Call("toBilin", s), v))),
            Equal(Call("finrank", Real, u), r),
            Equal(Seq(Call("finrank", Real, u), Sp, Plus, Sp, Call("finrank", Real, v)),
                Multiply(D(2), n)), Call("IsUnit", k),
            Call("IsUnit", Multiply(Multiply(o, j), Call("transpose", o))),
            Equal(Multiply(Multiply(j, s), l), Multiply(l, k)), bases);
        var assumptions = And(
            Equal(j, Seq(Minus, Call("MatrixJ", Call("Fin", n), Real))),
            Equal(p, Multiply(Multiply(o, Call("inv", s)), Call("transpose", o))),
            Equal(l, Multiply(Multiply(Call("inv", s), Call("transpose", o)), Call("inv", p))),
            Equal(u, Call("range", Call("mulVecLin", l))),
            Equal(v, Call("ker", Call("mulVecLin", o))),
            Equal(w, Call("toBilin", j)), Call("PosDef", s),
            Call("Surjective", Call("mulVec", o)),
            Equal(Multiply(o, Multiply(j, s)), Multiply(k, o)));
        var body = Seq(Paren(assumptions), Sp, Rightarrow, Sp, Paren(conclusion));
        body = All(w, Call("BilinForm", Real, ambient), body);
        body = All(u, Call("Submodule", Real, ambient), All(v, Call("Submodule", Real, ambient), body));
        body = All(l, Matrix(Modes(n), Call("Fin", r)), body);
        body = All(p, Matrix(Call("Fin", r), Call("Fin", r)), body);
        body = All(j, Matrix(Modes(n), Modes(n)), body);
        body = All(k, Matrix(Call("Fin", r), Call("Fin", r)), body);
        body = All(o, Matrix(Call("Fin", r), Modes(n)), body);
        body = All(s, Matrix(Modes(n), Modes(n)), body);
        return All(n, Nat, All(r, Nat, body));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Modes(Formula n) => Call("Sum", Call("Fin", n), Call("Fin", n));
    private static Formula Vectors(Formula i) => Paren(Seq(i, Sp, To, Sp, Real));
    private static Formula Matrix(Formula i, Formula j) => Call("Matrix", i, j, Real);
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Paren(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Paren(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(params Formula[] terms) => Seq(
        [.. terms.SelectMany((term, i) => i == 0
            ? new[] { Paren(term) } : new[] { Sp, Land, Sp, Paren(term) })]);
}
