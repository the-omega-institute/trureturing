using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class PartialTransposeTraceDocument : IScribeDocumentDefinition
{
    private static Formula X(string n) => F.Id(n);
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(X(n), [.. xs]);
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp, Par(Seq(X(n), Colon, t)), Comma, Sp, f);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Product(Formula a, Formula b) => Par(Seq(a, Times, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Statement()
    {
        var a=X("A"); var b=X("B"); var j=Product(a,b); var m=X("M"); var v=X("v");
        var left=Call("dotProduct",Call("star",v),Call("mulVec",Call("partialTranspose",m),v));
        var right=Call("trace",Call("mul",m,Call("partialTranspose",Call("vecMulVec",v,Call("star",v)))));
        return All("A",X("Type"),All("B",X("Type"),
            All("instA",Call("Fintype",a),All("instB",Call("Fintype",b),
                All("M",Call("Matrix",j,j,C),All("v",Arrow(j,C),Eqn(left,right)))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial transpose is self-adjoint for trace pairing on arbitrary finite product index types.",
        H("Partial-transpose trace duality"), Blocks(
            Describe.Lean(DescribeId.Create("partial-transpose-trace-duality"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/PartialTransposeTrace.partial_transpose_trace_duality"),
                H("Quadratic testing and trace pairing"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let A and B be arbitrary types with their given Fintype instances, M any complex matrix on A × B and v any complex vector on A × B. With second-factor partial transpose Gamma(M)[(a,b),(c,d)]=M[(a,d),(c,b)], star(v) dot (Gamma(M) v) equals tr(M Gamma(v star(v))). The displayed instA and instB binders are the two finite-type instances. The local cardinalities may differ and may be zero. No Hermiticity, positivity, trace-one condition, APPT hypothesis or normalization of v is assumed. Finite trace expansion and interchange of the two second-factor indices prove trace self-adjointness; the standard outer-product trace identity gives the vector formula. This is the standard trace-pairing identity in the repository's product-index convention, rather than a new physical criterion. It is consumed by the uniform rank-four necessary inequality, whose swap test uses a genuine four-by-four local product corner."))),
                DescribeRole.Theorem))));
}
