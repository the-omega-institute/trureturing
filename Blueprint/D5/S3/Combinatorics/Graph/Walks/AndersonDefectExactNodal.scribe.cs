using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class AndersonDefectExactNodalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common roots at the designated defect site satisfy the periodic Chebyshev equations and vanish on the strict trace product.",
        H("Common roots and periodic trace constraints"),
        Blocks(
            Paragraph(Text("Let K be a field with an algebra over the real numbers. Let r and m be natural numbers at least three, and let t and mu belong to K, with t transcendental over the real numbers. On Fin(rm), set q=(m-1)r+1 and U(i)=-1 exactly when i modulo r is zero or i=q, and U(i)=1 otherwise. The Hamiltonian H is the ordinary cycle graph Laplacian plus t diag(U). The matrix H^(q) is its actual principal submatrix deleting q; the remaining diagonal entries retain the value 2+tU(i).")),
            Paragraph(Text("Put T(d)=[[d,-1],[1,0]], a=2+t-mu, b=2-t-mu and sigma=trace(T(a)^(r-1)T(b)). The polynomials S_n satisfy S_0=1, S_1=X and S_(n+2)=X S_(n+1)-S_n. Let traceFactors be the product of sigma_r(lambda,t)-2cos(2 pi k/m) over 0<k and 2k<m. The hypotheses say that mu is a common root of the characteristic polynomials of H and H^(q).")),
            Describe.Lean(DescribeId.Create("common-root-trace-constraints"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/AndersonDefectExactNodal.common_root_trace_constraints"),
                H("The two Chebyshev equations"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a symmetric matrix and a singular principal minor, a nonzero kernel vector vanishing at the deleted coordinate is obtained by zero extension and the symmetry of the bilinear pairing. Applied to mu I-H, this gives an actual nodal eigenvector at q.")),
                    Paragraph(Text("The cycle equation transports this vector through the rotated block C=T(a)T(b)T(a)^(r-2). Two consecutive zero coordinates would force the vector to vanish throughout the cycle. Hence its initial nonzero coordinate can be divided out, giving C^m(1,0)=(1,0). The trace of C is sigma.")),
                    Paragraph(Text("Write s=S_(r-2)(a), v=S_(r-3)(a) and h=bs-v. The first column of C is (ah-s,h). If h=0, then (-s)^m=1. Since r is at least three, this makes a algebraic over the real numbers; s and v are then algebraic, and b=v/s is algebraic. The equality t=(a-b)/2 contradicts transcendence. Thus h is nonzero. The two coordinates of the determinant-one Chebyshev power formula now give the displayed equations.")),
                    Paragraph(Text("The first Chebyshev equation places sigma/2 among the real roots of U_(m-1), even when the common root lies in an extension field. The second equation and T_m=X U_(m-1)-U_(m-2) give T_m(sigma/2)=1. The real extremum classification forces an even angular index, while the roots of U_(m-1) exclude both endpoints. Thus sigma=2cos(2 pi k/m) for an index with 0<k and 2k<m, and the strict trace product vanishes at mu.")),
                    Paragraph(Text("The conclusion concerns common-root containment. It does not assert equality of the monic gcd with the periodic trace product, its exact degree, or squarefreeness."))),
                DescribeRole.Theorem))));

    private static Formula Call(string n, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(n))), [..a]);
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, Open, F.Id(n), Sp, Colon, Sp, t, Close, Comma, Sp, b);
    private static Formula Rel(Formula x, FormulaRelationOperator o, Formula y) =>
        new Formula.Relation(x, o, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Statement()
    {
        Formula K=F.Id("K"), R=Seq(Mathbb, Grp(F.Id("R"))), N=Seq(Mathbb, Grp(F.Id("N")));
        Formula r=F.Id("r"), m=F.Id("m"), t=F.Id("t"), mu=F.Id("mu");
        Formula sigma=Call("trace", Call("periodicBlock", r, t, mu));
        Formula equations=And(Equal(Call("eval", Call("S", K, Seq(m, Minus, D(1))), sigma), D(0)),
            Equal(Seq(Call("eval", Call("S", K, Seq(m, Minus, D(2))), sigma), Plus, D(1)), D(0)));
        equations=And(equations, Call("IsRoot", Call("traceFactors", r, m, t), mu));
        Formula result=Imp(Call("IsRoot", Call("charpoly", Call("principalMinor", r, m, t, Call("q", r, m))), mu), equations);
        result=Imp(Call("IsRoot", Call("charpoly", Call("H", r, m, t)), mu), result);
        result=Imp(Call("Transcendental", R, t), result);
        result=All("t", K, All("mu", K, result));
        result=Imp(Rel(D(3), FormulaRelationOperator.LessThanOrEqual, r),
            Imp(Rel(D(3), FormulaRelationOperator.LessThanOrEqual, m), result));
        result=All("r", N, All("m", N, result));
        result=Imp(Call("Field", K), Imp(Call("Algebra", R, K), result));
        return Disp(All("K", F.Id("Type"), result));
    }
}
