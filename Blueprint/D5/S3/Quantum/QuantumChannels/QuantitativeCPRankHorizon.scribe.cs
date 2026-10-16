using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class QuantitativeCPRankHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent compression and density observations for subunital completely positive maps.",
        H("Coherent compression of a positive orbit"),
        Blocks(Describe.Lean(DescribeId.Create("coherent-compression-trace-transfer"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/QuantitativeCPRankHorizon.coherent_compression_trace_transfer"),
            H("The corner defect controls the full orbit"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Matrices act on complex Euclidean space, and the norm is its operator norm. "
                    + "T is an arbitrary completely positive linear map with T(I) at most I. "
                    + "P is an orthogonal projection, X is any matrix at most P, and sigma is a "
                    + "positive matrix of trace one. No invertibility of sigma is required. "
                    + "Write Q=I-P and alpha=sqrt(norm(Q T(P) Q)). The same P determines the "
                    + "corner defect, the orbit comparison and the final observation.")),
                Paragraph(Text("For 0 at most Y at most P, put Z=T(Y). Positivity and subunitality give "
                    + "0 at most Z at most I. Factoring Z through its positive square root bounds "
                    + "norm(Q Z) by alpha, since norm(Q sqrt(Z)) squared equals norm(Q Z Q). "
                    + "The adjoint gives the same bound for Z Q. The identity "
                    + "Z-P Z P=Q Z+P Z Q therefore bounds the full coherent defect by 2 alpha, "
                    + "including both off-diagonal blocks.")),
                Paragraph(Text("Applying this estimate to Y=P gives T(P) at most P+2 alpha I. "
                    + "Induction using positivity of T and T(I) at most I gives "
                    + "T^n(X) at most P+2 n alpha I. "
                    + "Tracing against sigma proves the observation estimate. The result includes "
                    + "n=0, P=0, P=I and zero maps. It does not choose a spectral cutoff or "
                    + "infer the corner defect from a short-word frame."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Statement()
    {
        Formula d=F.Id("d"), t=F.Id("T"), p=F.Id("P"), x=F.Id("X"), s=F.Id("sigma"), n=F.Id("n");
        var nat=Seq(Mathbb, Grp(F.Id("N")));
        var mat=Call("ComplexEuclideanMatrix", d);
        var q=Seq(Open, Num(1), Minus, p, Close);
        var alpha=Call("sqrt",new Formula.Norm(Mul(Mul(q,Call("apply",t,p)),q)));
        var error=Mul(Mul(Num(2),n),alpha);
        var orbit=Call("iterate",t,n,x);
        var hypotheses=And(Le(Call("apply",t,Num(1)),Num(1)),
            And(Call("IsStarProjection",p),
                And(Le(x,p),And(Le(Num(0),s),Eq(Call("trace",s),Num(1))))));
        var conclusion=And(Le(orbit,Add(p,Call("smul",error,Num(1)))),
            Le(Call("re",Call("trace",Mul(s,orbit))),
                Add(Call("re",Call("trace",Mul(s,p))),error)));
        return Disp(All("d",nat,All("T",Call("CompletelyPositiveMap",mat,mat),
            All("P",mat,All("X",mat,All("sigma",mat,
                Imp(hypotheses,All("n",nat,conclusion))))))));
    }

}
