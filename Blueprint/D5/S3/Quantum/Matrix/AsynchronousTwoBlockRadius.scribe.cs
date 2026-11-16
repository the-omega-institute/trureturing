using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AsynchronousTwoBlockRadiusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact spectral radius of a two-block zero-diagonal history operator depends on the sum of its two remote delays.",
        H("The two-block delay radius and the original power bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-block-radius"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/AsynchronousTwoBlockRadius.two_block_radius"),
                H("Exact radius for every sufficiently long history"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The block sizes m and n are positive. The real rectangular matrices U and V are arbitrary. "
                    + "The matrix zeroDiagonal U V is the explicit reindexing of Matrix.fromBlocks 0 U V 0 into the dependent block coordinates. "
                    + "The delay array has rows (0,b) and (a,0), with each remote delay between one and k. "
                    + "The history length K independently bounds both delays and includes all slots from zero through K.")),
                    Paragraph(Text("The nonzero spectrum correspondence is used in both directions. "
                    + "Its zero-delay, one-slot specialization identifies the synchronous spectrum with the square roots of the product spectrum. "
                    + "For the upper bound, a delayed spectral value gives a product spectral value and then a synchronous spectral value. "
                    + "For equality, a synchronous spectral value of maximal modulus gives a product value whose complex roots lift back to the actual delayed matrix. "
                    + "No positive real eigenvalue, sign condition, rank condition, or equality of the two block sizes is required."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula a=X("a"), b=X("b"), k=X("k"), h=X("K"), u=X("U"), v=X("V"), lambda=X("lambda");
        Formula zero=At(Qualified("D5","S3","Quantum","Matrix","AsynchronousTwoBlockSpectrum","zeroDiagonal"),u,v);
        Formula delay=Seq(Begin,Grp(F.Id("pmatrix")),D(0),Amp,b,RowBreak,a,Amp,D(0),End,Grp(F.Id("pmatrix")));
        Formula history=At(Qualified("D5","S3","Quantum","Matrix","AsynchronousIterationSpectralRadiusRefutation","asyncMatrix"),zero,delay,h);
        Formula length=Typed(At(Qualified("Nat","cast"),Add(Add(a,b),D(2))),Reals());
        Formula realK=Typed(At(Qualified("Nat","cast"),k),Reals());
        Formula r=OfReal(new Formula.Power(lambda,new Formula.Fraction(Typed(D(2),Reals()),length)));
        Formula bound=OfReal(new Formula.Power(lambda,new Formula.Fraction(Typed(D(1),Reals()),Add(realK,Typed(D(1),Reals())))));
        Formula body=And(Equal(Radius(history),r),And(LE(r,bound),Less(bound,D(1))));
        body=Arrow(Equal(Radius(zero),OfReal(lambda)),body);
        body=Arrow(Less(lambda,D(1)),body);
        body=Arrow(Less(D(0),lambda),body);
        body=All("lambda",Reals(),body);
        foreach(var condition in new[]{LE(b,h),LE(a,h),LE(b,k),LE(a,k),LE(D(1),b),LE(D(1),a)}) body=Arrow(condition,body);
        body=All("V",At(Qualified("Matrix"),FinOf(X("n")),FinOf(X("m")),Reals()),body);
        body=All("U",At(Qualified("Matrix"),FinOf(X("m")),FinOf(X("n")),Reals()),body);
        body=Arrow(Less(D(0),X("n")),body);
        body=Arrow(Less(D(0),X("m")),body);
        foreach(var name in new[]{"K","k","b","a","n","m"}) body=All(name,Naturals(),body);
        return body;
    }
    private static Formula Radius(Formula x)=>At(Qualified("D5","S3","Quantum","Matrix","AsynchronousIterationSpectralRadiusRefutation","radius"),x);
    private static Formula OfReal(Formula x)=>At(Qualified("ENNReal","ofReal"),x);
    private static Formula Equal(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Less(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula X(string name)=>F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items=new System.Collections.Generic.List<Formula>();
        foreach(var part in parts) { if(items.Count>0) items.Add(Dot); items.Add(part switch {
            "D5"=>Seq(F.Id("D"),D(5)), "S3"=>Seq(F.Id("S"),D(3)), _=>F.Id(part)}); }
        return Seq(Operatorname,Grp(Seq([..items])));
    }
    private static Formula At(Formula function, params Formula[] args)=>new Formula.Apply(function,[..args]);
    private static Formula FinOf(Formula n)=>At(Qualified("Fin"),n);
    private static Formula Naturals()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Reals()=>Seq(Mathbb,Grp(F.Id("R")));
    private static Formula Par(Formula x)=>Seq(Open,x,Close);
    private static Formula Typed(Formula x,Formula t)=>Par(Seq(x,Colon,Sp,t));
    private static Formula All(string name,Formula type,Formula body)=>Seq(Forall,Sp,Typed(X(name),type),Comma,Sp,Par(body));
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(Par(a),Par(b));
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula LE(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
}
