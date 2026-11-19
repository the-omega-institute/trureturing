using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AsynchronousUniformOneDelayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit remote delays turn the spectral radius of a real zero-diagonal block matrix into its square root, independently of unused older history slots.",
        H("Unit remote delays with arbitrary history length"),
        Blocks(
            Paragraph(Text("There are ell positive-sized blocks, with ell positive and size n(i) in block i. "
                + "The coordinate type Vtx n is the dependent sum of Fin (n(i)) over i in Fin ell; Sigma.fst extracts the block index. "
                + "N is an arbitrary real matrix on these coordinates. Its entire diagonal blocks vanish: N(p,q)=0 whenever p and q have the same block index. "
                + "No sign, symmetry, rank or irreducibility hypothesis is imposed on the other blocks.")),
            Paragraph(Text("The natural-valued array delta is constant in time and is indexed from source block to destination block. "
                + "Every remote entry is a positive integer at most one, hence equals one. Local entries are unrestricted: their coefficients belong to zero diagonal blocks and cannot affect the update. "
                + "In particular, the convention with every local delay zero is included. "
                + "For any K at least one, asyncMatrix N delta K acts on all slots in Fin (K+1) times Vtx n, with slot zero newest. "
                + "Its newest slot is N applied to slot one, and each older slot copies its immediate predecessor. K is not required to equal one.")),
            Describe.Lean(
                DescribeId.Create("uniform-one-delay-radius"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/AsynchronousUniformOneDelay.whole_uniform_one_delay"),
                H("The exact square-root radius for every admissible history"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here radius is the spectral radius of the complexification of the actual real matrix, valued in the extended nonnegative reals. "
                        + "ENNReal.ofReal embeds the displayed nonnegative real values; Real.sqrt denotes the nonnegative square root. "
                        + "Thus the first conclusion is an exact equality for the actual history matrix, not merely an upper bound or a convergence criterion.")),
                    Paragraph(Text("For a nonzero complex spectral value z of the history matrix, the shift rows force slot s of an eigenvector to be z to the negative s power times its newest slot u. "
                        + "The newest slot cannot vanish, since then every history slot would vanish. "
                        + "The update row gives z u = z inverse times N u, so N u = z squared times u. "
                        + "Conversely, any nonzero eigenvector of N with eigenvalue z squared lifts to the actual history by this same formula for every slot from zero through K. "
                        + "This proves the nonzero spectral correspondence for every K, without discarding the older coordinates.")),
                    Paragraph(Text("Every history spectral value therefore has squared modulus at most lambda. "
                        + "A spectral value of N attaining its positive spectral radius has a complex square root, which lifts to a history spectral value of modulus square root of lambda. "
                        + "The two bounds give equality. Additional zero spectral values have no effect on this positive radius. "
                        + "Since lambda is strictly between zero and one, its square root is also less than one. "
                        + "No assertion about algebraic multiplicities, nonconstant delay schedules, or minimal block counts is made."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula ell=X("ell"), n=X("n"), matrix=X("N"), delta=X("delta"), k=X("K"), lambda=X("lambda");
        Formula blocks=FinOf(ell), coordinates=At(Qualified("D5","S3","Combinatorics","Graph","MultipartiteCHS","Defs","Vtx"),n);
        Formula history=At(Qualified("D5","S3","Quantum","Matrix","AsynchronousIterationSpectralRadiusRefutation","asyncMatrix"),matrix,delta,k);
        Formula sqrt=OfReal(At(Qualified("Real","sqrt"),lambda));
        Formula body=And(Equal(Radius(history),sqrt),Less(sqrt,D(1)));
        body=Arrow(Equal(Radius(matrix),OfReal(lambda)),body);
        body=Arrow(Less(lambda,D(1)),body);
        body=Arrow(Less(D(0),lambda),body);
        body=All("lambda",Reals(),body);
        body=Arrow(LE(D(1),k),body);
        body=All("K",Naturals(),body);
        Formula remote=All("i",blocks,All("j",blocks,
            Arrow(NotEqual(X("i"),X("j")),And(LE(D(1),At(delta,X("i"),X("j"))),LE(At(delta,X("i"),X("j")),D(1))))));
        body=Arrow(remote,body);
        Formula zeroBlocks=All("p",coordinates,All("q",coordinates,
            Arrow(Equal(At(Qualified("Sigma","fst"),X("p")),At(Qualified("Sigma","fst"),X("q"))),
                Equal(At(matrix,X("p"),X("q")),D(0)))));
        body=Arrow(zeroBlocks,body);
        body=All("delta",Arrow(blocks,Arrow(blocks,Naturals())),body);
        body=All("N",At(Qualified("Matrix"),coordinates,coordinates,Reals()),body);
        body=Arrow(All("i",blocks,Less(D(0),At(n,X("i")))),body);
        body=All("n",Arrow(blocks,Naturals()),body);
        body=Arrow(Less(D(0),ell),body);
        return All("ell",Naturals(),body);
    }

    private static Formula X(string name)=>F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items=new System.Collections.Generic.List<Formula>();
        foreach(var part in parts) { if(items.Count>0) items.Add(Dot); items.Add(part switch {
            "D5"=>Seq(F.Id("D"),D(5)), "S3"=>Seq(F.Id("S"),D(3)), _=>F.Id(part)}); }
        return Seq(Operatorname,Grp(Seq([..items])));
    }
    private static Formula At(Formula function,params Formula[] args)=>new Formula.Apply(function,[..args]);
    private static Formula FinOf(Formula n)=>At(Qualified("Fin"),n);
    private static Formula Radius(Formula matrix)=>At(Qualified("D5","S3","Quantum","Matrix","AsynchronousIterationSpectralRadiusRefutation","radius"),matrix);
    private static Formula OfReal(Formula value)=>At(Qualified("ENNReal","ofReal"),value);
    private static Formula Naturals()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Reals()=>Seq(Mathbb,Grp(F.Id("R")));
    private static Formula Par(Formula x)=>Seq(Open,x,Close);
    private static Formula Typed(Formula x,Formula type)=>Par(Seq(x,Colon,Sp,type));
    private static Formula All(string name,Formula type,Formula body)=>Seq(Forall,Sp,Typed(X(name),type),Comma,Sp,Par(body));
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(Par(a),Par(b));
    private static Formula Equal(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula NotEqual(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Less(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula LE(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
}
