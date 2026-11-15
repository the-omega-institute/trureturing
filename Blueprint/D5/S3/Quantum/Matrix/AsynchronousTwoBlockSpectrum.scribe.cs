using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AsynchronousTwoBlockSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonzero spectrum of the two-block constant-delay history matrix is obtained by taking roots of the rectangular product spectrum.",
        H("Two rectangular blocks with independent history length"),
        Blocks(
            Paragraph(Text("Let U have m rows and n columns, and let V have n rows and m columns. "
                + "The equivalence blockEquiv sends a left sum coordinate to block zero and a right sum coordinate to block one. "
                + "The real matrix zeroDiagonal U V is the reindexing of Matrix.fromBlocks 0 U V 0 along this equivalence. "
                + "Thus it uses exactly the dependent block coordinates of asyncMatrix. "
                + "The delay array has rows (0,b) and (a,0): a is the delay from block one to block zero. "
                + "The history contains every slot from zero through K, independently of a and b.")),
            Describe.Lean(
                DescribeId.Create("nonzero-spectrum"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/AsynchronousTwoBlockSpectrum.nonzero_spectrum_iff"),
                H("The literal history matrix and the rectangular product"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shift rows reconstruct the entire history from its newest slot using inverse powers of a nonzero spectral value. "
                    + "The two update rows then yield a product eigenvector in the first block. "
                    + "Conversely, a product eigenvector lifts to the history by setting its second block to the product of the appropriate inverse power and V applied to the first block. "
                    + "The argument applies to arbitrary rectangular matrices, including empty or singular blocks. "
                    + "It asserts no correspondence at zero and no equality of algebraic multiplicities."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula m=X("m"), n=X("n"), a=X("a"), b=X("b"), k=X("K"), z=X("z");
        Formula u=X("U"), v=X("V");
        Formula delay = Seq(Begin, Grp(F.Id("pmatrix")), D(0), Amp, b, RowBreak, a, Amp, D(0), End, Grp(F.Id("pmatrix")));
        Formula zero = At(Qualified("D5","S3","Quantum","Matrix","AsynchronousTwoBlockSpectrum","zeroDiagonal"),u,v);
        Formula history = At(Qualified("D5","S3","Quantum","Matrix","AsynchronousIterationSpectralRadiusRefutation","asyncMatrix"),zero,delay,k);
        Formula product = new Formula.Binary(u,FormulaBinaryOperator.Multiply,v);
        Formula length=Add(Add(a,b),D(2));
        Formula body = new Formula.Logic(
            Member(z,Spectrum(Complexify(history))), FormulaLogicOperator.Iff,
            Member(new Formula.Power(z,length),Spectrum(Complexify(product))));
        body=Arrow(NotEqual(z,Typed(D(0),Complexes())),body);
        body=All("z",Complexes(),body);
        body=Arrow(LE(b,k),body);
        body=Arrow(LE(a,k),body);
        body=All("V",At(Qualified("Matrix"),FinOf(n),FinOf(m),Reals()),body);
        body=All("U",At(Qualified("Matrix"),FinOf(m),FinOf(n),Reals()),body);
        foreach (var name in new[]{"K","b","a","n","m"}) body=All(name,Naturals(),body);
        return body;
    }
    private static Formula Complexify(Formula matrix) => At(Qualified("Matrix","map"),matrix,
        At(Qualified("DFunLike","coe"),At(Qualified("algebraMap"),Reals(),Complexes())));
    private static Formula Spectrum(Formula matrix) => At(Qualified("spectrum"),Complexes(),matrix);
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
    private static Formula Complexes()=>Seq(Mathbb,Grp(F.Id("C")));
    private static Formula Par(Formula x)=>Seq(Open,x,Close);
    private static Formula Typed(Formula x,Formula t)=>Par(Seq(x,Colon,Sp,t));
    private static Formula All(string name,Formula type,Formula body)=>Seq(Forall,Sp,Typed(X(name),type),Comma,Sp,Par(body));
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(Par(a),Par(b));
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula LE(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula NotEqual(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Member(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
}
