using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class GeneralizedChoiNonDetectionDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);


    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula J => Prod(Fin(Int(3)),Fin(Int(3)));
    private static Formula M => Matrix(J,J,C);
    private static Formula T => Matrix(Fin(Int(3)),Fin(Int(3)),C);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Sub(Formula x, Formula y) => Parenthesized(Seq(x,Minus,y));
    private static Formula Arrow(Formula x, Formula y) => Seq(x,To,Sp,y);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x,Comma,y));
    private static Formula StarOf(Formula x) => Call("star",x);
    private static Formula Smul(Formula x, Formula y) => Call("SMul.smul",x,y);
    private static Formula OfReal(Formula x) => Call("Complex.ofReal",x);
    private static Formula Sum(string x, Formula ty, Formula f) => Seq(new Formula.Subscript(F.Sum,Seq(Id(x),Colon,ty)),Sp,f);
    private static Formula b => Id("b");
    private static Formula c => Id("c");
    private static Formula v => Id("v");
    private static Formula X => Id("X");
    private static Formula Phi => Id("Phi");
    private static Formula rho => Id("rho");
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/QuantumStates/arunachalam2015absolute");
    private static Formula Entry(int i,int j) => Call("X",Int(i),Int(j));
    private static Formula Negative(Formula x) => Parenthesized(new Formula.Negate(x));
    private static Formula ChoiDefinition()
    {
        var a=OfReal(Sub(Sub(Int(2),b),c));
        var bc=OfReal(b); var cc=OfReal(c);
        var diagonalFirst=Add(Mul(a,Entry(0,0)),Mul(bc,Entry(1,1)),Mul(cc,Entry(2,2)));
        var diagonalSecond=Add(Mul(cc,Entry(0,0)),Mul(a,Entry(1,1)),Mul(bc,Entry(2,2)));
        var diagonalThird=Add(Mul(bc,Entry(0,0)),Mul(cc,Entry(1,1)),Mul(a,Entry(2,2)));
        var entries=Seq(Begin,Grp(Id("bmatrix")),diagonalFirst,Amp,Negative(Entry(0,1)),Amp,Negative(Entry(0,2)),RowBreak,
            Negative(Entry(1,0)),Amp,diagonalSecond,Amp,Negative(Entry(1,2)),RowBreak,
            Negative(Entry(2,0)),Amp,Negative(Entry(2,1)),Amp,diagonalThird,End,Grp(Id("bmatrix")));
        return All("b",R,All("c",R,All("X",T,Eq(Call("choiGen",b,c,X),Smul(Frac(Int(1),Int(2)),entries)))));
    }
    private static Formula TensorDefinition()
    {
        var i=Id("i"); var j=Id("j"); var k=Id("k"); var l=Id("l");
        var block=Parenthesized(Seq(Id("fun"),Sp,Id("s"),Sp,Id("t"),Sp,Mapsto,Sp,
            Call("rho",Pair(i,Id("s")),Pair(j,Id("t")))));
        var rhs=new Formula.Apply(new Formula.Apply(Phi,[block]),[k,l]);
        var lhs=new Formula.Apply(Call("idTensor",Phi,rho),[Pair(i,k),Pair(j,l)]);
        return All("Phi",Arrow(T,T),All("rho",M,All("i",Fin(Int(3)),All("k",Fin(Int(3)),
            All("j",Fin(Int(3)),All("l",Fin(Int(3)),Eq(lhs,rhs)))))));
    }
    private static Formula ClaimStatement()
    {
        var notOrigin=Seq(Pair(b,c),Neq,Sp,Pair(Int(0),Int(0)));
        var region=Seq(Parenthesized(Le(Add(b,c),Int(1))),Lor,Sp,
            Parenthesized(Le(Pow(Sub(Add(b,c),Int(1)),2),Mul(b,c))));
        var output=PSInt(Call("idTensor",Call("choiGen",b,c),rho));
        return All("b",R,All("c",R,Imp(Le(Int(0),b),Imp(Le(Int(0),c),Imp(notOrigin,Imp(region,
            All("rho",M,Imp(PSInt(rho),Imp(Eq(Trace(rho),Int(1)),Imp(Call("APPT",rho),output))))))))));
    }
    private static Formula WitnessBound()
    {
        var q=Add(Pow(Sub(Sub(Int(2),b),c),2),Pow(b,2),Pow(c,2));
        var w=Call("idTensor",Call("choiGen",c,b),Call("Matrix.vecMulVec",v,StarOf(v)));
        return All("b",R,All("c",R,Imp(Le(q,Int(2)),All("v",Arrow(J,C),
            Le(Call("Complex.re",Trace(Mul(w,w))),Frac(Pow(Sum("i",J,Call("Complex.normSq",Call("v",Id("i")))),2),Int(2)))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generalized Choi maps preserve positivity on absolutely PPT qutrit density matrices.",
        H("Generalized Choi maps and absolute PPT"),Blocks(
            Desc("GeneralizedChoiNonDetection","choiGen","The generalized Choi map",ChoiDefinition(),
                "Arunachalam–Johnston–Russo, Section 5.3, page 14. The coefficient a is 2-b-c. Indices are zero-based; the displayed entry at (0,0) is the source entry at (1,1). The scalar one-half is real and acts on the complex matrix.",provenance:AssessedProvenance.FromLiterature(Source)),
            Desc("GeneralizedChoiNonDetection","idTensor","Action on the second tensor factor",TensorDefinition(),
                "The map acts on every three-by-three block. The second tensor factor carries Phi, matching the second-factor partial transpose in APPT.",provenance:AssessedProvenance.FromLiterature(Source)),
            Desc("GeneralizedChoiNonDetection","claim","Non-detection for the full parameter region",Seq(Id("claim"),Iff,Sp,ClaimStatement()),
                "Arunachalam–Johnston–Russo, Section 7, page 21, asks whether every generalized Choi map in the stated region is incapable of detecting absolutely PPT entanglement. APPT is the literal predicate of QutritPerturbationAttainment; density positivity and trace normalization are separate hypotheses.",provenance:AssessedProvenance.FromLiterature(Source)),
            Desc("GeneralizedChoiNonDetection","witness_purity_bound","Homogeneous quadratic estimate",WitnessBound(),
                "For a vector of arbitrary length, the adjoint image of its rank-one matrix has real trace-square at most half the squared total component mass whenever the parameter square-sum is at most two. A Gram-matrix purity estimate and the sum of three squared column masses give the bound.",DescribeRole.Theorem),
            Desc("GeneralizedChoiNonDetection","result","Non-detection on absolutely PPT states",Id("claim"),
                "The adjoint quadratic estimate combines with the qutrit APPT purity bound 17/121 and centered Frobenius Cauchy–Schwarz. In the triangle b+c≤1 the map is a positive combination of the two boundary maps and a diagonal conjugation map.",DescribeRole.Theorem,AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("arunachalam-johnston-russo-2015-generalized-choi-absolutely-ppt"),ResolutionKind.Proved)))));
}
