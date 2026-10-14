using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritSpectralFeasiblePerturbationDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(Num(-n)) : Num(n);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((p,i) => i == 0 ? new[] {Id(p)} : new[] {Dot,Id(p)}).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Q(s), [..xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [..xs]);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Exists,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula And(params Formula[] fs) => Seq(fs.SelectMany((f,i)=> i==0 ? new[] {Parenthesized(f)} : new[] {Land,Sp,Parenthesized(f)}).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a),Rightarrow,Sp,Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a,F.Eq,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,Sp,b);
    private static Formula Lt(Formula a, Formula b) => Seq(a,F.Lt,b);
    private static Formula Ne(Formula a, Formula b) => Seq(a,Neq,Sp,b);
    private static Formula Arr(Formula a, Formula b) => Seq(a,To,Sp,b);
    private static Formula Add(Formula a, Formula b) => Seq(a,Plus,b);
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Ps(Formula a) => Seq(Parenthesized(a),Dot,Id("PosSemidef"));
    private static Formula Sum(string s, Formula t, Formula b) => Seq(new Formula.Subscript(F.Sum,Seq(Id(s),Colon,t)),Sp,b);
    private static Formula Range(Formula l) => Call("Set.range",l);
    private static Formula Card(Formula s) => Seq(Parenthesized(s),Dot,Id("ncard"));
    private static Formula L => Arr(Fin(Int(9)),R);
    private static DocumentBlock Desc(string name,string title,Formula f,string prose,DescribeRole role=DescribeRole.Theorem,AssessedProvenance? p=null) => Describe.Lean(
        DescribeId.Create(("wcs-QutritSpectralFeasiblePerturbation-"+name.Replace(".","-").Replace("_","-")).ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralFeasiblePerturbation."+name.Split('.')[name.Split('.').Length - 1]),H(title),StatementSource.FromAuthor(Disp(f)),
        p ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);


    private static Formula RadiusStatement()
    {
        var l=Id("l");var v=Id("v");var r=Id("r");var t=Id("t");var i=Id("i");
        var shifted=Add(l,Call("HSMul.hSMul",t,v));
        var after=And(Call("Antitone",shifted),All("i",Fin(Int(9)),Le(Int(0),App(Parenthesized(shifted),i))),
            Eq(Sum("i",Fin(Int(9)),App(Parenthesized(shifted),i)),Int(1)),Ps(Call("K1",shifted)),Ps(Call("K2",shifted)));
        var radius=Ex("r",R,And(Lt(Int(0),r),All("t",R,Imp(Lt(Call("abs",t),r),after))));
        var direction=Ex("v",L,And(Ne(v,Int(0)),radius));
        var before=And(Call("Antitone",l),All("i",Fin(Int(9)),Le(Int(0),App(l,i))),
            Eq(Sum("i",Fin(Int(9)),App(l,i)),Int(1)),Ps(Call("K1",l)),Ps(Call("K2",l)),Le(Int(7),Card(Range(l))));
        return All("l",L,Imp(before,direction));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven spectral levels admit a nonzero trace-zero perturbation preserving both positive pencils for a positive radius.",H("Feasible spectral perturbation"),Blocks(
        Desc("FeasiblePerturbation.spectral_radius","A positive feasible radius",RadiusStatement(),
            "Seven distinct levels give a nonzero block-preserving trace-zero direction. The dependency between the two pencil kernel equations leaves at most six independent constraints. Positive leading minors and continuity give a radius preserving positive semidefiniteness, order, nonnegativity, and mass."))));
}
