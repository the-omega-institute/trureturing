using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritSixLevelExtremalityDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(Num(-n)) : Num(n);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((p,i) => i == 0 ? new[] {Id(p)} : new[] {Dot,Id(p)}).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Q(s), [..xs]);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Exists,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula And(params Formula[] fs) => Seq(fs.SelectMany((f,i)=> i==0 ? new[] {Parenthesized(f)} : new[] {Land,Sp,Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula a, Formula b) => Seq(a,F.Eq,b);
    private static Formula Smul(Formula a, Formula b) => Call("SMul.smul",a,b);
    private static Formula Add(Formula a, Formula b) => Seq(a,Plus,b);
    private static Formula Prod(Formula a, Formula b) => Parenthesized(Seq(a,Times,Sp,b));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Mat(Formula i, Formula f) => Call("Matrix",i,i,f);
    private static Formula Ps(Formula a) => Seq(Parenthesized(a),Dot,Id("PosSemidef"));
    private static Formula Tr(Formula a) => Seq(Parenthesized(a),Dot,Id("trace"));
    private static Formula Card(Formula s) => Seq(Parenthesized(s),Dot,Id("ncard"));
    private static Formula In(Formula a,Formula s) => Seq(a,InMacro,Sp,s);
    private static Formula States => Seq(OpenBrace,Id("rho"),Mid,Sp,And(Ps(Id("rho")),Eq(Tr(Id("rho")),Int(1)),Call("APPT",Id("rho"))),CloseBrace);
    private static Formula J => Prod(Fin(Int(3)),Fin(Int(3)));
    private static Formula M => Mat(J,C);
    private static Formula PencilLinearity()
    {
        var a=Id("a"); var b=Id("b"); var l=Id("l"); var m=Id("m");
        var vectors=Seq(Fin(Int(9)),To,Sp,R);
        return All("a",R,All("b",R,All("l",vectors,All("m",vectors,
            Eq(Call("K2",Parenthesized(Add(Smul(a,l),Smul(b,m)))),
                Add(Smul(a,Call("K2",l)),Smul(b,Call("K2",m))))))));
    }
    private static DocumentBlock Desc(string name,string title,Formula f,string prose,DescribeRole role=DescribeRole.Theorem,AssessedProvenance? p=null) => Describe.Lean(
        DescribeId.Create(("wcs-QutritSixLevelExtremality-"+name.Replace(".","-").Replace("_","-")).ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSixLevelExtremality."+name.Split('.')[name.Split('.').Length - 1]),H(title),StatementSource.FromAuthor(Disp(f)),
        p ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supporting functional proves extremality of an absolutely PPT two-qutrit state with six spectral levels.",H("Six-level extremality"),Blocks(
        Desc("ConvexKernel.K2_linear","Linearity of the second pencil",PencilLinearity(),
            "The second Hildebrand pencil preserves real linear combinations. The convex-kernel argument and the feasible spectral perturbation use this identity to transport kernel equations."),
        Desc("Extremality.six_level_attainment","Six spectral levels are attained",Ex("rho",M,And(In(Id("rho"),Call("Set.extremePoints",R,States)),Eq(Card(Call("spectrum",C,Id("rho"))),Int(6)))),
            "There exists an extreme absolutely PPT density matrix on two qutrits with exactly six distinct eigenvalues. The diagonal entries of a witness are (318,312,200,169,148,148,130,130,130)/1685. A diagonal supporting functional with weights (-286,-208,-176,128,176,208,242,286,338) forces equality components to coincide."))));
}
