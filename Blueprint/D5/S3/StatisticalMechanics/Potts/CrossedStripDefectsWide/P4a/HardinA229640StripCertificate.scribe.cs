using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a;
internal sealed class HardinA229640StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripCertificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-row two-defect HDA strips.",H("HardinA229640StripCertificate"),Blocks(
            Paragraph(Text("The one-defect successor counts and continuation powers retain their original values. Exactly two monochromatic bonds define the additional transition entries. The full continuation vector satisfies the cube of the proper-colouring sextic after three transitions. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.")),
            Node("finite_certificate",Certificate(),true))));
    private static DocumentBlock Node(string name,Formula formula,bool theorem) => Describe.Lean(
        DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(name),
        StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229640")),
        Blocks(Paragraph(Text("The one-defect successor counts and continuation powers retain their original values. Exactly two monochromatic bonds define the additional transition entries. The full continuation vector satisfies the cube of the proper-colouring sextic after three transitions. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference."))),theorem?DescribeRole.Theorem:DescribeRole.Definition);
    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Row() => Arrow(Fin(4),Fin(3));
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Sum(string n,Formula t,Formula b) => Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(b));
    private static Formula If(Formula c,Formula y,Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n,params Formula[] a) => Call("HardinA229640StripData."+n,a);
    private static Formula IntVec(Formula x,int n) => Typed(x,Arrow(Fin(n),Q("Int")));
    private static Formula Power(Formula n) => Call("Matrix.mulVec",Call("HPow.hPow",Data("T"),n),Data("terminal"));
    private static Formula[] Coeffs() => new long[]{64,96,-1152,-1336,7824,6426,-23929,-13335,31293,15750,-18957,-10083,4906,2967,-357,-270,21,9}.Select(N).ToArray();
    private static Formula Vector(params Formula[] a) => Matrix(a);
    private static Formula Matrix(params Formula[][] rows) {
        var a=new List<Formula>{Begin,Grp(F.Id("pmatrix"))};
        for(int i=0;i<rows.Length;i++){if(i>0)a.Add(RowBreak);for(int j=0;j<rows[i].Length;j++){if(j>0)a.Add(Amp);a.Add(rows[i][j]);}}
        a.AddRange([End,Grp(F.Id("pmatrix"))]);return Seq(a.ToArray());}
    private static Formula Certificate() {
        var p=V("p");var r=V("r");var d=V("d");var s=V("s");var cost=Call("DefectTransfer.bondDefects",Call("HardinA229537StripData.between"),p,r);
        var trans=All("p",Row(),All("d",Fin(3),All("s",Fin(42),Eq(Sum("r",Row(),If(And(Le(cost,Val(d)),Eq(Data("cl",r,Sub(Val(d),cost)),s)),Typed(N(1),Q("Int")),Typed(N(0),Q("Int")))),Data("T",Data("cl",p,Val(d)),s)))));
        var poly=Eq(Power(N(21)),Sum("k",Fin(18),Call("HSMul.hSMul",App(IntVec(Vector(Coeffs()),18),V("k")),Power(Add(N(3),Val(V("k")))))));
        return And(trans,poly);
    }

}
