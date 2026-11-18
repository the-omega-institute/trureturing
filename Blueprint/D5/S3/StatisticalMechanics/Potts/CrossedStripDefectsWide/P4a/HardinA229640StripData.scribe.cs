using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a;
internal sealed class HardinA229640StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-row two-defect HDA strips.",H("HardinA229640StripData"),Blocks(
            Paragraph(Text("The first fourteen coordinates have two remaining defects. The trailing twenty-eight coordinates are exactly the one-defect transfer. The upper block consists of its one-defect block followed by the literal two-defect table. Each table entry counts next columns with exactly two monochromatic bonds. The submatrix selects rows zero through thirteen and columns fourteen through twenty-seven of the one-defect matrix. Fin.append concatenates the two fourteen-coordinate vectors; Fin.natAdd adds fourteen to an index.")),
            Node("cl",Class(),false),
            Node("T",Transfer(),false),
            Node("initial",All("s",Fin(42),Eq(Data("initial",V("s")),Sum("r",Row(),If(Eq(Data("cl",V("r"),N(2)),V("s")),Typed(N(1),Q("Int")),Typed(N(0),Q("Int")))))),false),
            Node("terminal",Eq(Data("terminal"),Call("Fin.append",IntVec(N(0),14),First("terminal"))),false))));
    private static DocumentBlock Node(string name,Formula formula,bool theorem) => Describe.Lean(
        DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(name),
        StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229640")),
        Blocks(Paragraph(Text("The first fourteen coordinates have two remaining defects. The trailing twenty-eight coordinates are exactly the one-defect transfer. The upper block consists of its one-defect block followed by the literal two-defect table. Each table entry counts next columns with exactly two monochromatic bonds. The submatrix selects rows zero through thirteen and columns fourteen through twenty-seven of the one-defect matrix. Fin.append concatenates the two fourteen-coordinate vectors; Fin.natAdd adds fourteen to an index."))),theorem?DescribeRole.Theorem:DescribeRole.Definition);
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
    private static Formula Pair(Formula a,Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Fn(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,Typed(V(n),t),Mapsto,Sp,Parenthesized(b)));
    private static Formula Sum(string n,Formula t,Formula b) => Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(b));
    private static Formula If(Formula c,Formula y,Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n,params Formula[] a) => Call("HardinA229640StripData."+n,a);
    private static Formula Old(string n,params Formula[] a) => Call("HardinA233177PairTransfer."+n,a);
    private static Formula IntVec(Formula x,int n) => Typed(x,Arrow(Fin(n),Q("Int")));
    private static Formula Matrix(params Formula[][] rows) {
        var a=new List<Formula>{Begin,Grp(F.Id("pmatrix"))};
        for(int i=0;i<rows.Length;i++){if(i>0)a.Add(RowBreak);for(int j=0;j<rows[i].Length;j++){if(j>0)a.Add(Amp);a.Add(rows[i][j]);}}
        a.AddRange([End,Grp(F.Id("pmatrix"))]);return Seq(a.ToArray());}
    private static Formula First(string n,params Formula[] a) => Call("HardinA229537StripData."+n,a);
    private static Formula Class() {var p=V("p");var d=V("d");var c=Old("cls",Pair(App(p,N(0)),Pair(App(p,N(1)),Pair(App(p,N(2)),App(p,N(3))))));
        return All("p",Row(),All("d",Q("Nat"),Eq(Data("cl",p,d),If(Eq(d,N(2)),Call("Fin.castAdd",N(28),c),Call("Fin.natAdd",N(14),First("cl",p,d))))));}
    private static Formula Transfer() {
        var e=Typed(Q("finSumFinEquiv"),Call("Equiv",Call("Sum",Fin(14),Fin(28)),Fin(42)));
        var sub=Call("Matrix.submatrix",First("T"),Fn("i",Fin(14),Call("Fin.castAdd",N(14),V("i"))),Fn("j",Fin(14),Call("Fin.natAdd",N(14),V("j"))),V("i"));
        var table=Typed(Matrix(new Formula[]{N(0),N(2),N(0),N(0),N(2),N(0),N(0),N(2),N(0),N(2),N(4),N(0),N(2),N(2)},new Formula[]{N(1),N(1),N(1),N(1),N(2),N(1),N(0),N(1),N(0),N(2),N(1),N(1),N(1),N(1)},new Formula[]{N(0),N(1),N(2),N(1),N(2),N(2),N(1),N(2),N(1),N(1),N(0),N(0),N(1),N(1)},new Formula[]{N(0),N(1),N(1),N(1),N(2),N(1),N(2),N(1),N(2),N(1),N(0),N(1),N(1),N(2)},new Formula[]{N(1),N(2),N(2),N(2),N(2),N(1),N(1),N(1),N(1),N(1),N(1),N(1),N(1),N(1)},new Formula[]{N(0),N(1),N(2),N(1),N(1),N(2),N(1),N(1),N(1),N(1),N(0),N(0),N(2),N(2)},new Formula[]{N(0),N(0),N(1),N(2),N(1),N(1),N(2),N(1),N(2),N(0),N(2),N(1),N(1),N(1)},new Formula[]{N(1),N(1),N(2),N(1),N(1),N(1),N(1),N(1),N(1),N(1),N(1),N(1),N(1),N(1)},new Formula[]{N(0),N(0),N(1),N(2),N(1),N(1),N(2),N(1),N(3),N(0),N(2),N(0),N(1),N(1)},new Formula[]{N(1),N(2),N(1),N(1),N(1),N(1),N(0),N(1),N(0),N(1),N(1),N(1),N(1),N(2)},new Formula[]{N(2),N(1),N(0),N(0),N(1),N(0),N(2),N(1),N(2),N(1),N(2),N(1),N(1),N(1)},new Formula[]{N(0),N(1),N(0),N(1),N(1),N(0),N(1),N(1),N(0),N(1),N(1),N(0),N(1),N(1)},new Formula[]{N(1),N(1),N(1),N(1),N(1),N(2),N(1),N(1),N(1),N(1),N(1),N(1),N(1),N(1)},new Formula[]{N(1),N(1),N(1),N(2),N(1),N(2),N(1),N(1),N(1),N(2),N(1),N(1),N(1),N(2)}),Call("Matrix",Fin(14),Fin(14),Q("Int")));
        var upper=Fn("i",Fin(14),Call("Fin.append",sub,App(table,V("i"))));
        return Eq(Data("T"),Call("Matrix.reindex",e,e,Call("Matrix.fromBlocks",Old("Q"),upper,Typed(N(0),Call("Matrix",Fin(28),Fin(14),Q("Int"))),First("T"))));
    }

}
