using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P4a;
internal sealed class HardinA229640StripDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640Strip.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-row exact-defect HDA strips.",H("HardinA229640Strip"),Blocks(
            Paragraph(Text("The filter counts every actual four-by-n array over Fin 3 with two monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least twenty-two.")),
            Node("a",Count(),false),
            Node("result",Recurrence(),true))));
    private static DocumentBlock Node(string name,Formula formula,bool theorem) => Describe.Lean(
        DescribeId.Create(name.Replace("_","-")),DeclarationHandle.Create(Prefix+name),H(name),
        StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229640")),
        Blocks(Paragraph(Text("The filter counts every actual four-by-n array over Fin 3 with two monochromatic HDA bond and row-major canonical colour introduction. All counts in the recurrence are cast from Nat to Int. Colour relabelling contributes a factor six because at least two colours occur in this range. The recurrence holds at every index at least twenty-two."))),theorem?DescribeRole.Theorem:DescribeRole.Definition);
    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Row() => Arrow(Fin(4),Fin(3));
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Pair(Formula a,Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Product(Formula a,Formula b) => Seq(Parenthesized(a),Times,Parenthesized(b));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Ex(string n,Formula t,Formula b) => Seq(Exists,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Fn(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,Typed(V(n),t),Mapsto,Sp,Parenthesized(b)));
    private static Formula Sum(string n,Formula t,Formula b) => Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(b));
    private static Formula If(Formula c,Formula y,Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Data(string n,params Formula[] a) => Call((n=="horizontal"||n=="between"?"HardinA229537StripData.":"HardinA229640StripData.")+n,a);
    private static Formula Own(string n,params Formula[] a) => Call("HardinA229640Strip."+n,a);
    private static Formula Old(string n,params Formula[] a) => Call("HardinA233177PairTransfer."+n,a);
    private static Formula IntVec(Formula x,int n) => Typed(x,Arrow(Fin(n),Q("Int")));
    private static Formula Power(Formula n) => Call("Matrix.mulVec",Call("HPow.hPow",Data("T"),n),Data("terminal"));
    private static Formula[] Coeffs() => new long[]{-16,-16,196,124,-741,-238,787,250,-288,-102,23,6}.Select(N).ToArray();
    private static Formula Vector(params Formula[] a) => Matrix(a);
    private static Formula Matrix(params Formula[][] rows) {
        var a=new List<Formula>{Begin,Grp(F.Id("pmatrix"))};
        for(int i=0;i<rows.Length;i++){if(i>0)a.Add(RowBreak);for(int j=0;j<rows[i].Length;j++){if(j>0)a.Add(Amp);a.Add(rows[i][j]);}}
        a.AddRange([End,Grp(F.Id("pmatrix"))]);return Seq(a.ToArray());}
    private static Formula Count() {
        var n=V("n");var a=V("A");var cells=Product(Fin(4),Fin(n));
        Formula idx(Formula p)=>Add(Mul(Val(Call("Prod.fst",p)),n),Val(Call("Prod.snd",p)));
        var canonical=All("p",cells,All("c",Fin(3),Imp(Lt(V("c"),App(a,V("p"))),Ex("q",cells,And(Lt(idx(V("q")),idx(V("p"))),Eq(App(a,V("q")),V("c")))))));
        var cols=Call("List.ofFn",Fn("j",Fin(n),Fn("i",Fin(4),App(a,Pair(V("i"),V("j"))))));
        return All("n",Q("Nat"),Eq(Own("a",n),Call("Finset.card",Call("Finset.filter",Fn("A",Arrow(cells,Fin(3)),And(Eq(Call("DefectTransfer.defects",Data("horizontal"),Data("between"),cols),N(2)),canonical)),Typed(Q("Finset.univ"),Call("Finset",Arrow(cells,Fin(3))))))));
    }
    private static Formula Recurrence() {
        Formula a(int j)=>Typed(Own("a",Add(V("n"),N(j))),Q("Int"));
        Formula rhs=Mul(N(9),a(21));
        long[] coeff=[21,-270,-357,2967,4906,-10083,-18957,15750,31293,-13335,-23929,6426,7824,-1336,-1152,96,64];
        for(int i=0;i<coeff.Length;i++) rhs=coeff[i]<0?Sub(rhs,Mul(N(-coeff[i]),a(20-i))):Add(rhs,Mul(N(coeff[i]),a(20-i)));
        return All("n",Q("Nat"),Eq(a(22),rhs));
    }

}
