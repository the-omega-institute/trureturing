using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The four-row one-sided pair transfer definitions.", H("One-sided pair transfer core"), Blocks(
        Paragraph(Text("The core supplies the literal four-row proper-pattern predicate, its fourteen-class transfer matrix and the public grid transport used by the counting certificate.")),
        Node("compatible", "One-sided column compatibility", CompatibleFormula(), DescribeRole.Definition),
        Node("instDecidableCompatible", "Deciding column compatibility", DecidableCompatibleFormula(), DescribeRole.Definition),
        Node("Proper", "Proper pair-label patterns", ProperFormula(), DescribeRole.Definition),
        Node("L", "Literal pair-pattern count", CountFormula(), DescribeRole.Definition),
        Node("Q", "Fourteen-class transfer matrix", MatrixFormula(), DescribeRole.Definition),
        Node("weights", "Class weights", WeightsFormula(), DescribeRole.Definition),
        Node("compatible_relabel", "Relabelling preserves compatibility", CompatibleRelabelFormula(), DescribeRole.Theorem),
        Node("grid_good", "Grid locality characterization", GridGoodFormula(), DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role) => Describe.Lean(DescribeId.Create(name == "gridEquiv" ? "grid-equiv" : name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(title + "."))), role);
    private static Formula CompatibleFormula()
    {
        var a=V("a"); var b=V("b"); var r=V("r"); var s=V("s");
        var condition=Imp(Or(Eq(r,s),Eq(Add(Val(r),D(1)),Val(s))),Ne(App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.column"),a,s),App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.column"),b,r)));
        return All("a",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),All("b",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),Eq(App(Own("compatible"),a,b),All("r",Fin(D(4)),All("s",Fin(D(4)),condition)))));
    }
    private static Formula ProperFormula()
    {
        var n=V("n"); var p=V("P"); var j=V("j"); var h=V("h"); var r=V("r"); var s=V("s");
        var next=App(Q("Fin.mk"),Add(Val(j),D(1)),h);
        var condition=Imp(Or(Eq(r,s),Eq(Add(Val(r),D(1)),Val(s))),Ne(App(p,Pair(s,j)),App(p,Pair(r,next))));
        return All("n",Q("Nat"),All("P",Arrow(Cells(n),Fin(D(3))),Eq(App(Own("Proper"),p),All("j",Fin(n),All("h",Lt(Add(Val(j),D(1)),n),All("r",Fin(D(4)),All("s",Fin(D(4)),condition)))))));
    }
    private static Formula DecidableCompatibleFormula()
    {
        var a=V("a"); var b=V("b");
        return All("a",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),All("b",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),
            Typed(Own("instDecidableCompatible",a,b),Call("Decidable",Own("compatible",a,b)))));
    }
    private static Formula CountFormula(){var n=V("n");var p=V("P");var arrays=Arrow(Cells(n),Fin(D(3)));return All("n",Q("Nat"),Eq(App(Own("L"),n),App(Q("Finset.card"),App(Q("Finset.filter"),Fn("P",arrays,App(Own("Proper"),p)),Q("Finset.univ")))));}
    private static Formula MatrixFormula()=>Eq(Own("Q"),MatrixRows());
    private static Formula WeightsFormula()=>Eq(Own("weights"),Typed(Vector(48,48,24,48,24,24,12,12,24,48,24,12,12,24),Arrow(Fin(D(14)),Q("Int"))));
    private static Formula CompatibleRelabelFormula(){var e=V("e");var a=V("a");var b=V("b");return All("e",Perm(),All("a",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),All("b",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),Iff(App(Own("compatible"),App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.relabel"),e,a),App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.relabel"),e,b)),App(Own("compatible"),a,b)))));}
    private static Formula GridGoodFormula()
    {
        var n=V("n"); var p=V("P");
        var unrestricted=Call("Function.const",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),
            Call("Function.const",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),Call("Function.const",Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Col"),Q("True"))));
        var good=App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix.good"),Own("compatible"),unrestricted,App(Q("List.ofFn"),App(App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.gridEquiv"),n),p)));
        return All("n",Q("Nat"),All("P",Arrow(Cells(n),Fin(D(3))),Iff(App(Own("Proper"),p),good)));
    }
    private static Formula MatrixRows()=>Vector(Vector(2,2,2,2,0,2,2,0,2,2,0,0,0,0),Vector(1,1,0,1,1,1,0,1,0,1,1,0,0,0),Vector(1,1,0,0,0,0,0,0,1,1,0,0,0,0),Vector(1,1,1,1,0,0,0,0,0,1,1,0,1,1),Vector(0,0,0,1,1,0,0,0,0,0,0,1,0,1),Vector(1,1,1,1,0,0,0,0,0,0,0,0,0,0),Vector(1,1,0,0,0,0,0,0,0,0,0,0,0,0),Vector(0,0,0,1,1,0,0,0,0,0,0,0,0,0),Vector(1,1,0,0,0,1,0,1,0,0,0,0,0,0),Vector(1,1,1,1,0,1,1,0,1,1,0,0,0,0),Vector(0,0,0,1,1,0,0,0,0,1,1,0,0,0),Vector(0,0,0,0,0,0,0,0,0,0,0,1,0,1),Vector(0,0,0,0,0,0,0,0,1,1,0,0,0,0),Vector(0,0,0,0,0,0,0,0,0,1,1,0,1,1));
    private static Formula Vector(params Formula[] xs)=>Seq(Bang,OpenBracket,Seq(xs.SelectMany((x,i)=>i==0?new[]{x}:new[]{Comma,Sp,x}).ToArray()),CloseBracket);
    private static Formula Vector(params int[] xs)=>Vector(xs.Select(x=>D(x)).ToArray());
    private static Formula Pair(Formula a,Formula b)=>Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Product(Formula a,Formula b)=>Seq(Parenthesized(a),Sp,Times,Sp,Parenthesized(b));
    private static Formula Cells(Formula n)=>Product(Fin(D(4)),Fin(n));
    private static Formula Perm()=>App(Q("Equiv.Perm"),Fin(D(3)));
    private static Formula Fn(string n,Formula t,Formula b)=>Parenthesized(Seq(LambdaLower,Sp,Typed(V(n),t),Sp,Mapsto,Sp,b));
    private static Formula Or(Formula a,Formula b)=>new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Or,Parenthesized(b));
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Iff,Parenthesized(b));
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Val(Formula x)=>App(Q("Fin.val"),x);
    private static Formula Parenthesized(Formula x)=>Seq(Open,x,Close);
    private static Formula Typed(Formula x,Formula t)=>Parenthesized(Seq(x,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula Own(string n,params Formula[] args)=>Call(LeanPrefix+n,args);
    private static Formula Call(string n,params Formula[] args)=>args.Length==0?Q(n):new Formula.Apply(Q(n),[..args]);
    private static Formula App(Formula f,params Formula[] args)=>new Formula.Apply(f,[..args]);
    private static Formula Q(string n)=>Seq(n.Split('.').SelectMany((part,i)=>i==0?new[]{Operatorname,Grp(V(part))}:new[]{Dot,Operatorname,Grp(V(part))}).ToArray());
    private static Formula V(string n)=>F.Id(n);
    private static Formula D(int n)=>StrataLint.Scribe.FormulaDsl.D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c=>(byte)(c-'0')).ToArray());
    private static Formula All(string n,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Fin(Formula n)=>App(Q("Fin"),n);
}
