using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a;

internal sealed class HardinA229538StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HDA transfers with one residual defect", H("Five-row HDA transfers with one residual defect"), Blocks(
            Paragraph(Text("A boundary stores the five entries in one column. Every bond crosses to the next column at the same row or an adjacent row.")),
            Node("edges",Edges(),false,"The oriented cut is the set of pairs of row indices that form a bond between columns zero and one."),
            Node("cost",Cost(),false,"The cost is the number of monochromatic bonds on the cut between two decoded columns."),
            Node("bondDefects_empty",BondDefectsEmpty(),true,"The number of monochromatic bonds of a row against itself over the empty edge set is zero."),
            Node("cost_zero",ZeroCost(),true,"A cut has cost zero exactly when every bond has different colours at its endpoints."),
            Node("zero_cost_entry",ZeroCostEntry(),true,"The proper-colouring transfer entry is the indicator of a cut without monochromatic bonds."),
            Node("oneDefect",OneDefect(),false,"Each entry is the indicator of a cut with exactly one monochromatic bond."),
            Node("transfer",Transfer(),false,"The two summands represent one and zero residual defects. A legal cut preserves the budget and a cut of cost one moves from the first summand to the second."),
            Node("terminal",Terminal(),false,"The empty continuation completes an array exactly when its remaining budget is zero."),
            Node("transfer_readout",TransferReadout(),true,"The state type belongs to an arbitrary universe. A vector recurrence for a matrix and terminal vector gives a shifted scalar recurrence for every readout vector."))));

    private static DocumentBlock Node(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229538")),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Pow(Formula a,Formula b) => Seq(a,Caret,Grp(b));
    private static Formula SumOver(string n,Formula t,Formula body) =>
        Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(body));
    private static Formula Pair(Formula a,Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Product(Formula a,Formula b) => Seq(Parenthesized(a),Times,Parenthesized(b));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula If(Formula c,Formula a,Formula b) =>
        Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,a,Sp,Q("else"),Sp,b));
    private static Formula AsInt(Formula a) => Typed(a,Q("Int"));
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula Columns() => Call("Sum",Column(),Column());
    private static Formula M(Formula s) => Call("Matrix",s,s,Q("Int"));
    private static Formula D(string n,params Formula[] a) => Call("HardinA229538StripData."+n,a);
    private static Formula C(string n,params Formula[] a) => Call("HardinA233178Chromatic."+n,a);

    private static Formula Edges() {
        var pairs = Product(Fin(5),Fin(5));
        var r = Call("Fin.val",V("r"));
        var s = Call("Fin.val",V("s"));
        var adjacent = new Formula.Logic(Eq(s,Add(r,N(1))),FormulaLogicOperator.Or,Eq(r,Add(s,N(1))));
        var predicate = new Formula.Logic(Eq(s,r),FormulaLogicOperator.Or,adjacent);
        var filter = Parenthesized(Seq(LambdaLower,Sp,Typed(Pair(V("r"),V("s")),pairs),
            Mapsto,Sp,Parenthesized(predicate)));
        var universe = Typed(Q("Finset.univ"),Call("Finset",pairs));
        return Eq(Typed(D("edges"),Call("Finset",pairs)),Call("Finset.filter",filter,universe));
    }
    private static Formula Cost() {
        Formula Decode(string n)=>Call("HardinA233178Recurrence.columnEquiv",V(n));
        return All("p",Column(),All("q",Column(),Eq(Typed(D("cost",V("p"),V("q")),Q("Nat")),
            Call("DefectTransfer.bondDefects",D("edges"),Decode("p"),Decode("q")))));
    }
    private static Formula BondDefectsEmpty() {
        var row = V("r");
        var empty = Typed(Q("Finset.empty"),Call("Finset",Product(Fin(5),Fin(5))));
        return All("r",Arrow(Fin(5),Fin(3)),Eq(Call("DefectTransfer.bondDefects",empty,row,row),N(0)));
    }
    private static Formula ZeroCost() => All("p",Column(),All("q",Column(),
        new Formula.Logic(Parenthesized(Eq(D("cost",V("p"),V("q")),N(0))),
            FormulaLogicOperator.Iff,Parenthesized(C("Bond",V("p"),V("q"))))));
    private static Formula ZeroCostEntry() => All("p",Column(),All("q",Column(),
        Eq(If(Eq(D("cost",V("p"),V("q")),N(0)),AsInt(N(1)),N(0)),C("T",V("p"),V("q")))));
    private static Formula OneDefect() => All("p",Column(),All("q",Column(),
        Eq(AsInt(D("oneDefect",V("p"),V("q"))),If(Eq(D("cost",V("p"),V("q")),N(1)),N(1),N(0)))));
    private static Formula Transfer() => Eq(Typed(D("transfer"),M(Columns())),
        Call("Matrix.fromBlocks",C("T"),D("oneDefect"),Typed(N(0),M(Column())),C("T")));
    private static Formula Terminal() => Eq(Typed(D("terminal"),Arrow(Columns(),Q("Int"))),
        Call("Sum.elim",Typed(N(0),Arrow(Column(),Q("Int"))),Typed(N(1),Arrow(Column(),Q("Int")))));

    private static Formula TransferReadout() {
        var state=V("S");var matrix=V("M");var u=V("u");var v=V("v");
        var d=V("d");var b=V("b");var n=V("n");var j=V("j");
        var index=Call("Fin",d);
        var vectors=Arrow(state,Q("Int"));
        Formula power(Formula k)=>Call("Matrix.mulVec",Pow(matrix,k),u);
        Formula coefficient()=>new Formula.Apply(V("c"),[j]);
        Formula read(Formula k)=>Call("dotProduct",v,power(k));
        var premise=Eq(power(Add(b,d)),SumOver("j",index,
            Call("SMul.smul",coefficient(),power(Add(b,Call("Fin.val",j))))));
        var shifted=Add(n,b);
        var conclusion=Eq(read(Add(shifted,d)),SumOver("j",index,
            Mul(coefficient(),read(Add(shifted,Call("Fin.val",j))))));
        var implication=new Formula.Logic(Parenthesized(premise),FormulaLogicOperator.Implies,
            Parenthesized(All("n",Q("Nat"),conclusion)));
        var parameters=All("M",M(state),All("u",vectors,All("v",vectors,All("d",Q("Nat"),
            All("b",Q("Nat"),All("c",Arrow(index,Q("Int")),implication))))));
        return All("S",Seq(Q("Type"),Star),Seq(OpenBracket,Call("Fintype",state),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",state),CloseBracket,Sp,parameters));
    }
}
