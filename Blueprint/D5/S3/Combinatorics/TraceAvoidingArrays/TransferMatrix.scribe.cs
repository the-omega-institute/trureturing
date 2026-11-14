using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class TransferMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/hardin2011tracearrays");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite words with pair and triple conditions are counted by a weighted matrix on classes of row pairs.",
        H("Counting locally constrained finite words"), Blocks(
            Node("tailGood", "Admissible continuations", TailFormula(), "After two specified rows, each new row must satisfy the pair test with its predecessor and the triple test with both preceding rows.", DescribeRole.Definition),
            Node("good", "Locally admissible words", GoodFormula(), "The empty word and every one-row word are admissible. Longer words satisfy the first pair test and all continuation tests.", DescribeRole.Definition),
            Existing("cont", "Continuation cardinality", "The integer cardinality counts all finite continuations after two specified boundary rows, with the original pair and triple conditions.", DescribeRole.Definition),
            Existing("cont_matrix", "Exact continuation transfer", "Under the classwise successor-count hypothesis, every admissible boundary pair has continuation count equal to its matrix-power coordinate, for every continuation length.", DescribeRole.Theorem),
            Node("good_iff_local", "Admissibility is a local condition", LocalFormula(), "A word is admissible exactly when every two consecutive entries pass the pair test and every three consecutive entries pass the triple test; entries are read with a default value outside the word, which the length bounds never reach.", DescribeRole.Theorem),
            Node("pairOK", "Horizontal trace tests", PairFormula(), "For two rows, traces at adjacent block columns differ.", DescribeRole.Definition),
            Node("tripleOK", "Vertical trace tests", TripleFormula(), "For three rows, traces at corresponding block columns in the two neighboring row pairs differ.", DescribeRole.Definition),
            Node("arrayOK", "All neighboring tests", ArrayFormula(), "The finite indexed array satisfies every horizontal and vertical neighboring-trace inequality.", DescribeRole.Definition),
            Node("arrayOKIffGood", "Indexed and recursive tests agree", ArrayIffFormula(), "Reading an indexed array as a list gives exactly the recursive pair and triple tests.", DescribeRole.Theorem),
            Node("cardMatrix", "The weighted counting formula", CardFormula(), "Suppose every allowed row pair in a given class has the same number of legal successors in each destination class, and the initial multiplicities are v. Induction on the continuation length gives the cardinality as the dot product of v with the corresponding matrix power applied to the constant-one vector.", DescribeRole.Theorem),
            Node("scalarRelationShift", "Transporting a vector relation", ShiftFormula(), "Multiplication by a further matrix power and an initial row vector transports a polynomial relation to every later scalar count.", DescribeRole.Theorem),
            Node("tabulatedPowers", "Successive vectors are matrix powers", TableFormula(), "A finite table starting at the constant-one vector and satisfying each matrix-vector step agrees with the corresponding powers throughout its domain.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose, DescribeRole role) => Describe.Lean(DescribeId.Create("hardin-transfer-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static DocumentBlock Existing(string declaration, string title, string prose, DescribeRole role) => Describe.Lean(DescribeId.Create("hardin-transfer-" + declaration.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula R() => V("R");
    private static Formula S() => V("S");
    private static Formula PropF() => Op("Prop");
    private static Formula ListR() => Call("List", R());
    private static Formula P() => V("P");
    private static Formula Q() => V("Q");
    private static Formula PQ(Formula body) => All("R", Op("Type"), All("P", Arr(R(), Arr(R(), PropF())), All("Q", Arr(R(), Arr(R(), Arr(R(), PropF()))), body)));
    private static Formula G(string name, params Formula[] args) => Call(name, args);
    private static Formula Cons(Formula a, Formula xs) => App(Qualified("List", "cons"), a, xs);
    private static Formula Nil() => Qualified("List", "nil");
    private static Formula TrueF() => Op("True");
    private static Formula Match(Formula xs, Formula nilCase, Formula consPattern, Formula consCase) => Seq(Op("match"), Sp, xs, Sp, Op("with"), Sp, Mid, Sp, Nil(), Sp, Mapsto, Sp, nilCase, Sp, Mid, Sp, consPattern, Sp, Mapsto, Sp, consCase);
    private static Formula TailFormula()
    {
        var a=V("a");var b=V("b");var c=V("c");var xs=V("xs");var cs=V("cs");
        return Disp(PQ(All("a",R(),All("b",R(),All("xs",ListR(),Eq(G("tailGood",P(),Q(),a,b,xs),Match(xs,TrueF(),Cons(c,cs),AndF(App(P(),b,c),AndF(App(Q(),a,b,c),G("tailGood",P(),Q(),b,c,cs))))))))));
    }
    private static Formula GoodFormula()
    {
        var a=V("a"); var b=V("b"); var cs=V("cs");
        var empty=Eq(G("good",P(),Q(),Nil()),TrueF());
        var singleton=All("a",R(),Eq(G("good",P(),Q(),Cons(a,Nil())),TrueF()));
        var longer=All("a",R(),All("b",R(),All("cs",ListR(),
            Eq(G("good",P(),Q(),Cons(a,Cons(b,cs))),
                AndF(App(P(),a,b),G("tailGood",P(),Q(),a,b,cs))))));
        return Disp(PQ(AndF(empty,AndF(singleton,longer))));
    }
    private static Formula TraceBind(Formula body) => All("R",Op("Type"),All("J",Op("Type"),All("K",Op("Type"),All("tr",Arr(R(),Arr(R(),Arr(V("J"),V("K")))),body))));
    private static Formula AdjBind(Formula body) => All("adj",Arr(V("J"),Arr(V("J"),PropF())),body);
    private static Formula LocalFormula()
    {
        var xs=V("xs");var i=V("i");
        Formula At(Formula k) => App(Qualified("List","getD"),xs,k,Op("default"));
        Formula Below(int d) => Seq(PlusF(i,Num(d)),Sp,F.Lt,Sp,App(Qualified("List","length"),xs));
        var pairs=All("i",NatF(),Imp(Below(1),App(P(),At(i),At(PlusF(i,Num(1))))));
        var triples=All("i",NatF(),Imp(Below(2),App(Q(),At(i),At(PlusF(i,Num(1))),At(PlusF(i,Num(2))))));
        return Disp(PQ(Seq(OpenBracket,Call("Inhabited",R()),CloseBracket,Sp,All("xs",ListR(),IffF(G("good",P(),Q(),xs),AndF(pairs,triples))))));
    }
    private static Formula PairFormula()
    {
        var a=V("a");var b=V("b");var j=V("j");var k=V("k");var tr=V("tr");var adj=V("adj");
        return Disp(TraceBind(AdjBind(All("a",R(),All("b",R(),IffF(G("pairOK",tr,adj,a,b),All("j",V("J"),All("k",V("J"),Imp(App(adj,j,k),Ne(App(tr,a,b,j),App(tr,a,b,k)))))))))));
    }
    private static Formula TripleFormula()
    {
        var a=V("a");var b=V("b");var c=V("c");var j=V("j");var tr=V("tr");
        return Disp(TraceBind(All("a",R(),All("b",R(),All("c",R(),IffF(G("tripleOK",tr,a,b,c),All("j",V("J"),Ne(App(tr,a,b,j),App(tr,b,c,j)))))))));
    }
    private static Formula Val(Formula a) => Call("val",a);
    private static Formula ArrayBody()
    {
        var n=V("n");var a=V("a");var i=V("i");var k=V("k");var j=V("j");var l=V("l");
        Formula Trace(Formula r,Formula c) => App(V("tr"),App(a,App(Qualified("Fin","castSucc"),r)),App(a,App(Qualified("Fin","succ"),r)),c);
        return AndF(All("i",Fin(n),All("k",Fin(n),All("j",V("J"),Imp(Eq(Val(k),PlusF(Val(i),Num(1))),Ne(Trace(i,j),Trace(k,j)))))),All("i",Fin(n),All("j",V("J"),All("l",V("J"),Imp(App(V("adj"),j,l),Ne(Trace(i,j),Trace(i,l)))))));
    }
    private static Formula ArrayParams(Formula body) => TraceBind(AdjBind(All("n",NatF(),All("a",Arr(Fin(PlusF(V("n"),Num(1))),R()),body))));
    private static Formula ArrayFormula() => Disp(ArrayParams(IffF(G("arrayOK",V("tr"),V("adj"),V("n"),V("a")),ArrayBody())));
    private static Formula ArrayIffFormula() => Disp(ArrayParams(Seq(OpenBracket,Call("Inhabited",R()),CloseBracket,Sp,IffF(G("arrayOK",V("tr"),V("adj"),V("n"),V("a")),G("good",G("pairOK",V("tr"),V("adj")),G("tripleOK",V("tr")),App(Qualified("List","ofFn"),V("a")))))));
    private static Formula Sum(string name,Formula type,Formula value) => Seq(new Formula.Subscript(F.Sum,Parenthesized(Seq(V(name),Colon,Sp,type))),Sp,value);
    private static Formula GenericStates(Formula body) => All("R",Op("Type"),All("S",Op("Type"),Seq(OpenBracket,Call("Fintype",R()),CloseBracket,Sp,OpenBracket,Call("Fintype",S()),CloseBracket,Sp,OpenBracket,Call("DecidableEq",S()),CloseBracket,Sp,body)));
    private static Formula StateOnly(Formula body) => All("S",Op("Type"),Seq(OpenBracket,Call("Fintype",S()),CloseBracket,Sp,OpenBracket,Call("DecidableEq",S()),CloseBracket,Sp,body));
    private static Formula OneVector() => Cast(Num(1),Arr(S(),IntF()));
    private static Formula MV(Formula exponent) => App(Qualified("Matrix","mulVec"),Pow(V("T"),exponent),OneVector());
    private static Formula CardFormula()
    {
        var a=V("a");var b=V("b");var c=V("c");var s=V("s");var n=V("n");var cl=V("cl");
        var ht=All("a",R(),All("b",R(),Imp(App(P(),a,b),All("s",S(),Eq(Sum("c",R(),IfF(AndF(App(P(),b,c),AndF(App(Q(),a,b,c),Eq(App(cl,b,c),s))),Cast(Num(1),IntF()),Num(0))),App(V("T"),App(cl,a,b),s))))));
        var hv=All("s",S(),Eq(Sum("a",R(),Sum("b",R(),IfF(AndF(App(P(),a,b),Eq(App(cl,a,b),s)),Cast(Num(1),IntF()),Num(0)))),App(V("v"),s)));
        var card=Cast(App(Qualified("Nat","card"),Seq(OpenBrace,V("a"),Colon,Sp,Arr(Fin(PlusF(n,Num(2))),R()),Sp,Mid,Sp,G("good",P(),Q(),App(Qualified("List","ofFn"),V("a"))),CloseBrace)),IntF());
        var body=All("P",Arr(R(),Arr(R(),PropF())),All("Q",Arr(R(),Arr(R(),Arr(R(),PropF()))),All("cl",Arr(R(),Arr(R(),S())),All("T",MatrixF(S(),S(),IntF()),All("v",Arr(S(),IntF()),Imp(ht,Imp(hv,All("n",NatF(),Eq(card,Call("dotProduct",V("v"),MV(n)))))))))));
        return Disp(GenericStates(body));
    }
    private static Formula ShiftFormula()
    {
        var n=V("n");var b=V("b");var d=V("d");var j=V("j");var c=V("c");
        var h=Eq(MV(PlusF(b,d)),Sum("j",Fin(d),App(Qualified("HSMul","hSMul"),App(c,j),MV(PlusF(b,Val(j))))));
        var body=All("T",MatrixF(S(),S(),IntF()),All("v",Arr(S(),IntF()),All("d",NatF(),All("b",NatF(),All("c",Arr(Fin(d),IntF()),Imp(h,All("n",NatF(),Eq(Call("dotProduct",V("v"),MV(PlusF(PlusF(n,b),d))),Sum("j",Fin(d),Mul(App(c,j),Call("dotProduct",V("v"),MV(PlusF(PlusF(n,b),Val(j))))))))))))));
        return Disp(StateOnly(body));
    }
    private static Formula TableFormula()
    {
        var k=V("k");var n=V("N");var w=V("W");
        var step=All("k",Fin(n),Eq(App(w,App(Qualified("Fin","succ"),k)),App(Qualified("Matrix","mulVec"),V("T"),App(w,App(Qualified("Fin","castSucc"),k)))));
        return Disp(StateOnly(All("T",MatrixF(S(),S(),IntF()),All("N",NatF(),All("W",Arr(Fin(PlusF(n,Num(1))),Arr(S(),IntF())),Imp(Eq(App(w,Num(0)),OneVector()),Imp(step,All("k",Fin(PlusF(n,Num(1))),Eq(MV(Val(k)),App(w,k))))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Num(int n) => n < 0 ? Seq(Minus, Num(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Seq(Op("if"), Sp, cond, Sp, Op("then"), Sp, yes, Sp, Op("else"), Sp, no);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula PlusF(Formula a, Formula b) => Add(a, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula MatrixF(Formula rows, Formula cols, Formula field) => Call("Matrix", rows, cols, field);

}
