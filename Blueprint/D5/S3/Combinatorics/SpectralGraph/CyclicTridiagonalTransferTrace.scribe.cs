using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class CyclicTridiagonalTransferTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace.";
    public DocumentDefinition Create()
    {
        Formula r=V("R"), n=V("n"), d=V("d"), i=V("i"), j=V("j"), x=V("x");
        Formula seq=Fn(Nat(),r);
        Formula cycle=RingBind(All("N",Nat(),All("d",seq,
            Eqn(Call("cycleDiag",V("N"),d),Sub(
                App(Q("Matrix","diagonal"),Seq(LambdaLower,Sp,i,Colon,Sp,Fin(V("N")),Sp,Mapsto,Sp,App(d,Val(i)))),
                App(Q("SimpleGraph","adjMatrix"),App(Q("SimpleGraph","cycleGraph"),V("N")),r))))));
        Formula entries=RingBind(All("n",Nat(),All("d",seq,All("i",Fin(Add(n,D(3))),All("j",Fin(Add(n,D(3))),
            Eqn(App(Call("cycleDiag",Add(n,D(3)),d),i,j),If(Eqn(i,j),App(d,Val(i)),
                If(Adj(i,j,Add(n,D(3))),MinusOf(D(1)),D(0)))))))));
        Formula transfer=RingOnlyBind(All("d",V("K"),Eqn(Call("transfer",d),Seq(Begin,Grp(V("pmatrix")),d,Amp,MinusOf(D(1)),RowBreak,D(1),Amp,D(0),End,Grp(V("pmatrix"))))));
        Formula prod=RingOnlyBind(All("d",Fn(Nat(),V("K")),new Formula.Logic(Eqn(Call("evolution",d,D(0)),D(1)),FormulaLogicOperator.And,Parenthesized(All("n",Nat(),Eqn(Call("evolution",d,Add(n,D(1))),Mul(Call("transfer",App(d,n)),Call("evolution",d,n))))))));
        Formula evolutionAdd=RingOnlyBind(All("d",Fn(Nat(),V("K")),All("n",Nat(),All("k",Nat(),
            Eqn(Call("evolution",d,Add(n,V("k"))),Mul(Call("evolution",
                Seq(LambdaLower,Sp,i,Colon,Sp,Nat(),Sp,Mapsto,Sp,App(d,Add(n,i))),V("k")),Call("evolution",d,n)))))));
        Formula evolutionDet=RingBind(All("d",seq,All("n",Nat(),Eqn(Det(Call("evolution",d,n)),D(1)))));
        Formula determinant=RingBind(All("x",r,Eqn(Det(Call("transfer",x)),D(1))));
        Formula result=RingBind(All("n",Nat(),All("d",seq,Eqn(Det(Call("cycleDiag",Add(n,D(3)),d)),
            Sub(App(Q("Matrix","trace"),Call("evolution",d,Add(n,D(3)))),D(2))))));
        return DocumentDefinition.Create(ScribeNode.Create("A cyclic Jacobi determinant and its two-dimensional transfer evolution.",
            H("Cyclic tridiagonal determinants and transfer traces"),Blocks(
                Node("cycle","Cyclic tridiagonal matrix","cycleDiag",cycle,"The diagonal potential matrix minus the adjacency matrix of the cycle graph. The determinant identity concerns sizes at least three.",DescribeRole.Definition),
                Node("entries","Entries of the cyclic matrix","cycleDiag_apply",entries,"For sizes at least three, the diagonal entries are d, cyclic off-diagonal entries are minus one, and all remaining entries are zero.",DescribeRole.Theorem),
                Node("transfer","One transfer step","transfer",transfer,"The two coordinates carry consecutive values of a second-order recurrence.",DescribeRole.Definition),
                Node("product","Ordered transfer product","evolution",prod,"The recursion multiplies the next step on the left. The variable n in the successor branch is bound by that pattern.",DescribeRole.Definition),
                Node("unit","Determinant of one step","transfer_det",determinant,"Every transfer step has determinant one; this also determines the determinant of a finite product.",DescribeRole.Theorem),
                Node("addition","Splitting the transfer evolution","evolution_add",evolutionAdd,"Splitting a sequence after n steps puts the later k steps on the left.",DescribeRole.Theorem),
                Node("productdet","Determinant of the evolution","evolution_det",evolutionDet,"Multiplicativity of the determinant and induction preserve determinant one.",DescribeRole.Theorem),
                Node("determinant","The cyclic determinant identity","cycleDiag_det_transfer",result,"Impulse solutions form a lower unitriangular matrix. Multiplication reduces all interior rows to coordinate rows and leaves a two by two boundary block. Its determinant is the negative cyclic determinant. The two impulse solutions also give the entries of the transfer product, whose determinant is one; the boundary determinant consequently equals two minus the trace. These identities hold over every commutative ring.",DescribeRole.Theorem))));
    }
    private static DocumentBlock Node(string id,string title,string name,Formula f,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cyclic-transfer-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula Q(string owner, string name) => Seq(C(owner), Dot, C(name));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [..a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? C(s) : App(C(s), a);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula MinusOf(Formula a) => new Formula.Negate(Parenthesized(a));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Nat() => C("Nat");
    private static Formula Val(Formula i) => Call("val", i);
    private static Formula Mod(Formula a, Formula n) => App(Q("Nat", "mod"), a, n);
    private static Formula Adj(Formula i, Formula j, Formula n) => new Formula.Logic(
        Eqn(Mod(Add(Val(i), D(1)), n), Val(j)), FormulaLogicOperator.Or,
        Eqn(Mod(Add(Val(j), D(1)), n), Val(i)));
    private static Formula If(Formula h, Formula a, Formula b) => Seq(C("if"), Sp, Parenthesized(h), Sp, C("then"), Sp, a, Sp, C("else"), Sp, b);
    private static Formula Det(Formula a) => App(Q("Matrix", "det"), a);
    private static Formula RingOnlyBind(Formula f) => All("K", C("Type"), Seq(OpenBracket, Call("Ring", V("K")), CloseBracket, Sp, f));
    private static Formula RingBind(Formula f) => All("R", C("Type"), Seq(OpenBracket, Call("CommRing", V("R")), CloseBracket, Sp, f));
}
