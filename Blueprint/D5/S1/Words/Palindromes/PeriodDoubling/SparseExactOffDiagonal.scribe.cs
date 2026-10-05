using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;
internal sealed class SparseExactOffDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Sparse Off-Diagonal",H("Exact Sparse Off-Diagonal"),Blocks(
        Describe.Lean(DescribeId.Create("pd-sparseexactoffdiagonal-offdiagonal-exact-family"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/SparseExactOffDiagonal.offdiagonal_exact_family"),
            H("Exact Sparse Off-Diagonal"),StatementSource.FromAuthor(MainFormula()),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For positive odd a and odd b at least 2a+1, the prefix palindromic length of the sparse integer with binary expansion (100)^a(10)^b equals a+b. The constructed cut path attains the signed-weight lower bound. upd denotes the period-doubling word u_pd."))),DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Prop() => Ty("Prop");
    private static Formula SetOf(Formula a) => Call("Set", a);
    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NotF(Formula a) => new Formula.Not(a);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula At(Formula f, Formula x) => Call("val", f, x);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));





    private static Formula Sparse(Formula a,Formula b) => Add(
        Call("sum",Call("range",a),Lam("i",N(),Pow(D(2),Add(Add(Mul(D(2),b),D(2)),Mul(D(3),V("i")))))),
        Call("sum",Call("range",b),Lam("j",N(),Pow(D(2),Add(Mul(D(2),V("j")),D(1))))));
    private static Formula P(Formula n) => Call("PL",Call("ofFn",Seq(LambdaLower,Sp,V("k"),Colon,Call("Fin",n),Sp,Mapsto,Sp,Call("upd",Call("val",V("k"))))));
    private static Formula MainFormula()
    {
        var a=V("a");
        var b=V("b");
        var hyp=And(LtF(D(0),a),Eqn(Call("mod",a,D(2)),D(1)),Eqn(Call("mod",b,D(2)),D(1)),LeF(Add(Mul(D(2),a),D(1)),b));
        return Disp(All("a",N(),All("b",N(),Imp(hyp,Eqn(P(Sparse(a,b)),Add(a,b))))));
    }
}
