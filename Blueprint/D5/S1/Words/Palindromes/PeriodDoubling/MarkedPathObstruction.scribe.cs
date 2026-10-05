using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedPathObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Charge Obstruction", H("Marked Charge Obstruction"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedpathobstruction-marked-charge-obstruction"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathObstruction.marked_charge_obstruction"),
            H("Marked Charge Obstruction"), StatementSource.FromAuthor(MainFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A class-S endpoint of even parity and even signed weight can attain its signed-weight lower bound only if twice its marked-prefix weight fits inside the signed-digit charge plus the lower-tail phase correction. The proof follows an optimal tight path and accounts for each removed marked digit. div and mod denote natural integer quotient and remainder; cast explicitly denotes the displayed coercions. upd denotes the period-doubling word u_pd."))), DescribeRole.Theorem))));
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




    private static Formula MainFormula()
    {
        var n=V("n"); var m=V("m"); var q=V("q"); var t=V("T");
        var half=Cast(Call("div",Add(n,D(1)),D(2)),Z());
        var weight=Call("signedWeight",half);
        var p=Call("PL",Call("ofFn",Seq(LambdaLower,Sp,V("i"),Colon,Call("Fin",n),Sp,Mapsto,Sp,Call("upd",Call("val",V("i"))))));
        var hypotheses=And(Call("classS",n),Call("markedPrefix",n,m,q,t),Eqn(Call("mod",n,D(2)),D(0)),Eqn(Call("mod",weight,D(2)),D(0)),Eqn(p,weight));
        var total=Call("sum",Call("range",m),Lam("s",N(),Add(D(1),Mul(D(2),Cast(Call("mod",Add(q,Mul(D(3),V("s"))),D(2)),Z())))));
        var eta=Ite(LtF(Sub(Mul(D(2),t),Cast(Call("mod",n,D(2)),Z())),D(0)),D(1),D(0));
        var bound=Add(Cast(Call("signedDigitCharge",n),Z()),Mul(Mul(D(2),Cast(Call("mod",q,D(2)),Z())),eta));
        return Disp(All("n",N(),All("m",N(),All("q",N(),All("T",Z(),Imp(hypotheses,LeF(Mul(D(2),total),bound)))))));
    }
}
