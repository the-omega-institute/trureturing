using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedPrefixRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The marked prefix survives tight odd palindromic cuts with a corrected charge inequality.",
        H("Arithmetic Rigidity of a Marked Prefix"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedprefixrigidity-marked-prefix-rigidity-and-charge"),
            DeclarationHandle.Create(Prefix + "marked_prefix_rigidity_and_charge"),
            H("Retained and removed prefix alternatives"),
            StatementSource.FromAuthor(RigidityFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A tight palindromic cut between endpoints of opposite parity preserves every positive digit of a literal marked prefix, or removes precisely its lowest digit. In the retained case, the lower tail may change and the difference of signed-digit charges is bounded after correcting by the difference of lower-tail phases. In the removed case, the new lower tail is the exact negative of the old one, with input phase one and output phase zero. The position weight is 1+2(p mod 2), and the phase is the indicator of 2T minus the endpoint parity being negative. The selected digit position and phase snapshots are reconstructed from the path before the marker; the terminal potential then supplies the charge inequality. div and mod denote natural integer quotient and remainder, and Nat.sub denotes truncated natural subtraction."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);




    private static Formula Mod(Formula n) => Call("mod",n,D(2));
    private static Formula Half(Formula n) => Cast(Call("div",Add(n,D(1)),D(2)),Z());
    private static Formula Eta(Formula n, Formula tail) =>
        Ite(LtF(Sub(Mul(D(2),tail),Cast(Mod(n),Z())),D(0)),D(1),D(0));
    private static Formula Weight(Formula p) => Add(D(1),Mul(D(2),Cast(Mod(p),Z())));
    private static Formula ChargeDifference() =>
        Sub(Cast(Call("signedDigitCharge",V("j")),Z()),Cast(Call("signedDigitCharge",V("n")),Z()));
    private static Formula RigidityFormula()
    {
        var n=V("n"); var j=V("j"); var m=V("m"); var p=V("p"); var tail=V("T");
        var pal=Call("Palindrome",Call("ofFn",Seq(LambdaLower,Sp,V("i"),Colon,Call("Fin",DottedCall("Nat", "sub",n,j)),Sp,Mapsto,Sp,
            Upd(Add(j,Call("val",V("i")))))));
        var hypotheses=And(LtF(D(0),m),Call("classS",n),Call("markedPrefix",n,m,p,tail),LtF(j,n),
            Ne(Mod(n),Mod(j)),pal,
            Eqn(Call("signedWeight",Half(n)),Add(Call("signedWeight",Half(j)),D(1))));
        var retained=Ex("U",Z(),And(Call("markedPrefix",j,m,p,V("U")),
            LeF(Add(ChargeDifference(),Mul(Parenthesized(Sub(Weight(p),D(1))),
                Parenthesized(Sub(Eta(j,V("U")),Eta(n,tail))))),D(0))));
        var removed=And(Call("markedPrefix",j,DottedCall("Nat", "sub",m,D(1)),Add(p,D(3)),NegF(tail)),
            Eqn(Eta(n,tail),D(1)),Eqn(Eta(j,NegF(tail)),D(0)),
            LeF(Add(Add(ChargeDifference(),Weight(p)),D(1)),D(0)));
        return Disp(All("n",N(),All("j",N(),All("m",N(),All("p",N(),All("T",Z(),
            Imp(hypotheses,new Formula.Logic(retained,FormulaLogicOperator.Or,removed))))))));
    }
}
