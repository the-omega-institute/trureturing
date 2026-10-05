using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class TightCutChargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/TightCutCharge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tight legal palindrome cuts preserve class S and do not increase the literal signed-digit charge.", H("Class Preservation and Charge Monotonicity"), Blocks(
        Describe.Lean(DescribeId.Create("pd-tightcutcharge-tight-cut-class-and-q"),
            DeclarationHandle.Create(Prefix + "tight_cut_class_and_Q"), H("The tight-cut transition law"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A cut is tight when the minimum signed weight of the rounded half drops by exactly one. Complete path realization gives an accepting base path. The class-escape potential bound zero excludes the invalid-output mode, since its f charge is one. In the valid-output mode the q+3f bound with terminal phase gives Q(j)≤Q(n). The path's output signed expansion has the literal rounded-half value and class spacing; equal-length zero padding and nonadjacent uniqueness identify it with the triple-binary expansion defining class S. div denotes natural integer quotient, and NatSub denotes truncated natural subtraction."))), DescribeRole.Theorem))));
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


    private static Formula Pair() => Product(N(),N());
    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Ints(params Formula[] xs) => Seq(OpenBracket,xs.Skip(1).Aggregate(xs[0],(a,b)=>Seq(a,Comma,Sp,b)),CloseBracket);
    private static Formula Entry(Formula s, int k) => Call("getD",Call("getElemOption",s,new Formula.Number(k)),D(0));
    private static Formula Fold(Formula xs, Formula elem, Formula value, Formula term) =>
        Call("foldr",Seq(LambdaLower,Sp,V("a"),Colon,elem,Sp,V("x"),Colon,value,Sp,Mapsto,Sp,
            Add(term,Mul(D(2),V("x")))),D(0),xs);
    private static Formula CutFormula()
    {
        Formula Weight(Formula n) => Call("signedWeight",Cast(Call("div",Add(n,D(1)),D(2)),Z()));
        var word=Call("ofFn",Lam("i",Call("Fin",Call("NatSub",V("n"),V("j"))),Call("upd",Add(V("j"),Call("val",V("i"))))));
        var assumptions=And(Call("classS",V("n")),LtF(V("j"),V("n")),Call("Palindrome",word),
            Eqn(Weight(V("n")),Add(Weight(V("j")),D(1))));
        var conclusion=And(Call("classS",V("j")),LeF(Call("signedDigitCharge",V("j")),Call("signedDigitCharge",V("n"))));
        return Disp(All("n",N(),All("j",N(),Imp(assumptions,conclusion))));
    }
}
