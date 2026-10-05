using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class CutRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/CutRepresentation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual palindrome cut from class S is represented by the complete finite transducer.", H("Complete Representation of Palindrome Cuts"), Blocks(
        Describe.Lean(DescribeId.Create("pd-cutrepresentation-classs"),
            DeclarationHandle.Create(Prefix + "classS"), H("The literal signed-digit class S"),
            StatementSource.FromAuthor(ClassFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Class S consists of endpoints whose rounded-half nonadjacent expansion has a gap of at least three between consecutive nonzero digits of different signs. The existential length has an explicit bound making the triple-binary expansion complete. Indices i and j range over Fin h; intermediate indices k range over the naturals. Entry means option lookup with default zero, div and mod mean natural integer quotient and remainder, and NatSub is truncated natural subtraction."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-cutrepresentation-cut-representation-completeness"),
            DeclarationHandle.Create(Prefix + "cut_representation_completeness"), H("Literal legal cuts give accepting paths"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every nonempty palindromic suffix from j to n with n in class S, an accepting path records both endpoint parities and both shifted endpoint values. Either acceptance mode may occur: true has a valid output class, and false records an output class violation. The proof builds the bit-relation path from the actual dyadic palindrome radius, pads it by zero bits, supplies complete nonadjacent signed expansions, derives distance-two input spacing from the consecutive-sign condition, and performs the carry realization. All lengths are unrestricted. This theorem supplies complete legal-cut representation; tightness is used separately to exclude the class-violation mode."))), DescribeRole.Theorem))));
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
    private static Formula ClassFormula()
    {
        var ds=Call("tripleSignedDigits",Call("div",Add(V("n"),D(1)),D(2)),V("h"));
        Formula E(Formula i) => Call("getD",Call("getElemOption",ds,i),D(0));
        var i=Call("val",V("i"));var j=Call("val",V("j"));
        var separated=All("i",Call("Fin",V("h")),All("j",Call("Fin",V("h")),Imp(And(
            LtF(i,j),Ne(E(i),D(0)),Ne(E(j),D(0)),
            All("k",N(),Imp(And(LtF(i,V("k")),LtF(V("k"),j)),Eqn(E(V("k")),D(0)))),Ne(E(i),E(j))),
            LeF(D(3),Call("NatSub",j,i)))));
        return Disp(All("n",N(),IffF(Call("classS",V("n")),Ex("h",N(),And(
            LtF(Mul(D(3),Call("div",Add(V("n"),D(1)),D(2))),Pow(D(2),Add(V("h"),D(1)))),separated)))));
    }
    private static Formula CutFormula()
    {
        var pn=Call("mod",V("n"),D(2));var pj=Call("mod",V("j"),D(2));
        var graph=Call("baseAutomaton",V("charge"));
        var conclusion=Ex("charge",Ty("Bool"),Ex("s",Call("Fin",D(1,4,9,2)),Ex("t",Call("Fin",D(1,4,9,2)),Ex("xs",ListOf(Alphabet()),And(
            Mem(V("s"),Call("start",graph)),Mem(V("t"),Call("accept",graph)),Call("Nonempty",Call("Path",graph,V("s"),V("t"),V("xs"))),
            Eqn(Entry(Call("fst",Call("baseTable",Call("val",V("s")))),2),Cast(pn,Z())),
            Eqn(Entry(Call("fst",Call("baseTable",Call("val",V("s")))),3),Cast(pj,Z())),
            Eqn(Fold(V("xs"),Alphabet(),Z(),Call("fst",Call("snd",Call("snd",V("a"))))),Cast(Call("div",V("n"),D(2)),Z())),
            Eqn(Fold(V("xs"),Alphabet(),Z(),Call("snd",Call("snd",Call("snd",V("a"))))),Cast(Call("div",V("j"),D(2)),Z())))))));
        var word=Call("ofFn",Lam("i",Call("Fin",Call("NatSub",V("n"),V("j"))),Call("upd",Add(V("j"),Call("val",V("i"))))));
        return Disp(All("n",N(),All("j",N(),Imp(And(Call("classS",V("n")),LtF(V("j"),V("n")),Call("Palindrome",word)),conclusion))));
    }
}
