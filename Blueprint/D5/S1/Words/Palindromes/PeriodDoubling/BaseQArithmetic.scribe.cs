using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseQArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Accepted q paths have the literal arithmetic charge Q(j) - Q(n).", H("Literal Endpoint Charge"), Blocks(
        Describe.Lean(DescribeId.Create("pd-baseqarithmetic-triplesigneddigits"),
            DeclarationHandle.Create(Prefix + "tripleSignedDigits"), H("The nonadjacent digit formula"),
            StatementSource.FromAuthor(DigitsFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Digits are in increasing order of position: digit i is bit i+1 of 3X minus bit i+1 of X. div and mod are natural integer quotient and remainder. The chosen length is a separate parameter."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-baseqarithmetic-signeddigitcharge"),
            DeclarationHandle.Create(Prefix + "signedDigitCharge"), H("Q from positions, sign changes and endpoint parity"),
            StatementSource.FromAuthor(QFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Take X = div(n+1,2) and h = log(2,3X)+1. Enumerate its nonadjacent digits, discard zeros, and sum the weights 1+2(i mod 2), consecutive sign changes, and endpoint parity XOR the negativity of the first surviving sign. The last indicator is zero when no digit survives. Option.elim returns the displayed default for none and applies its function for some."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-baseqarithmetic-memoryrowcheck"),
            DeclarationHandle.Create(Prefix + "memoryRowCheck"), H("Endpoint and first-sign memory checker"),
            StatementSource.FromAuthor(MemoryFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every outgoing edge must preserve the two endpoint parities and update both first-nonzero-sign memories only while their incoming memory is zero. This Boolean checker is reused by the charge identification and by the lowest-position arithmetic interpretation."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-baseqarithmetic-base-path-q-semantics"),
            DeclarationHandle.Create(Prefix + "base_path_Q_semantics"), H("Exact charge of every accepting path"),
            StatementSource.FromAuthor(PathFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For an accepting charge-mode path whose source parities and binary folds encode n and j, the sum of q edge charges plus the terminal phase correction is Q(j)-Q(n). Component 2 or 3 of the source is the endpoint parity; the last two components of an edge label are bits of the integer quotients div(n,2) and div(j,2). The proof checks all sign-memory transitions and identifies the padded output streams with the unique nonadjacent expansions of the rounded halves. The dummy initial zero contributes no weight."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula BooleanNe(Formula a, Formula b) =>
        Seq(Open, a, Sp, Bang, Eq, Sp, b, Close);
    private static Formula BooleanEq(Formula a, Formula b) =>
        Seq(Open, a, Sp, Eq, Eq, Sp, b, Close);

    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));
    private static Formula OptionalHead(Formula xs) =>
        Call("ite", Eqn(xs, Seq(OpenBracket, CloseBracket)), Call("none"),
            Call("some", DottedCall("List", "head", xs)));

    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula s, int k) => Call("getD",OptionalIndex(s,new Formula.Number(k)),D(0));

    private static Formula Digits(Formula x, Formula h) => Call("tripleSignedDigits",x,h);
    private static Formula DigitValue(Formula x, Formula i) =>
        Sub(Cast(Call("mod",Call("div",Mul(D(3),x),Pow(D(2),Add(Call("val",i),D(1)))),D(2)),Z()),
            Cast(Call("mod",Call("div",x,Pow(D(2),Add(Call("val",i),D(1)))),D(2)),Z()));
    private static Formula DigitsFormula() => Disp(All("X",N(),All("h",N(),
        Eqn(Digits(V("X"),V("h")),Call("ofFn",Lam("i",Call("Fin",V("h")),DigitValue(V("X"),V("i"))))))));
    private static Formula QFormula()
    {
        var pair=Product(Z(),N());
        var x=Call("div",Add(V("n"),D(1)),D(2));
        var h=Add(Call("log",D(2),Mul(D(3),x)),D(1));
        var nz=Call("filter",Lam("z",pair,BooleanNe(Call("fst",V("z")), D(0))),Call("zipIdx",Digits(x,h),D(0)));
        var weights=Call("sum",Call("map",Lam("z",pair,Add(D(1),Mul(D(2),Call("mod",Call("snd",V("z")),D(2))))),nz));
        var flips=Call("length",Call("filter",Lam("z",Product(Parenthesized(pair),Parenthesized(pair)),
            BooleanNe(Call("fst",Call("fst",V("z"))), Call("fst",Call("snd",V("z"))))),Call("zip",nz,Call("tail",nz))));
        var initial=DottedCall("Option", "elim", OptionalHead(nz), D(0), Lam("z",pair,Call("toNat",BooleanNe(BooleanEq(Call("mod",V("n"),D(2)), D(1)), Call("decide",LtF(Call("fst",V("z")),D(0)))))));
        return Disp(All("n",N(),Eqn(Call("signedDigitCharge",V("n")),Add(Add(weights,flips),initial))));
    }
    private static Formula PathFormula()
    {
        var f=Call("Fin",D(1,4,9,2));
        var graph=Call("baseAutomaton",Ty("true"));
        var state=Call("fst",Call("baseTable",Call("val",V("s"))));
        var terminal=Call("fst",Call("baseTable",Call("val",V("t"))));
        var nbit=Call("fst",Call("snd",Call("snd",V("a"))));
        var jbit=Call("snd",Call("snd",Call("snd",V("a"))));
        Formula Fold(Formula bit) => Call("foldr",Seq(LambdaLower,Sp,V("a"),Colon,Alphabet(),Sp,V("x"),Colon,Z(),Sp,Mapsto,Sp,Add(bit,Mul(D(2),V("x")))),D(0),V("xs"));
        var qcost=Seq(LambdaLower,Sp,OpenBracket,f,CloseBracket,Sp,V("a"),Colon,Alphabet(),Sp,OpenBracket,f,CloseBracket,Sp,Mapsto,Sp,Call("fst",Call("snd",V("a"))));
        var hyp=And(Mem(V("s"),Call("start",graph)),Mem(V("t"),Call("accept",graph)),
            Eqn(Entry(state,2),Cast(Call("mod",V("n"),D(2)),Z())),Eqn(Entry(state,3),Cast(Call("mod",V("j"),D(2)),Z())),
            Eqn(Fold(nbit),Cast(Call("div",V("n"),D(2)),Z())),Eqn(Fold(jbit),Cast(Call("div",V("j"),D(2)),Z())));
        var body=Imp(hyp,Eqn(Add(Call("pathCharge",qcost,V("p")),Call("baseOffset",terminal)),
            Sub(Cast(Call("signedDigitCharge",V("j")),Z()),Cast(Call("signedDigitCharge",V("n")),Z()))));
        return Disp(All("n",N(),All("j",N(),All("s",f,All("t",f,All("xs",ListOf(Alphabet()),
            All("p",Call("Path",graph,V("s"),V("t"),V("xs")),body)))))));
    }
    private static Formula MemoryFormula()
    {
        var source=Call("fst",Call("baseTable",V("i")));
        var target=Call("fst",Call("baseTable",Call("fst",V("e"))));
        var edges=Call("fst",Call("snd",Call("baseTable",V("i"))));
        Formula E(Formula state,int k) => Call("getD",OptionalIndex(state,new Formula.Number(k)),D(0));
        var cond=And(Eqn(E(target,2),E(source,2)),Eqn(E(target,3),E(source,3)),
            Eqn(E(target,14),Ite(Eqn(E(source,14),D(0)),E(target,10),E(source,14))),
            Eqn(E(target,15),Ite(Eqn(E(source,15),D(0)),E(target,12),E(source,15))));
        var check=Call("all",Seq(LambdaLower,Sp,V("e"),Colon,Product(N(),Z(),Z(),Z(),Z()),Sp,Mapsto,Sp,Call("decide",cond)),edges);
        return Disp(All("i",N(),Eqn(Call("memoryRowCheck",V("i")),check)));
    }

}
