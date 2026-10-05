using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseDigitRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseDigitRealization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse expansions turn every accepting cut-bit path into an accepting finite arithmetic path.", H("Signed-Digit Realization of Cut Bit Paths"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basedigitrealization-base-bit-path-realization"),
            DeclarationHandle.Create(Prefix + "base_bit_path_realization"), H("Digit rigidity and carry realization"),
            StatementSource.FromAuthor(RealizationFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Both supplied signed expansions have the length of the bit input and evaluate to twice the respective ceiling half-endpoint. Their coefficients are minus one, zero or one, and adjacent digits cannot both be nonzero. The input additionally forbids opposite signs at distance two, including the two initial zero memories. Modulo-four rigidity identifies the emitted digits at each step; bounded converter carries preserve the residual value and the input spacing prevents rejection. The terminal bit state and zero residual force all converter carries to flush. The finite graph then realizes this arithmetic run with exactly one transition per supplied bit. The charge-mode Boolean selects one of the two graph acceptance sets. div and mod are natural integer quotient and remainder."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
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
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula Pair() => Product(N(),N());
    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Ints(params Formula[] xs) => Seq(OpenBracket,xs.Skip(1).Aggregate(xs[0],(a,b)=>Seq(a,Comma,Sp,b)),CloseBracket);
    private static Formula Entry(Formula s, int k) => Call("getD",Call("getElemOption",s,new Formula.Number(k)),D(0));
    private static Formula Fold(Formula xs, Formula elem, Formula value, Formula term) =>
        Call("foldr",Seq(LambdaLower,Sp,V("a"),Colon,elem,Sp,V("x"),Colon,value,Sp,Mapsto,Sp,
            Add(term,Mul(D(2),V("x")))),D(0),xs);
    private static Formula Coeff(Formula ds) => All("z",Z(),Imp(Mem(V("z"),ds),
        new Formula.Logic(Eqn(V("z"),NegF(D(1))),FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(V("z"),D(0)),FormulaLogicOperator.Or,Eqn(V("z"),D(1))))));
    private static Formula Sparse(Formula ds) => Call("IsChain",ds,
        Seq(LambdaLower,Sp,V("a"),Colon,Z(),Sp,V("b"),Colon,Z(),Sp,Mapsto,Sp,
            new Formula.Logic(Eqn(V("a"),D(0)),FormulaLogicOperator.Or,Eqn(V("b"),D(0)))));
    private static Formula RealizationFormula()
    {
        var pn=Call("mod",V("n"),D(2));var pj=Call("mod",V("j"),D(2));
        var modes=Ite(Eqn(pn,pj),Ints(D(6)),Ite(LtF(pj,pn),Ints(D(1),D(2),D(0)),Ints(D(1),D(2))));
        var chain=Call("cons",D(0),Call("cons",D(0),V("dns")));
        var classCondition=Call("IsChain",Call("zip",chain,Call("tail",chain)),
            Seq(LambdaLower,Sp,V("a"),Colon,Product(Z(),Z()),Sp,V("b"),Colon,Product(Z(),Z()),Sp,Mapsto,Sp,
                Ne(Mul(Call("fst",V("a")),Call("snd",V("b"))),NegF(D(1)))));
        var assumptions=And(Mem(V("r"),modes),Call("Nonempty",Call("Path",V("cutBitAutomaton"),V("r"),D(0),V("bits"))),
            All("a",Pair(),Imp(Mem(V("a"),V("bits")),And(LeF(Call("fst",V("a")),D(1)),LeF(Call("snd",V("a")),D(1))))),
            Eqn(Fold(V("bits"),Pair(),N(),Call("fst",V("a"))),Call("div",V("n"),D(2))),
            Eqn(Fold(V("bits"),Pair(),N(),Call("snd",V("a"))),Call("div",V("j"),D(2))),
            Eqn(Call("length",V("dns")),Call("length",V("bits"))),Eqn(Call("length",V("djs")),Call("length",V("bits"))),
            Coeff(V("dns")),Coeff(V("djs")),Sparse(V("dns")),Sparse(V("djs")),classCondition,
            Eqn(Fold(V("dns"),Z(),Z(),V("a")),Mul(D(2),Cast(Call("div",Add(V("n"),D(1)),D(2)),Z()))),
            Eqn(Fold(V("djs"),Z(),Z(),V("a")),Mul(D(2),Cast(Call("div",Add(V("j"),D(1)),D(2)),Z()))));
        var graph=Call("baseAutomaton",V("charge"));
        var conclusion=Ex("charge",Ty("Bool"),Ex("s",Call("Fin",D(1,4,9,2)),Ex("t",Call("Fin",D(1,4,9,2)),Ex("xs",ListOf(Alphabet()),And(
            Mem(V("s"),Call("start",graph)),Mem(V("t"),Call("accept",graph)),Call("Nonempty",Call("Path",graph,V("s"),V("t"),V("xs"))),
            Eqn(Entry(Call("fst",Call("baseTable",Call("val",V("s")))),2),Cast(pn,Z())),
            Eqn(Entry(Call("fst",Call("baseTable",Call("val",V("s")))),3),Cast(pj,Z())),
            Eqn(Fold(V("xs"),Alphabet(),Z(),Call("fst",Call("snd",Call("snd",V("a"))))),Cast(Call("div",V("n"),D(2)),Z())),
            Eqn(Fold(V("xs"),Alphabet(),Z(),Call("snd",Call("snd",Call("snd",V("a"))))),Cast(Call("div",V("j"),D(2)),Z())),
            Eqn(Call("length",V("xs")),Call("length",V("bits"))))))));
        return Disp(All("n",N(),All("j",N(),All("r",Z(),All("bits",ListOf(Pair()),All("dns",ListOf(Z()),All("djs",ListOf(Z()),Imp(assumptions,conclusion))))))));
    }
}
