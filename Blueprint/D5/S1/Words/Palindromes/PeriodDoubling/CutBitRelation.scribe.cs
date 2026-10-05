using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class CutBitRelationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/CutBitRelation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty literal palindrome cut has an accepting run in the bit relation.", H("Complete Palindrome Cut Bit Relation"), Blocks(
        Describe.Lean(DescribeId.Create("pd-cutbitrelation-cutbitautomaton"),
            DeclarationHandle.Create(Prefix + "cutBitAutomaton"), H("The relation before adding arithmetic memories"),
            StatementSource.FromAuthor(AutomatonFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The state is an integer relation label; an input is a pair of natural binary digits. Every state is allowed as a starting state in this auxiliary automaton, and only state zero accepts. The cut theorem specifies the actual source choices after consuming the lowest endpoint bits. relNext is the original nine-state transition table."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-cutbitrelation-cut-bit-relation-completeness"),
            DeclarationHandle.Create(Prefix + "cut_bit_relation_completeness"), H("All actual palindrome cuts are represented"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For any nonempty palindromic suffix from prefix j to prefix n, the remaining bit pairs have an accepting path to zero and encode div(n,2) and div(j,2). Equal endpoint parities choose the even-cut source 6; the pair (1,0) additionally permits the already-flushed source 0. Other odd cuts start in source 1 or 2. Every emitted input is zero or one. The proof uses the exact dyadic palindrome radius to construct the complementary A runs and the skipped-bit B runs, and the valuation parity to construct the even-00 runs. No bound is imposed on the length of these runs. div and mod denote natural integer quotient and remainder, and NatSub denotes truncated natural subtraction. This theorem concerns the bit relation; adjoining the signed-digit memories is a separate obligation."))), DescribeRole.Theorem))));
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


    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula s, int k) => Call("getD",Call("getElemOption",s,new Formula.Number(k)),D(0));


    private static Formula Pair() => Product(N(),N());
    private static Formula Ints(params Formula[] xs) => Seq(OpenBracket,xs.Skip(1).Aggregate(xs[0],(a,b)=>Seq(a,Comma,Sp,b)),CloseBracket);
    private static Formula AutomatonFormula()
    {
        var graph=V("cutBitAutomaton");
        var first=Eqn(Call("start",graph),Call("univ",Z()));
        var next=All("s",Z(),All("a",Pair(),Eqn(Call("step",graph,V("s"),V("a")),
            SetBuilder("t",Z(),Mem(V("t"),Call("relNext",V("s"),Cast(Call("fst",V("a")),Z()),Cast(Call("snd",V("a")),Z())))))));
        var last=Eqn(Call("accept",graph),Seq(OpenBrace,D(0),CloseBrace));
        return Disp(And(Parenthesized(first),Parenthesized(next),Parenthesized(last)));
    }
    private static Formula CutFormula()
    {
        var pn=Call("mod",V("n"),D(2));var pj=Call("mod",V("j"),D(2));
        var modes=Ite(Eqn(pn,pj),Ints(D(6)),Ite(LtF(pj,pn),Ints(D(1),D(2),D(0)),Ints(D(1),D(2))));
        Formula Fold(string proj) => Call("foldr",Seq(LambdaLower,Sp,V("a"),Colon,Pair(),Sp,V("x"),Colon,N(),Sp,Mapsto,Sp,
            Add(Call(proj,V("a")),Mul(D(2),V("x")))),D(0),V("xs"));
        var bits=All("a",Pair(),Imp(Mem(V("a"),V("xs")),And(LeF(Call("fst",V("a")),D(1)),LeF(Call("snd",V("a")),D(1)))));
        var conclusion=Ex("r",Z(),Ex("xs",ListOf(Pair()),And(Mem(V("r"),modes),
            Call("Nonempty",Call("Path",V("cutBitAutomaton"),V("r"),D(0),V("xs"))),
            Eqn(Fold("fst"),Call("div",V("n"),D(2))),Eqn(Fold("snd"),Call("div",V("j"),D(2))),bits)));
        var word=Call("ofFn",Lam("i",Call("Fin",Call("NatSub",V("n"),V("j"))),Call("upd",Add(V("j"),Call("val",V("i"))))));
        return Disp(All("n",N(),All("j",N(),Imp(And(LtF(V("j"),V("n")),Call("Palindrome",word)),conclusion))));
    }
    private static Formula SetBuilder(string n, Formula t, Formula p) => Seq(OpenBrace,V(n),Colon,t,Sp,Bar,Sp,p,CloseBrace);
}
