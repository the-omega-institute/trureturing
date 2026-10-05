using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BasePathRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BasePathRealization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal arithmetic paths are represented completely by the finite transducer graph.", H("Complete Representation of Arithmetic Transducer Paths"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basepathrealization-baserawautomaton"),
            DeclarationHandle.Create(Prefix + "baseRawAutomaton"), H("The arithmetic automaton before indexing"),
            StatementSource.FromAuthor(RawFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("States are lists of integer components. The source set is initialStates, each step is one of baseSuccessors, and acceptance requires baseTerminal to be true. The four alphabet coordinates are the signed-weight charge, signed-digit charge and the two shifted input bits. This automaton applies the literal arithmetic operations without restricting its state carrier to the finite table."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basepathrealization-base-path-realization"),
            DeclarationHandle.Create(Prefix + "base_path_realization"), H("Every arithmetic path is in the finite graph"),
            StatementSource.FromAuthor(RealizationFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every source-to-flushed-state path has an indexed path with the identical edge labels and identical initial and final state components. The output violation flag chooses one of the two acceptance modes. All seven source rows and all possible successors of each of the 1492 rows are checked, so path induction covers arbitrary finite lengths. This assertion lifts arithmetic paths; deriving an arithmetic path from a palindrome cut is a separate condition."))), DescribeRole.Theorem))));
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


    private static Formula State() => ListOf(Z());
    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula RawFormula()
    {
        var start = Seq(OpenBrace,V("s"),Colon,State(),Sp,Mid,Sp,Mem(V("s"),V("initialStates")),CloseBrace);
        var step = Lam("s",State(),Lam("a",Alphabet(),
            Seq(OpenBrace,V("t"),Colon,State(),Sp,Mid,Sp,
                Mem(Tuple(V("t"),V("a")),Call("baseSuccessors",V("s"))),CloseBrace)));
        var accept = Seq(OpenBrace,V("t"),Colon,State(),Sp,Mid,Sp,
            Eqn(Call("baseTerminal",V("t")),V("true")),CloseBrace);
        return Disp(Eqn(V("baseRawAutomaton"),Call("NFAmk",step,start,accept)));
    }
    private static Formula RealizationFormula()
    {
        var raw = V("baseRawAutomaton");
        var graph = Call("baseAutomaton",V("charge"));
        var body = And(Mem(V("i"),Call("start",graph)),Mem(V("k"),Call("accept",graph)),
            Eqn(Call("fst",Call("baseTable",Call("val",V("i")))),V("s")),
            Eqn(Call("fst",Call("baseTable",Call("val",V("k")))),V("t")),
            Call("Nonempty",Call("Path",graph,V("i"),V("k"),V("xs"))));
        body = Ex("charge",Ty("Bool"),Ex("i",Call("Fin",D(1,4,9,2)),Ex("k",Call("Fin",D(1,4,9,2)),body)));
        body = Imp(Call("Nonempty",Call("Path",raw,V("s"),V("t"),V("xs"))),body);
        body = Imp(And(Mem(V("s"),Call("start",raw)),Mem(V("t"),Call("accept",raw))),body);
        return Disp(All("s",State(),All("t",State(),All("xs",ListOf(Alphabet()),body))));
    }
}
