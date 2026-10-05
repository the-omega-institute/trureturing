using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedPrefixCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every accepted marked-prefix path satisfies its shape or charge bound.", H("Marked-Prefix Potential Certificates"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-prefixtable"),
            DeclarationHandle.Create(Prefix + "prefixTable"), H("The complete marked-prefix product graph"),
            StatementSource.FromAuthor(TableFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Indices zero through 4261 list the eight-component marker state, every labelled product edge, and the two optional potentials. The components are the base-state index, marker phase, flip flag, marker parity, retained flag, input phase, output phase and bad flag. Outside this range the final row is returned; all paths use Fin 4262."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-prefixoffset"),
            DeclarationHandle.Create(Prefix + "prefixOffset"), H("The terminal marked-prefix charge correction"),
            StatementSource.FromAuthor(OffsetFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The terminal correction adds the base charge offset to the contribution of the retained or removed lowest marked digit. The marker parity assigns weight one or three. The operator getD reads an optional list entry with default zero, toNat converts an integer index to a natural number, and bne is Boolean inequality."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-prefixautomaton"),
            DeclarationHandle.Create(Prefix + "prefixAutomaton"), H("The marked-prefix automata"),
            StatementSource.FromAuthor(AutomatonFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Both modes start at indices zero through four and use every listed product edge. Acceptance requires the marker phase to be four, a terminal base state, and bad flag zero for the charge mode or one for the shape mode. The Boolean parameter chooses the mode."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-prefix-accepted-bound"),
            DeclarationHandle.Create(Prefix + "prefix_accepted_bound"), H("Bounds on every accepted marked-prefix path"),
            StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The shape mode bounds total f charge by zero. The charge mode bounds five times f charge plus q charge and the terminal marked-prefix correction by five. The potentials telescope along paths of arbitrary length. Identifying these graph labels with integer cuts and signed-digit charges is a separate arithmetic obligation."))), DescribeRole.Theorem))));

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


    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula TableFormula() => Disp(All("i", N(), Seq(Call("prefixTable", V("i")), Colon,
        Product(ListOf(Z()), ListOf(Product(N(), Z(), Z(), Z(), Z())), Call("Option", Z()), Call("Option", Z())))));
    private static Formula Entry(Formula f, int i) => Call("getD", Call("getElemOption", f, new Formula.Number(i)), D(0));
    private static Formula OffsetFormula()
    {
        var full = V("full");
        var w = Add(D(1), Mul(D(2), Entry(full, 3)));
        var state = Call("fst", Call("baseTable", Call("toNat", Entry(full, 0))));
        var correction = Ite(Call("bne", Entry(full, 4), D(0)),
            Mul(Parenthesized(Sub(w, D(1))), Parenthesized(Sub(Entry(full, 6), Entry(full, 5)))), Add(w, D(1)));
        return Disp(All("full", ListOf(Z()), Eqn(Call("prefixOffset", full), Add(Call("baseOffset", state), correction))));
    }
    private static Formula AutomatonFormula()
    {
        var fin = Call("Fin", D(4,2,6,2));
        var state = Call("fst", Call("prefixTable", Call("val", V("i"))));
        var sources = Seq(OpenBrace, V("i"), Colon, fin, Sp, Mid, Sp, LtF(Call("val", V("i")), D(5)), CloseBrace);
        var successors = Seq(OpenBrace, V("j"), Colon, fin, Sp, Mid, Sp,
            Mem(Tuple(Call("val", V("j")), V("a")), Call("edges", Call("prefixTable", Call("val", V("i"))))), CloseBrace);
        var baseIndex = Call("toNat", Entry(state, 0));
        var terminal = Call("andBool", Call("andBool", Call("beq", Entry(state, 1), D(4)),
            Call("baseTerminal", Call("fst", Call("baseTable", baseIndex)))),
            Call("beq", Entry(state, 7), Ite(V("charge"), D(0), D(1))));
        var accepted = Seq(OpenBrace, V("i"), Colon, fin, Sp, Mid, Sp, terminal, CloseBrace);
        return Disp(All("charge", Ty("Bool"), Eqn(Call("prefixAutomaton", V("charge")),
            Call("NFAmk", Lam("i", fin, Lam("a", Alphabet(), successors)), sources, accepted))));
    }
    private static Formula BoundFormula()
    {
        var fin = Call("Fin", D(4,2,6,2));
        var automaton = Call("prefixAutomaton", V("charge"));
        var weight = Add(Mul(Ite(V("charge"), D(5), D(1)), Call("fst", V("a"))),
            Ite(V("charge"), Call("fst", Call("snd", V("a"))), D(0)));
        var cost = Seq(LambdaLower, Sp, OpenBracket, fin, CloseBracket, Sp,
            V("a"), Colon, Alphabet(), Sp, OpenBracket, fin, CloseBracket, Sp, Mapsto, Sp, weight);
        var state = Call("fst", Call("prefixTable", Call("val", V("t"))));
        var bound = LeF(Add(Call("pathCharge", cost, V("p")), Ite(V("charge"), Call("prefixOffset", state), D(0))),
            Ite(V("charge"), D(5), D(0)));
        var body = All("p", Call("Path", automaton, V("s"), V("t"), V("xs")), bound);
        body = Imp(And(Mem(V("s"), Call("start", automaton)), Mem(V("t"), Call("accept", automaton))), body);
        return Disp(All("charge", Ty("Bool"), All("s", fin, All("t", fin, All("xs", ListOf(Alphabet()), body)))));
    }

}
