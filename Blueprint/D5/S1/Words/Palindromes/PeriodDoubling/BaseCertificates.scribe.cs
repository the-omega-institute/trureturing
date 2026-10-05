using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fully reconstructed finite graph has exact integer bounds on every accepted run.", H("Concrete Period-Doubling Transducer Potentials"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basecertificates-basesuccessors"),
            DeclarationHandle.Create(Prefix + "baseSuccessors"), H("All literal arithmetic successors"),
            StatementSource.FromAuthor(SuccessorsFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For each of the four pairs of binary input bits, the relation transition supplies every allowed next relation state. baseNext adds the rounded-half carries, emits signed digits, updates the first and latest nonzero signs, and rejects an opposite input digit two positions later. The remaining components record the output violation flag and the two edge charges."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-initialstates"),
            DeclarationHandle.Create(Prefix + "initialStates"), H("The seven arithmetic source states"),
            StatementSource.FromAuthor(InitialFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The two lowest input bits give the fixed endpoint parities and initial rounded-half carries. Equal bits start the even-cut relation; different bits start A and B, with the flushed relation additionally available for the pair (1,0). All sign, previous-bit, addition-carry and violation components start at zero."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-basetable"),
            DeclarationHandle.Create(Prefix + "baseTable"), H("The complete concrete graph and two potentials"),
            StatementSource.FromAuthor(TableFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For indices 0 through 1491 the function contains 1492 literal rows. Each row consists of its 19 integer state components, a complete list of edges (target, f, q, input bit, output bit), and the optional class and charge potentials. Lookup outside that range returns the final row; the automaton uses Fin 1492, so its runs never use that fallback."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-baseoffset"),
            DeclarationHandle.Create(Prefix + "baseOffset"), H("The final parity and lowest-sign correction"),
            StatementSource.FromAuthor(OffsetFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("getD(getElemOption(s,k),0) reads a state component with default zero. Components 2 and 3 contain the two fixed endpoint parities; 14 and 15 contain their lowest nonzero signs. The formula is precisely the difference of the two final corrections."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-baseterminal"),
            DeclarationHandle.Create(Prefix + "baseTerminal"), H("Flushed relation and arithmetic state"),
            StatementSource.FromAuthor(TerminalFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A state is terminal precisely when its relation component is zero and all six arithmetic carry and previous-bit components at indices 4 through 9 are zero. Boolean beq and andBool denote equality testing and Boolean conjunction."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-baseautomaton"),
            DeclarationHandle.Create(Prefix + "baseAutomaton"), H("The graph with selected terminal states"),
            StatementSource.FromAuthor(AutomatonFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There are seven source indices, 0 through 6. Every edge is the literal row entry. A terminal state has relation component zero and vanishing arithmetic components 4 through 9. The last component selects valid outputs for the charge bound and invalid outputs for the class bound. The four input coordinates are f, q, n-bit, j-bit."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-base-accepted-bound"),
            DeclarationHandle.Create(Prefix + "base_accepted_bound"), H("The concrete zero and three bounds"),
            StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The complete row checks reconstruct every possible transition, enforce in-range successor indices, verify the source and goal conditions, and check reverse-closed integer potential inequalities. Kernel reduction checks 24 blocks of at most 64 rows in both modes. The partial-potential path theorem then applies to arbitrary finite accepted runs. This statement concerns graph paths; identifying such paths with actual integer palindrome cuts requires a separate arithmetic bridge."))), DescribeRole.Theorem))));

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
    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula Entry(Formula s, int k) => Call("getD", Call("getElemOption", s, new Formula.Number(k)), D(0));
    private static Formula Bits() => Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
    private static Formula IntList(params Formula[] xs) =>
        Seq(OpenBracket, xs.Skip(1).Aggregate(xs[0], (a,b) => Seq(a,Comma,Sp,b)), CloseBracket);
    private static Formula SuccessorsFormula()
    {
        var body = Call("filterMap", Call("baseNext", V("s"), V("n"), V("j")),
            Call("relNext", Entry(V("s"),0), V("n"), V("j")));
        body = Call("flatMap", Lam("j", Z(), body), Bits());
        body = Call("flatMap", Lam("n", Z(), body), Bits());
        return Disp(All("s", State(), Eqn(Call("baseSuccessors",V("s")),body)));
    }
    private static Formula InitialFormula()
    {
        var modes = Ite(Eqn(V("n"),V("j")),IntList(D(6)),
            Ite(LtF(V("j"),V("n")),IntList(D(1),D(2),D(0)),IntList(D(1),D(2))));
        var state = IntList(V("r"),D(1),V("n"),V("j"),V("n"),V("j"),
            D(0),D(0),D(0),D(0),D(0),D(0),D(0),D(0),D(0),D(0),D(0),D(0),D(0));
        var body = Call("map",Lam("r",Z(),state),modes);
        body = Call("flatMap",Lam("j",Z(),body),Bits());
        body = Call("flatMap",Lam("n",Z(),body),Bits());
        return Disp(Eqn(V("initialStates"),body));
    }
    private static Formula TableFormula() => Disp(All("i", N(), Seq(Call("baseTable", V("i")), Colon,
        Product(State(), ListOf(Product(N(), Z(), Z(), Z(), Z())), Call("Option", Z()), Call("Option", Z())))));
    private static Formula OffsetFormula()
    {
        var s = V("s");
        var output = Ite(LtF(Entry(s,15), D(0)), Sub(D(1), Entry(s,3)), Entry(s,3));
        var input = Ite(LtF(Entry(s,14), D(0)), Sub(D(1), Entry(s,2)), Entry(s,2));
        return Disp(All("s", State(), Eqn(Call("baseOffset", s), Sub(output, input))));
    }
    private static Formula TerminalFormula()
    {
        var indices = Seq(OpenBracket, D(4), Comma, D(5), Comma, D(6), Comma,
            D(7), Comma, D(8), Comma, D(9), CloseBracket);
        var all = Call("all", Lam("k", N(), Call("beq", Call("getD", Call("getElemOption", V("s"), V("k")), D(0)), D(0))), indices);
        return Disp(All("s", State(), Eqn(Call("baseTerminal", V("s")),
            Call("andBool", Call("beq", Entry(V("s"),0), D(0)), all))));
    }
    private static Formula AutomatonFormula()
    {
        var row = Call("baseTable", Call("val", V("i")));
        var sources = Seq(OpenBrace, V("i"), Colon, Call("Fin", D(1,4,9,2)), Sp, Mid, Sp,
            Call("contains", Seq(OpenBracket, D(0), Comma, D(1), Comma, D(2), Comma, D(3), Comma, D(4), Comma, D(5), Comma, D(6), CloseBracket), Call("val", V("i"))), CloseBrace);
        var successors = Seq(OpenBrace, V("j"), Colon, Call("Fin", D(1,4,9,2)), Sp, Mid, Sp,
            Mem(Tuple(Call("val", V("j")), V("a")), Call("edges", row)), CloseBrace);
        var step = Lam("i", Call("Fin", D(1,4,9,2)), Lam("a", Alphabet(), successors));
        var accepted = Seq(OpenBrace, V("i"), Colon, Call("Fin", D(1,4,9,2)), Sp, Mid, Sp,
            And(Call("baseTerminal", Call("state", row)),
                Eqn(Entry(Call("state", row),18), Ite(V("charge"), D(0), D(1)))), CloseBrace);
        return Disp(All("charge", Ty("Bool"), Eqn(Call("baseAutomaton", V("charge")),
            Call("NFAmk", step, sources, accepted))));
    }
    private static Formula BoundFormula()
    {
        var automaton = Call("baseAutomaton", V("charge"));
        var cost = Seq(LambdaLower, Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp,
            V("a"), Colon, Alphabet(), Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp, Mapsto, Sp,
            Add(Mul(Ite(V("charge"), D(3), D(1)), Call("fst", V("a"))),
                Ite(V("charge"), Call("fst", Call("snd", V("a"))), D(0))));
        var offset = Ite(V("charge"), Call("baseOffset", Call("state", Call("baseTable", Call("val", V("t"))))), D(0));
        var bound = LeF(Add(Call("pathCharge", cost, V("p")), offset), Ite(V("charge"), D(3), D(0)));
        var assumptions = And(Mem(V("s"), Call("start", automaton)), Mem(V("t"), Call("accept", automaton)));
        var body = All("p", Call("Path", automaton, V("s"), V("t"), V("xs")), bound);
        body = Imp(assumptions, body);
        body = All("xs", ListOf(Alphabet()), body);
        body = All("t", Call("Fin", D(1,4,9,2)), body);
        body = All("s", Call("Fin", D(1,4,9,2)), body);
        return Disp(All("charge", Ty("Bool"), body));
    }

}
