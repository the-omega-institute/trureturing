using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseCertificatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fully reconstructed finite graph has exact integer bounds on every accepted run.", H("Concrete Period-Doubling Transducer Potentials"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basecertificates-relnext"),
            DeclarationHandle.Create(Prefix + "relNext"), H("The nine relation-state transitions"),
            StatementSource.FromAuthor(RelationFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("State 0 reads equal higher bits. State 1 reads complementary bits and may stop at (1,0). State 2 reads complementary lower bits, then one equal skipped bit to state 3. States 3,4,5 require a positive odd run of (0,1) before (1,0). States 6,7,8 impose the corresponding even-cut parity restriction. Inputs outside these nine relation states have no successors."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-basenext"),
            DeclarationHandle.Create(Prefix + "baseNext"), H("The literal arithmetic update"),
            StatementSource.FromAuthor(NextFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The update adds the endpoint-parity carries to the next binary bits, divides by two for the new carries, adds each rounded-half bit to its preceding bit and addition carry, and subtracts that bit from the resulting remainder to emit a signed digit. It rejects an input digit opposite to the digit two positions earlier. Otherwise it returns the full 19-component state and the label (f,q,n,j). div and mod here are Euclidean integer quotient and remainder. Boolean tests are embedded in the integers by toNat followed by cast."))), DescribeRole.Definition),
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
            Blocks(Paragraph(Text("Optional lookup reads a state component with default zero. Components 2 and 3 contain the two fixed endpoint parities; 14 and 15 contain their lowest nonzero signs. The formula is precisely the difference of the two final corrections."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-baseterminal"),
            DeclarationHandle.Create(Prefix + "baseTerminal"), H("Flushed relation and arithmetic state"),
            StatementSource.FromAuthor(TerminalFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A state is terminal precisely when its relation component is zero and all six arithmetic carry and previous-bit components at indices 4 through 9 are zero."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-baseautomaton"),
            DeclarationHandle.Create(Prefix + "baseAutomaton"), H("The graph with selected terminal states"),
            StatementSource.FromAuthor(AutomatonFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("There are seven source indices, 0 through 6. Every edge is the literal row entry. A terminal state has relation component zero and vanishing arithmetic components 4 through 9. The last component selects valid outputs for the charge bound and invalid outputs for the class bound. The four input coordinates are f, q, n-bit, j-bit."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basecertificates-base-accepted-bound"),
            DeclarationHandle.Create(Prefix + "base_accepted_bound"), H("The concrete zero and three bounds"),
            StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The complete row checks reconstruct every possible transition, enforce in-range successor indices, verify the source and goal conditions, and check reverse-closed integer potential inequalities. Kernel reduction checks 24 blocks of at most 64 rows in both modes. The partial-potential path theorem then applies to arbitrary finite accepted runs. This statement concerns graph paths; identifying such paths with actual integer palindrome cuts requires a separate arithmetic bridge."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula BooleanEq(Formula a, Formula b) =>
        Seq(Open, a, Sp, Eq, Eq, Sp, b, Close);
    private static Formula BooleanNe(Formula a, Formula b) =>
        Seq(Open, a, Sp, Bang, Eq, Sp, b, Close);

    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));

    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

    private static Formula NfaMk(params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V("NFA"), Dot, V("mk"))), [.. args]);
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
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));


    private static Formula State() => ListOf(Z());
    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula Entry(Formula s, int k) => Call("getD", OptionalIndex(s, new Formula.Number(k)), D(0));
    private static Formula Bits() => Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
    private static Formula IntList(params Formula[] xs) =>
        Seq(OpenBracket, xs.Skip(1).Aggregate(xs[0], (a,b) => Seq(a,Comma,Sp,b)), CloseBracket);
    private static Formula RelationFormula()
    {
        var r=V("r");var n=V("n");var j=V("j");var empty=ListNil();
        var same=Eqn(n,j);var up=And(Eqn(n,D(0)),Eqn(j,D(1)));var top=And(Eqn(n,D(1)),Eqn(j,D(0)));
        Formula body=empty;
        body=Ite(Eqn(r,D(8)),Ite(up,IntList(D(7)),empty),body);
        body=Ite(Eqn(r,D(7)),Ite(top,IntList(D(0)),Ite(up,IntList(D(8)),empty)),body);
        body=Ite(Eqn(r,D(6)),Ite(up,IntList(D(7)),empty),body);
        body=Ite(Eqn(r,D(5)),Ite(up,IntList(D(4)),empty),body);
        body=Ite(Eqn(r,D(4)),Ite(top,IntList(D(0)),Ite(up,IntList(D(5)),empty)),body);
        body=Ite(Eqn(r,D(3)),Ite(up,IntList(D(4)),empty),body);
        body=Ite(Eqn(r,D(2)),Ite(same,IntList(D(3)),IntList(D(2))),body);
        body=Ite(Eqn(r,D(1)),Ite(same,empty,Ite(top,IntList(D(1),D(0)),IntList(D(1)))),body);
        body=Ite(Eqn(r,D(0)),Ite(same,IntList(D(0)),empty),body);
        return Disp(All("r",Z(),All("n",Z(),All("j",Z(),Eqn(Call("relNext",r,n,j),body)))));
    }
    private static Formula NextFormula()
    {
        var s=V("s");var n=V("n");var j=V("j");var r=V("r");
        var bindings=new List<(string Name,Formula Value)>();
        Formula BindValue(string name,Formula value)
        {
            bindings.Add((name,value));
            return V(name);
        }
        var nv=BindValue("nv",Add(n,Entry(s,4)));var jv=BindValue("jv",Add(j,Entry(s,5)));
        var xn=BindValue("xn",Call("mod",nv,D(2)));var xj=BindValue("xj",Call("mod",jv,D(2)));
        var nt=BindValue("nt",Add(Add(xn,Entry(s,6)),Entry(s,8)));
        var jt=BindValue("jt",Add(Add(xj,Entry(s,7)),Entry(s,9)));
        var nd=BindValue("nd",Sub(Call("mod",nt,D(2)),xn));
        var jd=BindValue("jd",Sub(Call("mod",jt,D(2)),xj));
        Formula Indicator(Formula b) => Cast(Call("toNat",b),Z());
        Formula Cost(Formula d,int prev) => Ite(Eqn(d,D(0)),D(0),Add(Add(D(1),Mul(D(2),Entry(s,1))),
            Indicator(DottedCall("Bool", "and",BooleanNe(Entry(s,prev), D(0)),BooleanNe(Entry(s,prev), d)))));
        var f=Sub(Indicator(BooleanNe(nd, D(0))),Indicator(BooleanNe(jd, D(0))));
        var state=IntList(r,Sub(D(1),Entry(s,1)),Entry(s,2),Entry(s,3),
            Call("div",nv,D(2)),Call("div",jv,D(2)),xn,xj,Call("div",nt,D(2)),Call("div",jt,D(2)),
            nd,Entry(s,10),jd,Entry(s,12),Ite(Eqn(Entry(s,14),D(0)),nd,Entry(s,14)),
            Ite(Eqn(Entry(s,15),D(0)),jd,Entry(s,15)),Ite(Eqn(nd,D(0)),Entry(s,16),nd),
            Ite(Eqn(jd,D(0)),Entry(s,17),jd),Indicator(DottedCall("Bool", "or",BooleanNe(Entry(s,18), D(0)),
                BooleanEq(Mul(jd,Entry(s,13)), Call("neg",D(1))))));
        var value=Ite(Eqn(Mul(nd,Entry(s,11)),Call("neg",D(1))),Ty("none"),
            Call("some",Tuple(state,f,Sub(Cost(jd,17),Cost(nd,16)),n,j)));
        for(var i=bindings.Count-1;i>=0;i--)
        {
            var binding=bindings[i];
            value=new Formula.Apply(Seq(LambdaLower,Sp,V(binding.Name),Colon,Z(),Sp,Mapsto,Sp,value),[binding.Value]);
        }
        return Disp(All("s",State(),All("n",Z(),All("j",Z(),All("r",Z(),Eqn(Call("baseNext",s,n,j,r),value))))));
    }
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
        var all = Call("all", Lam("k", N(), BooleanEq(Call("getD", OptionalIndex(V("s"), V("k")), D(0)), D(0))), indices);
        return Disp(All("s", State(), Eqn(Call("baseTerminal", V("s")),
            DottedCall("Bool", "and", BooleanEq(Entry(V("s"),0), D(0)), all))));
    }
    private static Formula AutomatonFormula()
    {
        var row = Call("baseTable", Call("val", V("i")));
        var sources = Seq(OpenBrace, V("i"), Colon, Call("Fin", D(1,4,9,2)), Sp, Mid, Sp,
            Call("contains", new Formula.Apply(Seq(V("List"), Dot, V("range")), [D(7)]), Call("val", V("i"))), CloseBrace);
        var successors = Seq(OpenBrace, V("j"), Colon, Call("Fin", D(1,4,9,2)), Sp, Mid, Sp,
            Mem(Tuple(Call("val", V("j")), V("a")), Call("fst", Call("snd", row))), CloseBrace);
        var step = Lam("i", Call("Fin", D(1,4,9,2)), Lam("a", Alphabet(), successors));
        var accepted = Seq(OpenBrace, V("i"), Colon, Call("Fin", D(1,4,9,2)), Sp, Mid, Sp,
            And(Call("baseTerminal", Call("fst", row)),
                Eqn(Entry(Call("fst", row),18), Ite(V("charge"), D(0), D(1)))), CloseBrace);
        return Disp(All("charge", Ty("Bool"), Eqn(Call("baseAutomaton", V("charge")),
            NfaMk(step, sources, accepted))));
    }
    private static Formula BoundFormula()
    {
        var automaton = Call("baseAutomaton", V("charge"));
        var cost = Seq(LambdaLower, Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp,
            V("a"), Colon, Alphabet(), Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp, Mapsto, Sp,
            Add(Mul(Ite(V("charge"), D(3), D(1)), Call("fst", V("a"))),
                Ite(V("charge"), Call("fst", Call("snd", V("a"))), D(0))));
        var offset = Ite(V("charge"), Call("baseOffset", Call("fst", Call("baseTable", Call("val", V("t"))))), D(0));
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
