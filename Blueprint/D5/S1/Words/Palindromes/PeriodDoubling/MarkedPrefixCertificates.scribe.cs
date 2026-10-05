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
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-nextmarker"),
            DeclarationHandle.Create(Prefix + "nextMarker"), H("The literal marker-state update"),
            StatementSource.FromAuthor(NextMarkerFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The marker modes are zero before selection, one and two while reading the two separating zeros, three before the next positive coefficient, and four during the final zeros. The formula displays the complete branch update. Each Boolean flag is converted to a natural number and then to an integer for storage."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-successors"),
            DeclarationHandle.Create(Prefix + "successors"), H("Literal marker transitions"),
            StatementSource.FromAuthor(SuccessorFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every base edge is passed to the marker-state transition nextMarker. The unmarked phase may remain unmarked or select a positive digit with two preceding zeros; marked phases read two zeros and the next positive digit, and phase four flushes leading zeros. Output-class violations are excluded and the flip, phase, parity, retention and bad flags follow the literal marker update."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-prefixrealizationrowcheck"),
            DeclarationHandle.Create(Prefix + "prefixRealizationRowCheck"), H("The successor-completeness checker"),
            StatementSource.FromAuthor(RealizationRowFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The checker compares every literal marker successor against the decoded indexed edge list, then verifies every target index is below 4262. It checks transition completeness independently of the potential inequalities."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-prefixrealizationblockcheck"),
            DeclarationHandle.Create(Prefix + "prefixRealizationBlockCheck"), H("Bounded reconstruction windows"),
            StatementSource.FromAuthor(RealizationBlockFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Each window checks count consecutive rows starting at start. Separate kernel certificates cover all windows, and their union covers every marker state."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixcertificates-terminal"),
            DeclarationHandle.Create(Prefix + "terminal"), H("Completed marker and terminal base state"),
            StatementSource.FromAuthor(TerminalFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The terminal test requires marker phase four and a terminal underlying base state. The bad flag is tested separately by each automaton's acceptance predicate. Option lookups use default zero and toNat converts the stored integer index to a natural number."))), DescribeRole.Definition),
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
    private static Formula BooleanEq(Formula a, Formula b) =>
        Parenthesized(Seq(a, Sp, Eq, Eq, Sp, b));
    private static Formula BooleanNe(Formula a, Formula b) =>
        Parenthesized(Seq(a, Sp, Bang, Eq, Sp, b));

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
    private static Formula ListNil() => Seq(
        OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));


    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula TableFormula() => Disp(All("i", N(), Seq(Call("prefixTable", V("i")), Colon,
        Product(ListOf(Z()), ListOf(Product(N(), Z(), Z(), Z(), Z())), Call("Option", Z()), Call("Option", Z())))));
    private static Formula Entry(Formula f, int i) => Call("getD", OptionalIndex(f, new Formula.Number(i)), D(0));
    private static Formula NextMarkerFormula()
    {
        var full=V("full"); var e=V("e");
        var edgeType=Product(N(),Z(),Z(),Z(),Z());
        var old=Call("fst",Call("baseTable",Call("toNat",Entry(full,0))));
        var next=Call("fst",Call("baseTable",Call("fst",e)));
        var oldValue=old; var nextValue=next; old=V("old"); next=V("next");
        var nd=Entry(next,10); var jd=Entry(next,12); var m=Entry(full,1);
        var flip=BooleanNe(Entry(full,2), D(0)); var parity=Entry(full,3);
        var keep=Entry(full,4); var ni=Entry(full,5); var nj=Entry(full,6);
        var bad=BooleanNe(Entry(full,7), D(0));
        var bindings=new (string Name,Formula Type,Formula Value)[] {
            ("old",ListOf(Z()),oldValue),("next",ListOf(Z()),nextValue),
            ("nd",Z(),nd),("jd",Z(),jd),("m",Z(),m),("flip",Ty("Bool"),flip),
            ("parity",Z(),parity),("keep",Z(),keep),("ni",Z(),ni),("nj",Z(),nj),("bad",Ty("Bool"),bad)};
        nd=V("nd");jd=V("jd");m=V("m");flip=V("flip");parity=V("parity");
        keep=V("keep");ni=V("ni");nj=V("nj");bad=V("bad");
        Formula AndB(Formula a,Formula b) => DottedCall("Bool", "and",a,b);
        Formula OrB(Formula a,Formula b) => DottedCall("Bool", "or",a,b);
        Formula NotB(Formula a) => DottedCall("Bool", "not",a);
        Formula Beq(Formula a,Formula b) => BooleanEq(a, b);
        Formula Bne(Formula a,Formula b) => BooleanNe(a, b);
        Formula Flag(Formula a) => Cast(Call("toNat",a),Z());
        Formula Items(params Formula[] items) => Seq(
            OpenBracket,
            items.Skip(1).Aggregate(items[0],(a,b)=>Seq(a,Comma,Sp,b)),CloseBracket);
        var finishValue=Seq(LambdaLower,Sp,V("state"),Colon,ListOf(Z()),Sp,Mapsto,Sp,
            Tuple(V("state"),Call("fst",Call("snd",e)),Call("fst",Call("snd",Call("snd",e))),
                Call("fst",Call("snd",Call("snd",Call("snd",e)))),
                Call("snd",Call("snd",Call("snd",Call("snd",e))))));
        var finishType=new Formula.TypeArrow(ListOf(Z()),Product(ListOf(Z()),Z(),Z(),Z(),Z()));
        Formula Finish(Formula mode,Formula fl,Formula par,Formula kp,Formula an,Formula aj,Formula bd) =>
            new Formula.Apply(V("finish"),[Items(Cast(Call("fst",e),Z()),mode,fl,par,kp,an,aj,bd)]);
        var unmarkedValue=Finish(D(0),Flag(AndB(flip,Beq(Add(nd,jd),D(0)))),D(0),D(0),D(0),D(0),D(0));
        var unmarked=V("unmarked");
        var markedBindings=new List<(string Name,Formula Value)>();
        Formula BindFlag(string name,Formula value)
        {
            markedBindings.Add((name,value));
            return V(name);
        }
        var an=BindFlag("an",OrB(Call("decide",LtF(Entry(old,16),D(0))),AndB(Beq(Entry(old,16),D(0)),Beq(Entry(old,2),D(1)))));
        var aj=BindFlag("aj",OrB(Call("decide",LtF(Entry(old,17),D(0))),AndB(Beq(Entry(old,17),D(0)),Beq(Entry(old,3),D(1)))));
        var kp=BindFlag("kp",Beq(jd,D(1)));
        var bd=BindFlag("bd",OrB(OrB(OrB(Bne(Entry(old,12),D(0)),Bne(Entry(old,13),D(0))),AndB(Bne(jd,D(0)),Bne(jd,D(1)))),
            AndB(NotB(kp),OrB(OrB(NotB(an),aj),NotB(flip)))));
        Formula marked=Finish(D(1),Flag(flip),Entry(old,1),Flag(kp),Flag(an),Flag(aj),Flag(bd));
        for(var i=markedBindings.Count-1;i>=0;i--)
        {
            var binding=markedBindings[i];
            marked=new Formula.Apply(Parenthesized(Seq(LambdaLower,Sp,V(binding.Name),Colon,Ty("Bool"),Sp,Mapsto,Sp,marked)),[binding.Value]);
        }
        var unselected=Ite(And(Eqn(nd,D(1)),Eqn(Entry(old,10),D(0)),Eqn(Entry(old,11),D(0))),Items(unmarked,marked),Items(unmarked));
        unselected=new Formula.Apply(Parenthesized(Seq(LambdaLower,Sp,V("unmarked"),Colon,
            Product(ListOf(Z()),Z(),Z(),Z(),Z()),Sp,Mapsto,Sp,unselected)),[unmarkedValue]);
        var middle=Ite(Bne(nd,D(0)),ListNil(),Items(Finish(Add(m,D(1)),Flag(flip),parity,keep,ni,nj,Flag(OrB(bad,Bne(nd,jd))))));
        var third=Ite(AndB(Bne(nd,D(0)),Bne(nd,D(1))),ListNil(),
            Items(Finish(Ite(Eqn(nd,D(1)),D(1),D(4)),Flag(flip),parity,keep,ni,nj,Flag(OrB(bad,Bne(nd,jd))))));
        var final=Ite(Bne(nd,D(0)),ListNil(),Items(Finish(D(4),Flag(flip),parity,keep,ni,nj,Flag(OrB(bad,Bne(nd,jd))))));
        var update=Ite(Bne(Entry(next,18),D(0)),ListNil(),Ite(Eqn(m,D(0)),unselected,
            Ite(new Formula.Logic(Eqn(m,D(1)),FormulaLogicOperator.Or,Eqn(m,D(2))),middle,Ite(Eqn(m,D(3)),third,final))));
        update=new Formula.Apply(Parenthesized(Seq(LambdaLower,Sp,V("finish"),Colon,finishType,Sp,Mapsto,Sp,update)),[finishValue]);
        for(var i=bindings.Length-1;i>=0;i--)
        {
            var binding=bindings[i];
            update=new Formula.Apply(Parenthesized(Seq(LambdaLower,Sp,V(binding.Name),Colon,binding.Type,Sp,Mapsto,Sp,update)),[binding.Value]);
        }
        return Disp(All("full",ListOf(Z()),All("e",edgeType,Eqn(Call("nextMarker",full,e),update))));
    }
    private static Formula SuccessorFormula()
    {
        var edges=Call("fst",Call("snd",Call("baseTable",Call("toNat",Entry(V("full"),0)))));
        var edgeType=Product(N(),Z(),Z(),Z(),Z());
        return Disp(All("full",ListOf(Z()),Eqn(Call("successors",V("full")),
            Call("flatMap",Lam("e",edgeType,Call("nextMarker",V("full"),V("e"))),edges))));
    }
    private static Formula RealizationRowFormula()
    {
        var row=Call("prefixTable",V("i"));
        var edges=Call("fst",Call("snd",row));
        var edgeType=Product(N(),Z(),Z(),Z(),Z());
        var decoded=Call("map",Lam("e",edgeType,Tuple(Call("fst",Call("prefixTable",Call("fst",V("e")))),Call("snd",V("e")))),edges);
        var complete=Call("all",Lam("a",Product(ListOf(Z()),Z(),Z(),Z(),Z()),Call("contains",decoded,V("a"))),Call("successors",Call("fst",row)));
        var valid=Call("all",Lam("e",edgeType,Call("decide",LtF(Call("fst",V("e")),D(4,2,6,2)))),edges);
        return Disp(All("i",N(),Eqn(Call("prefixRealizationRowCheck",V("i")),DottedCall("Bool", "and",complete,valid))));
    }
    private static Formula RealizationBlockFormula() => Disp(All("start",N(),All("count",N(),
        Eqn(Call("prefixRealizationBlockCheck",V("start"),V("count")),
            Call("all",Lam("k",N(),Call("prefixRealizationRowCheck",Add(V("start"),V("k")))),Call("range",V("count")))))));
    private static Formula TerminalFormula() => Disp(All("full",ListOf(Z()),
        Eqn(Call("terminal",V("full")),DottedCall("Bool", "and",BooleanEq(Entry(V("full"),1), D(4)),
            Call("baseTerminal",Call("fst",Call("baseTable",Call("toNat",Entry(V("full"),0)))))))));
    private static Formula OffsetFormula()
    {
        var full = V("full");
        var w = Add(D(1), Mul(D(2), Entry(full, 3)));
        var state = Call("fst", Call("baseTable", Call("toNat", Entry(full, 0))));
        var correction = Ite(BooleanNe(Entry(full, 4), D(0)),
            Mul(Parenthesized(Sub(w, D(1))), Parenthesized(Sub(Entry(full, 6), Entry(full, 5)))), Add(w, D(1)));
        return Disp(All("full", ListOf(Z()), Eqn(Call("prefixOffset", full), Add(Call("baseOffset", state), correction))));
    }
    private static Formula AutomatonFormula()
    {
        var fin = Call("Fin", D(4,2,6,2));
        var state = Call("fst", Call("prefixTable", Call("val", V("i"))));
        var sources = Seq(
            OpenBrace, V("i"), Colon, fin, Sp, Mid, Sp, LtF(Call("val", V("i")), D(5)), CloseBrace);
        var successors = Seq(
            OpenBrace, V("j"), Colon, fin, Sp, Mid, Sp,
            Mem(Tuple(Call("val", V("j")), V("a")), Call("fst", Call("snd", Call("prefixTable", Call("val", V("i")))))), CloseBrace);
        var baseIndex = Call("toNat", Entry(state, 0));
        var terminal = DottedCall("Bool", "and", DottedCall("Bool", "and", BooleanEq(Entry(state, 1), D(4)),
            Call("baseTerminal", Call("fst", Call("baseTable", baseIndex)))),
            BooleanEq(Entry(state, 7), Ite(V("charge"), D(0), D(1))));
        var accepted = Seq(
            OpenBrace, V("i"), Colon, fin, Sp, Mid, Sp, terminal, CloseBrace);
        return Disp(All("charge", Ty("Bool"), Eqn(Call("prefixAutomaton", V("charge")),
            NfaMk(Lam("i", fin, Lam("a", Alphabet(), successors)), sources, accepted))));
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
