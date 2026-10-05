using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseChargeArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseChargeArithmetic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The q weights count position charges and successive nonzero-sign changes exactly.", H("Arithmetic Meaning of the Signed-Digit Charge"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basechargearithmetic-digitstreamcharge"),
            DeclarationHandle.Create(Prefix + "digitStreamCharge"), H("Signed-stream charge with incoming memory"),
            StatementSource.FromAuthor(ChargeFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A zero digit contributes nothing and preserves the previous nonzero sign. A nonzero digit contributes 1 + 2 par and an extra unit when its sign differs from a nonzero incoming sign. The parity switches after every digit. This is the position-weight and sign-change part of Q, without its terminal endpoint-parity correction. The Boolean indicators are converted to natural numbers and then embedded in the integers."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basechargearithmetic-chargerowcheck"),
            DeclarationHandle.Create(Prefix + "chargeRowCheck"), H("Literal last-sign and charge updates"),
            StatementSource.FromAuthor(RowFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Each base edge flips the position parity, updates each most recent nonzero sign exactly when a nonzero digit is emitted, and gives q the difference of the two literal position-and-sign-change contributions."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-basechargearithmetic-digit-stream-charge-formula"),
            DeclarationHandle.Create(Prefix + "digit_stream_charge_formula"), H("The literal position and sign-change sum"),
            StatementSource.FromAuthor(StreamFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Enumerate the digits from natural position p and discard the zeros. The charge is the sum of 1 + 2(i mod 2) over the surviving positions, plus the number of changes between successive surviving signs, plus the change from a nonzero incoming sign to the first surviving sign. An empty nonzero list has zero incoming correction. mod is natural remainder; Option.elim is zero for none and applies the displayed function for some."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("pd-basechargearithmetic-base-path-charge-reconstruction"),
            DeclarationHandle.Create(Prefix + "base_path_charge_reconstruction"), H("q is the difference of the two stream charges"),
            StatementSource.FromAuthor(ReconstructionFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This equality holds for every finite path and either acceptance mode, without requiring its endpoints to be sources or goals. State component 1 is the current position parity; components 16 and 17 are the latest nonzero signs of the two streams. Every table edge updates these memories and carries the difference of the contributions. Path induction then reconstructs the entire charge. Components 10 and 12 of the successor state are the emitted input and output signed digits."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula BooleanNe(Formula a, Formula b) =>
        Parenthesized(Seq(a, Sp, Bang, Eq, Sp, b));

    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));
    private static Formula OptionalHead(Formula xs) =>
        Call("ite", Eqn(xs, Seq(
            OpenBracket, CloseBracket)), Call("none"),
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
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
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


    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula s, int k) => Call("getD",OptionalIndex(s,new Formula.Number(k)),D(0));
    private static Formula Contribution(Formula par, Formula previous, Formula d) =>
        Ite(Eqn(d,D(0)),D(0),Add(Add(D(1),Mul(D(2),par)),
            Cast(Call("toNat",DottedCall("Bool", "and",BooleanNe(previous, D(0)),BooleanNe(previous, d))),Z())));
    private static Formula ChargeFormula()
    {
        var par=V("par");var previous=V("previous");var d=V("d");var ds=V("ds");
        var zero=All("par",Z(),All("previous",Z(),Eqn(Call("digitStreamCharge",par,previous,ListNil()),D(0))));
        var step=Eqn(Call("digitStreamCharge",par,previous,Call("cons",d,ds)),
            Add(Contribution(par,previous,d),Call("digitStreamCharge",Sub(D(1),par),Ite(Eqn(d,D(0)),previous,d),ds)));
        step=All("par",Z(),All("previous",Z(),All("d",Z(),All("ds",ListOf(Z()),step))));
        return Disp(And(Parenthesized(zero),Parenthesized(step)));
    }
    private static Formula RowFormula()
    {
        var S=Call("fst",Call("baseTable",V("i")));
        var T=Call("fst",Call("baseTable",Call("fst",V("e"))));
        Formula EntryAt(Formula x,int k) => Call("getD",OptionalIndex(x,new Formula.Number(k)),D(0));
        var dn=EntryAt(T,10); var dj=EntryAt(T,12);
        Formula Last(Formula d,int k) => Ite(Eqn(d,D(0)),EntryAt(S,k),d);
        Formula Cost(Formula d,int k) => Ite(Eqn(d,D(0)),D(0),
            Add(Add(D(1),Mul(D(2),EntryAt(S,1))),Cast(Call("toNat",DottedCall("Bool", "and",BooleanNe(EntryAt(S,k), D(0)),BooleanNe(EntryAt(S,k), d))),Z())));
        var law=And(Eqn(EntryAt(T,1),Sub(D(1),EntryAt(S,1))),Eqn(EntryAt(T,16),Last(dn,16)),
            Eqn(EntryAt(T,17),Last(dj,17)),Eqn(Call("fst",Call("snd",Call("snd",V("e")))),Sub(Cost(dj,17),Cost(dn,16))));
        return Disp(All("i",N(),Eqn(Call("chargeRowCheck",V("i")),
            Call("all",Lam("e",Product(N(),Z(),Z(),Z(),Z()),Call("decide",law)),Call("fst",Call("snd",Call("baseTable",V("i"))))))));
    }
    private static Formula StreamFormula()
    {
        var pair=Product(Z(),N());
        var nz=Call("filter",Lam("z",pair,BooleanNe(Call("fst",V("z")), D(0))),Call("zipIdx",V("ds"),V("p")));
        var weights=Call("sum",Call("map",Lam("z",pair,Add(D(1),Mul(D(2),Call("mod",Call("snd",V("z")),D(2))))),nz));
        var flips=Call("length",Call("filter",Lam("z",Product(Parenthesized(pair),Parenthesized(pair)),
            BooleanNe(Call("fst",Call("fst",V("z"))), Call("fst",Call("snd",V("z"))))),
            Call("zip",nz,Call("tail",nz))));
        var initial=DottedCall("Option", "elim", OptionalHead(nz), D(0), Lam("z",pair,
            Cast(Call("toNat",DottedCall("Bool", "and",BooleanNe(V("previous"), D(0)),
                BooleanNe(V("previous"), Call("fst",V("z"))))),Z())));
        var body=Eqn(Call("digitStreamCharge",Cast(Call("mod",V("p"),D(2)),Z()),V("previous"),V("ds")),
            Add(Add(Cast(weights,Z()),Cast(flips,Z())),initial));
        return Disp(All("ds",ListOf(Z()),All("p",N(),All("previous",Z(),body))));
    }
    private static Formula ReconstructionFormula()
    {
        var graph=Call("baseAutomaton",V("charge"));
        var state=Call("fst",Call("baseTable",Call("val",V("s"))));
        var dsN=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,Call("Fin",D(1,4,9,2)),CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,Call("Fin",D(1,4,9,2)),Sp,Mapsto,Sp,
            Entry(Call("fst",Call("baseTable",Call("val",V("q")))),10)),V("p"));
        var dsJ=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,Call("Fin",D(1,4,9,2)),CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,Call("Fin",D(1,4,9,2)),Sp,Mapsto,Sp,
            Entry(Call("fst",Call("baseTable",Call("val",V("q")))),12)),V("p"));
        var qcost=Seq(LambdaLower,Sp,OpenBracket,Call("Fin",D(1,4,9,2)),CloseBracket,Sp,
            V("a"),Colon,Alphabet(),Sp,OpenBracket,Call("Fin",D(1,4,9,2)),CloseBracket,Sp,Mapsto,Sp,
            Call("fst",Call("snd",V("a"))));
        var body=Eqn(Call("pathCharge",qcost,V("p")),
            Sub(Call("digitStreamCharge",Entry(state,1),Entry(state,17),dsJ),
                Call("digitStreamCharge",Entry(state,1),Entry(state,16),dsN)));
        return Disp(All("charge",Ty("Bool"),All("s",Call("Fin",D(1,4,9,2)),All("t",Call("Fin",D(1,4,9,2)),
            All("xs",ListOf(Alphabet()),All("p",Call("Path",graph,V("s"),V("t"),V("xs")),body))))));
    }
}
