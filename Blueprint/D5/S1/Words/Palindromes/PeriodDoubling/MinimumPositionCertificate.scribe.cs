using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MinimumPositionCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No accepted escape path in the complete lifted graph has positive f weight.", H("Lowest Signed-Digit Position Certificate"), Blocks(
        Describe.Lean(DescribeId.Create("pd-minimumpositioncertificate-minimumtable"),
            DeclarationHandle.Create(Prefix + "minimumTable"), H("The complete lifted lowest-position graph"),
            StatementSource.FromAuthor(TableFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Indices zero through 1709 list the base-state index, the persistent lowest-position escape flag, every lifted edge, and the optional integer potential. Base states are the 1492 states of baseTable. Outside this range lookup returns the final row; all runs use Fin 1710."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-minimumpositioncertificate-successors"),
            DeclarationHandle.Create(Prefix + "successors"), H("The literal lowest-position flag update"),
            StatementSource.FromAuthor(SuccessorsFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every outgoing base edge, preserve its four labels and attach the persistent flag. The flag is set when the first-input-sign memory is still zero, the newly emitted input digit is zero, and the newly emitted output digit is nonzero. This is the arithmetic update used both by the potential checker and by complete path realization."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-minimumpositioncertificate-minimumautomaton"),
            DeclarationHandle.Create(Prefix + "minimumAutomaton"), H("The lowest-position escape automaton"),
            StatementSource.FromAuthor(AutomatonFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Its seven source indices are zero through six. Edges are literal table entries. A terminal state has the escape flag true and its base state is accepted in the valid-output mode of baseAutomaton. The flag becomes true when an output nonzero digit appears before the first input nonzero digit."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-minimumpositioncertificate-minimum-accepted-bound"),
            DeclarationHandle.Create(Prefix + "minimum_accepted_bound"), H("The lowest-position escape bound"),
            StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Kernel reduction checks all 1710 rows, verifies complete lifting of the base graph, and proves the source, goal and reverse-closed potential inequalities. Every accepting run has total f charge at most zero. This graph statement requires an arithmetic identification of f with the signed-weight difference before it can imply a statement about actual cuts."))), DescribeRole.Theorem))));

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

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));


    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula TableFormula() => Disp(All("i", N(), Seq(Call("minimumTable", V("i")), Colon,
        Product(N(), Ty("Bool"), ListOf(Product(N(), Z(), Z(), Z(), Z())), Call("Option", Z())))));
    private static Formula SuccessorsFormula()
    {
        var row=Call("minimumTable",V("i"));
        var state=Call("fst",Call("baseTable",Call("fst",row)));
        var target=Call("fst",Call("baseTable",Call("fst",V("e"))));
        Formula Entry(Formula a,int k) => Call("getD",OptionalIndex(a,new Formula.Number(k)),D(0));
        var flag=DottedCall("Bool", "or",Call("fst",Call("snd",row)),
            DottedCall("Bool", "and",DottedCall("Bool", "and",BooleanEq(Entry(state,14), D(0)),BooleanEq(Entry(target,10), D(0))),
                BooleanNe(Entry(target,12), D(0))));
        var value=Tuple(Call("fst",V("e")),flag,Call("snd",V("e")));
        var edges=Call("fst",Call("snd",Call("baseTable",Call("fst",row))));
        var body=Call("map",Seq(LambdaLower,Sp,V("e"),Colon,Product(N(),Alphabet()),Sp,Mapsto,Sp,value),edges);
        return Disp(All("i",N(),Eqn(Call("successors",V("i")),body)));
    }
    private static Formula AutomatonFormula()
    {
        var fin = Call("Fin", D(1,7,1,0));
        var sources = Seq(
            OpenBrace, V("i"), Colon, fin, Sp, Mid, Sp, LtF(Call("val", V("i")), D(7)), CloseBrace);
        var successors = Seq(
            OpenBrace, V("j"), Colon, fin, Sp, Mid, Sp,
            Mem(Tuple(Call("val", V("j")), V("a")), Call("fst", Call("snd", Call("snd", Call("minimumTable", Call("val", V("i"))))))), CloseBrace);
        var baseIndex = Call("fst", Call("minimumTable", Call("val", V("i"))));
        var baseState = Call("fst", Call("baseTable", baseIndex));
        var flag = Call("fst", Call("snd", Call("minimumTable", Call("val", V("i")))));
        var condition = DottedCall("Bool", "and", DottedCall("Bool", "and", flag, Call("baseTerminal", baseState)),
            BooleanEq(Call("getD", OptionalIndex(baseState, D(1,8)), D(0)), D(0)));
        var accepted = Seq(
            OpenBrace, V("i"), Colon, fin, Sp, Mid, Sp, condition, CloseBrace);
        return Disp(Eqn(Call("minimumAutomaton"), NfaMk(Lam("i", fin, Lam("a", Alphabet(), successors)), sources, accepted)));
    }
    private static Formula BoundFormula()
    {
        var fin = Call("Fin", D(1,7,1,0));
        var automaton = Call("minimumAutomaton");
        var cost = Seq(LambdaLower, Sp, OpenBracket, fin, CloseBracket, Sp,
            V("a"), Colon, Alphabet(), Sp, OpenBracket, fin, CloseBracket, Sp, Mapsto, Sp, Call("fst", V("a")));
        var body = All("p", Call("Path", automaton, V("s"), V("t"), V("xs")),
            LeF(Call("pathCharge", cost, V("p")), D(0)));
        body = Imp(And(Mem(V("s"), Call("start", automaton)), Mem(V("t"), Call("accept", automaton))), body);
        return Disp(All("s", fin, All("t", fin, All("xs", ListOf(Alphabet()), body))));
    }

}
