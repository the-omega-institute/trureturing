using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedPathSelectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathSelection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A good completed marker path separates into its lower tail, selected digit and higher suffix.", H("Marked Path Selection"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedpathselection-marked-path-selection"),
            DeclarationHandle.Create(Prefix + "marked_path_selection"), H("Selected transition and phase snapshots"),
            StatementSource.FromAuthor(SelectionFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every path from mode zero to mode four whose final bad flag is zero has a selected transition from mode zero to mode one. Its preceding path is the unmarked lower tail. Input and output streams agree after the selected transition. The two preceding signed digits vanish in both streams. The selected input digit is one. Its output is either one, or zero with input negative phase one, output negative phase zero and an unbroken lower negation flag. Marker parity, retention and both phases at the terminal state are exactly the snapshots saved on the selected transition."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
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

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));



    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula f,int k) => Call("getD",Call("getElemOption",f,new Formula.Number(k)),D(0));

    private static Formula SelectionFormula()
    {
        var list=ListOf(Z());var alpha=Alphabet();
        Formula Path(Formula s, Formula t, Formula xs) => Call("Path",Ty("prefixRawAutomaton"),s,t,xs);
        Formula Digit(Formula q, int k) => Entry(Call("fst",Call("baseTable",Call("toNat",Entry(q,0)))),k);
        Formula Output(int k, Formula p) => Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,list,CloseBracket,Sp,
            OpenBracket,alpha,CloseBracket,Sp,V("q"),Colon,list,Sp,Mapsto,Sp,Digit(V("q"),k)),p);
        Formula Phase(int sign, int parity) => Call("orBool",Call("decide",LtF(Digit(V("u"),sign),D(0))),
            Call("andBool",Call("beq",Digit(V("u"),sign),D(0)),Call("beq",Digit(V("u"),parity),D(1))));
        Formula BoolInt(Formula b) => Cast(Call("toNat",b),Z());
        var data=All("k",N(),Imp(And(LeF(D(3),V("k")),LeF(V("k"),D(6))),
            Eqn(Call("getD",Call("getElemOption",V("t"),V("k")),D(0)),
                Call("getD",Call("getElemOption",V("v"),V("k")),D(0)))));
        var removed=And(Eqn(Digit(V("v"),12),D(0)),Eqn(Entry(V("v"),5),D(1)),
            Eqn(Entry(V("v"),6),D(0)),Ne(Entry(V("u"),2),D(0)));
        var selected=And(Eqn(Digit(V("v"),10),D(1)),Eqn(Digit(V("u"),10),D(0)),
            Eqn(Digit(V("u"),11),D(0)),Eqn(Digit(V("u"),12),D(0)),Eqn(Digit(V("u"),13),D(0)),
            Eqn(Entry(V("v"),3),Digit(V("u"),1)),
            Eqn(Entry(V("v"),4),BoolInt(Call("beq",Digit(V("v"),12),D(1)))),
            Eqn(Entry(V("v"),5),BoolInt(Phase(16,2))),Eqn(Entry(V("v"),6),BoolInt(Phase(17,3))),
            new Formula.Logic(Eqn(Digit(V("v"),12),D(1)),FormulaLogicOperator.Or,removed));
        var facts=And(Eqn(V("xs"),Call("append",V("as"),Call("cons",V("a"),V("bs")))),
            Eqn(Entry(V("u"),1),D(0)),Eqn(Entry(V("v"),1),D(1)),
            Mem(Tuple(V("v"),V("a")),Call("successors",V("u"))),Eqn(Entry(V("v"),7),D(0)),
            Eqn(Output(10,V("p")),Call("append",Output(10,V("before")),
                Call("cons",Digit(V("v"),10),Output(10,V("after"))))),
            Eqn(Output(12,V("p")),Call("append",Output(12,V("before")),
                Call("cons",Digit(V("v"),12),Output(10,V("after"))))),
            Eqn(Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,list,CloseBracket,Sp,
                OpenBracket,alpha,CloseBracket,Sp,V("q"),Colon,list,Sp,Mapsto,Sp,Entry(V("q"),1)),V("p")),
                Call("append",Call("replicate",Call("length",V("as")),D(0)),Call("cons",D(1),
                    Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,list,CloseBracket,Sp,
                        OpenBracket,alpha,CloseBracket,Sp,V("q"),Colon,list,Sp,Mapsto,Sp,Entry(V("q"),1)),V("after"))))),data,selected);
        var conclusion=Ex("u",list,Ex("v",list,Ex("as",ListOf(alpha),Ex("bs",ListOf(alpha),Ex("a",alpha,
            Ex("before",Path(V("s"),V("u"),V("as")),Ex("after",Path(V("v"),V("t"),V("bs")),facts)))))));
        var hypotheses=And(Eqn(Entry(V("s"),1),D(0)),Eqn(Entry(V("t"),1),D(4)),Eqn(Entry(V("t"),7),D(0)));
        return Disp(All("s",list,All("t",list,All("xs",ListOf(alpha),
            All("p",Path(V("s"),V("t"),V("xs")),Imp(hypotheses,conclusion))))));
    }
}
