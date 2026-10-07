using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class TightPathEvenCutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/TightPathEvenCuts.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tight palindrome-cut path has at most one even-length deletion.", H("At Most One Tight Even Cut"), Blocks(
        Describe.Lean(DescribeId.Create("pd-tightpathevencuts-tight-path-at-most-one-even-cut"),
            DeclarationHandle.Create(Prefix + "tight_path_at_most_one_even_cut"), H("The path obstruction"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The path is any finite descending list of literal tight palindrome cuts beginning in class S. Its even cuts are exactly the pairs with equal endpoint parity. An even palindrome has length two. Signed-weight arithmetic and the source letters force a tight even cut to start at an odd integer at least five with odd rounded half; its successor has positive dyadic valuation. Class preservation and lowest-position monotonicity keep that valuation positive until zero, excluding any further even cut. Induction counts the exceptional first even cut. The statement does not require the path to end at zero. div denotes natural integer quotient and Nat.sub denotes truncated natural subtraction."))), DescribeRole.Theorem))));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula V(string name) => F.Id(name);
    private static Formula BooleanEq(Formula a, Formula b) =>
        Parenthesized(Seq(a, Sp, Eq, Eq, Sp, b));

    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula Pair() => Product(N(),N());
    private static Formula CutFormula()
    {
        var s=V("s"); var t=V("t");
        Formula Weight(Formula n) => Call("signedWeight",Cast(Call("div",Add(n,D(1)),D(2)),Z()));
        var word=Call("ofFn",Lam("i",Call("Fin",DottedCall("Nat", "sub",s,t)),Upd(Add(t,Call("val",V("i"))))));
        var relation=Lam("s",N(),Lam("t",N(),And(LtF(t,s),Call("Palindrome",word),Eqn(Weight(s),Add(Weight(t),D(1))))));
        var path=Call("cons",V("n"),V("cuts"));
        var pairs=Call("zip",path,V("cuts"));
        var parity=BooleanEq(Call("mod",Call("fst",V("e")),D(2)), Call("mod",Call("snd",V("e")),D(2)));
        var count=Call("length",Call("filter",Lam("e",Pair(),parity),pairs));
        return Disp(All("n",N(),All("cuts",ListOf(N()),
            Imp(And(Call("classS",V("n")),Call("IsChain",path,relation)),LeF(count,D(1))))));
    }
}
