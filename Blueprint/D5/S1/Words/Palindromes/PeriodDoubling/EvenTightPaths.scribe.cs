using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class EvenTightPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/EvenTightPaths.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every cut in an even tight path from an even endpoint to zero has odd length.", H("Odd Cuts in Even Tight Paths"), Blocks(
        Describe.Lean(DescribeId.Create("pd-eventightpaths-even-tight-path-has-only-odd-cuts"),
            DeclarationHandle.Create(Prefix + "even_tight_path_has_only_odd_cuts"), H("The path obstruction"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The initial endpoint belongs to class S and is even, and its rounded-half signed weight is even. The descending path ends at zero and every cut is a literal palindrome whose signed weight drops by one. Induction makes the number of cuts equal to the initial signed weight and balances endpoint parity with the count of equal-parity edges. The one-even-cut bound then forces that count to zero, so all endpoint parities differ. div denotes natural integer quotient and Nat.sub denotes truncated natural subtraction. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

    private static Formula LastOption(Formula xs) =>
        Ite(Eqn(xs, ListNil()), Ty("none"), Call("some",
            new Formula.Apply(Seq(Operatorname, Grp(V("List"), Dot, V("getLast"))), [xs])));
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
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);


    private static Formula CutFormula()
    {
        var s=V("s"); var t=V("t");
        Formula Mod2(Formula n) => Call("mod",n,D(2));
        Formula Weight(Formula n) => Call("signedWeight",Cast(Call("div",Add(n,D(1)),D(2)),Z()));
        var word=Call("ofFn",Lam("i",Call("Fin",DottedCall("Nat", "sub",s,t)),Upd(Add(t,Call("val",V("i"))))));
        var relation=Lam("s",N(),Lam("t",N(),And(LtF(t,s),Call("Palindrome",word),Eqn(Weight(s),Add(Weight(t),D(1))))));
        var path=Call("cons",V("n"),V("cuts"));
        var assumptions=And(Call("classS",V("n")),Eqn(Mod2(V("n")),D(0)),Eqn(Mod2(Weight(V("n"))),D(0)),
            Eqn(LastOption(path),Call("some",D(0))),Call("IsChain",path,relation));
        var conclusion=Call("IsChain",path,Lam("s",N(),Lam("t",N(),Ne(Mod2(s),Mod2(t)))));
        return Disp(All("n",N(),All("cuts",ListOf(N()),Imp(assumptions,conclusion))));
    }
}
