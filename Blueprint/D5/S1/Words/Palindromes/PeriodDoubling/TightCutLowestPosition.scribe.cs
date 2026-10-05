using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class TightCutLowestPositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/TightCutLowestPosition.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The lowest nonzero signed position never decreases on a tight legal cut.", H("Lowest-Position Monotonicity"), Blocks(
        Describe.Lean(DescribeId.Create("pd-tightcutlowestposition-tight-cut-lowest-position"),
            DeclarationHandle.Create(Prefix + "tight_cut_lowest_position"), H("The literal minimum-position transition law"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A cut is tight when the minimum signed weight of the rounded half drops by exactly one. Complete cut realization excludes the invalid class mode. Lifting the base path to the minimum product gives a persistent flag for output nonzero digits emitted before any input nonzero digit. Its accepting potential bound zero excludes a true flag on a path with signed-weight drop one. Digit induction then yields the order of the first nonzero coefficients, and their literal dyadic valuations give the stated inequality. The zero endpoint is listed separately because its dyadic valuation is defined to be zero. div denotes natural integer quotient, and NatSub denotes truncated natural subtraction."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula CutFormula()
    {
        Formula Weight(Formula n) => Call("signedWeight",Cast(Call("div",Add(n,D(1)),D(2)),Z()));
        var word=Call("ofFn",Lam("i",Call("Fin",Call("NatSub",V("n"),V("j"))),Upd(Add(V("j"),Call("val",V("i"))))));
        var assumptions=And(Call("classS",V("n")),LtF(V("j"),V("n")),Call("Palindrome",word),
            Eqn(Weight(V("n")),Add(Weight(V("j")),D(1))));
        Formula Valuation(Formula n) => Call("padicValNat",D(2),Call("div",Add(n,D(1)),D(2)));
        var conclusion=new Formula.Logic(Eqn(V("j"),D(0)),FormulaLogicOperator.Or,
            LeF(Valuation(V("n")),Valuation(V("j"))));
        return Disp(All("n",N(),All("j",N(),Imp(assumptions,conclusion))));
    }
}
