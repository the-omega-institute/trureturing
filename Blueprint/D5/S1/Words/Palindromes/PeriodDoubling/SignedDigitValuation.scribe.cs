using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class SignedDigitValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitValuation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first coefficient equal to plus or minus one fixes the dyadic valuation of the signed value.", H("Lowest Signed Digit and Dyadic Valuation"), Blocks(
        Describe.Lean(DescribeId.Create("pd-signeddigitvaluation-signed-digits-lowest-valuation"),
            DeclarationHandle.Create(Prefix + "signed_digits_lowest_valuation"), H("Peeling the zero prefix"),
            StatementSource.FromAuthor(ValuationFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The finite integer list is read least significant first. All positions below k vanish, and its coefficient at k is either minus one or plus one. Higher coefficients are arbitrary integers; nonadjacency is not required. The value is a nonzero multiple of exactly 2 to the power k, because the first residual is odd. Option lookup uses default zero. padicValInt is Mathlib's valuation of the natural absolute value of the integer."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);
    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));

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
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula NegF(Formula a) => Call("neg", a);


    private static Formula ValuationFormula()
    {
        Formula E(Formula i) => Call("getD",OptionalIndex(V("ds"),i),D(0));
        var zero=All("i",N(),Imp(LtF(V("i"),V("k")),Eqn(E(V("i")),D(0))));
        var coeff=new Formula.Logic(Eqn(E(V("k")),NegF(D(1))),FormulaLogicOperator.Or,Eqn(E(V("k")),D(1)));
        var value=Call("foldr",Seq(LambdaLower,Sp,V("z"),Colon,Z(),Sp,V("x"),Colon,Z(),Sp,Mapsto,Sp,
            Add(V("z"),Mul(D(2),V("x")))),D(0),V("ds"));
        return Disp(All("ds",ListOf(Z()),All("k",N(),Imp(And(zero,coeff),Eqn(Call("padicValInt",D(2),value),V("k"))))));
    }
}
