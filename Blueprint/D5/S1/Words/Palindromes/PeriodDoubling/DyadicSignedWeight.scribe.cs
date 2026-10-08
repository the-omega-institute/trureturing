using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class DyadicSignedWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/DyadicSignedWeight.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dyadic boundary has exactly two possible carry costs.", H("Dyadic Splitting of Signed Weight"), Blocks(
        Describe.Lean(DescribeId.Create("pd-dyadicsignedweight-signed-weight-dyadic-split"),
            DeclarationHandle.Create(Prefix + "signed_weight_dyadic_split"), H("The exact dyadic minimum"),
            StatementSource.FromAuthor(SplitFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The high part M is any integer. The low part u is a natural number in the closed interval from zero to the dyadic power. The second branch uses truncated natural subtraction 2^h minus u, then coerces to an integer. Binary induction couples both carries, including the two endpoints."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula SplitFormula()
    {
        var term = Add(Mul(V("M"), Pow(D(2), V("h"))), Cast(V("u"), Z()));
        var first = Add(Call("signedWeight", V("M")), Call("signedWeight", Cast(V("u"), Z())));
        var tail = Cast(DottedCall("Nat", "sub", Pow(D(2), V("h")), V("u")), Z());
        var second = Add(Call("signedWeight", Add(V("M"), D(1))), Call("signedWeight", tail));
        return Disp(All("h", N(), All("M", Z(), All("u", N(),
            Imp(LeF(V("u"), Pow(D(2), V("h"))),
                Eqn(Call("signedWeight", term), Call("min", first, second)))))));
    }

}
