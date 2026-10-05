using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class TripleBinaryDigitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/TripleBinaryDigits.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary binary digits determine a minimum nonadjacent signed expansion.", H("Minimum Signed Digits from Triple Binary Differences"), Blocks(
        Describe.Lean(DescribeId.Create("pd-triplebinarydigits-triple-digits-value-and-minimality"),
            DeclarationHandle.Create(Prefix + "triple_digits_value_and_minimality"), H("A minimum signed expansion from ordinary binary digits"),
            StatementSource.FromAuthor(TripleFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At position i, the signed digit is the difference of the binary digits at position i+1 of 3X and X. The bound on h pads both numbers by leading zeros. The resulting signed digit list has value X, no adjacent nonzero digits, and exactly the minimum number of nonzero digits. NatDiv and mod denote natural integer division and remainder. Cast denotes the natural-to-integer embedding. Digits are listed from the lowest position upward."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);


    private static Formula Digits()
    {
        var power = Pow(D(2), Add(Call("val", V("i")), D(1)));
        var z = Cast(Call("mod", Call("NatDiv", Mul(D(3), V("X")), power), D(2)), Z());
        var b = Cast(Call("mod", Call("NatDiv", V("X"), power), D(2)), Z());
        return Call("ofFn", Lam("i", Call("Fin", V("h")), Sub(z, b)));
    }
    private static Formula TripleFormula()
    {
        var digits = Digits();
        var value = Call("foldr", Lam("z", Z(), Lam("acc", Z(), Add(V("z"), Mul(D(2), V("acc"))))), D(0), digits);
        var relation = Lam("a", Z(), Lam("b", Z(), new Formula.Logic(Eqn(V("a"), D(0)),
            FormulaLogicOperator.Or, Eqn(V("b"), D(0)))));
        var weight = Call("length", Call("filter", Lam("z", Z(), Call("bne", V("z"), D(0))), digits));
        var result = And(Eqn(value, Cast(V("X"), Z())), Call("IsChain", digits, relation),
            Eqn(Call("signedWeight", Cast(V("X"), Z())), weight));
        return Disp(All("X", N(), All("h", N(), Imp(LtF(Mul(D(3), V("X")),
            Pow(D(2), Add(V("h"), D(1)))), result))));
    }

}
