using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class LehmerTotientDichotomyDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Factorization/LehmerTotientDichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six general arithmetic consequences of Lehmer's totient divisibility condition.",
        H("Component Consequences of Lehmer's Totient Condition"),
        Blocks(
            Entry(
                "prime_dvd_totient_of_prime_sq_dvd",
                "prime-square-factor-in-totient",
                "A repeated prime factor enters the totient",
                PrimeSquareFormula(),
                "If p is prime and p squared divides n, then p divides Euler's totient of n."),
            Entry(
                "squarefree_of_totient_dvd_sub_one",
                "lehmer-condition-squarefree",
                "The Lehmer condition forces squarefreeness",
                SquarefreeFormula(),
                "For n greater than one, totient divisibility by n minus one rules out every repeated prime factor."),
            Entry(
                "totient_eq_primeFactors_sub_one_prod",
                "squarefree-totient-product",
                "The squarefree totient product formula",
                TotientProductFormula(),
                "For a nonzero squarefree n, Euler's totient is the product of p minus one over its distinct prime factors."),
            Entry(
                "odd_of_totient_dvd_sub_one",
                "lehmer-condition-odd",
                "The composite Lehmer branch is odd",
                OddFormula(),
                "A composite n greater than one whose totient divides n minus one must be odd."),
            Entry(
                "two_pow_primeFactors_card_dvd_sub_one",
                "lehmer-condition-two-adic-factor",
                "The prime-factor count gives a two-adic divisor",
                TwoAdicFormula(),
                "On the composite branch, two to the number of distinct prime factors divides n minus one."),
            Entry(
                "three_le_primeFactors_card",
                "lehmer-condition-three-prime-factors",
                "The composite branch has at least three distinct prime factors",
                ThreeFactorsFormula(),
                "A composite Lehmer candidate cannot have zero, one, or two distinct prime factors."))));

    private DocumentBlock.Describe Entry(string declaration, string id, string title,
        Formula formula, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Root + declaration), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula PrimeSquareFormula()
    {
        Formula p = F.Id("p"), n = F.Id("n");
        Formula premise = And(Call("Prime", p), Divides(Power(p, D(2)), n));
        return Disp(ForAll("p", ForAll("n", Implies(premise, Divides(p, Totient(n))))));
    }

    private static Formula SquarefreeFormula()
    {
        Formula n = F.Id("n");
        Formula premise = And(Less(D(1), n), Divides(Totient(n), Subtract(n, D(1))));
        return Disp(ForAll("n", Implies(premise, Call("Squarefree", n))));
    }

    private static Formula TotientProductFormula()
    {
        Formula n = F.Id("n");
        Formula premise = And(NotEqual(n, D(0)), Call("Squarefree", n));
        return Disp(ForAll("n", Implies(premise, Equal(Totient(n), PrimeFactorProduct(n)))));
    }

    private static Formula OddFormula()
    {
        Formula n = F.Id("n");
        Formula premise = And(
            Less(D(1), n),
            Divides(Totient(n), Subtract(n, D(1))),
            NotFormula(Call("Prime", n)));
        return Disp(ForAll("n", Implies(premise, Call("Odd", n))));
    }

    private static Formula TwoAdicFormula()
    {
        Formula n = F.Id("n");
        Formula premise = And(
            Less(D(1), n),
            Divides(Totient(n), Subtract(n, D(1))),
            NotFormula(Call("Prime", n)));
        Formula conclusion = Divides(
            Power(D(2), Call("card", Call("primeFactors", n))),
            Subtract(n, D(1)));
        return Disp(ForAll("n", Implies(premise, conclusion)));
    }

    private static Formula ThreeFactorsFormula()
    {
        Formula n = F.Id("n");
        Formula premise = And(
            Less(D(1), n),
            Divides(Totient(n), Subtract(n, D(1))),
            NotFormula(Call("Prime", n)));
        Formula conclusion = LessOrEqual(D(3), Call("card", Call("primeFactors", n)));
        return Disp(ForAll("n", Implies(premise, conclusion)));
    }

    private static Formula PrimeFactorProduct(Formula n)
    {
        Formula p = F.Id("p");
        return Seq(new Formula.Subscript(F.Prod, Member(p, Call("primeFactors", n))), Sp,
            Parenthesized(Subtract(p, D(1))));
    }

    private static Formula ForAll(string name, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
        body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Totient(Formula n) => Call("phi", n);

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula item in rest)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        }
        return result;
    }

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotFormula(Formula value) => new Formula.Not(value);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Power(Formula basis, Formula exponent) =>
        Seq(basis, Caret, Grp(exponent));

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
