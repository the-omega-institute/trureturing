using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class LehmerTotientStructureDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Arith/Congruence/LehmerTotientStructure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lehmer's totient divisibility condition forces oddness, squarefreeness, "
            + "Korselt divisibilities, a two-adic factor, and at least three prime factors "
            + "unless the number is prime.",
        H("Structure Forced by Lehmer's Totient Condition"),
        Blocks(
            Entry(
                "IsKorselt",
                "korselt-condition",
                "The squarefree Korselt condition",
                KorseltDefinitionFormula(),
                DescribeRole.Definition,
                "A natural number satisfies IsKorselt when it is squarefree and every prime "
                    + "factor p has p - 1 dividing n - 1. This formulation also applies to primes."),
            Entry(
                "lehmer_totient_structure",
                "lehmer-totient-structure",
                "The full Lehmer structural alternative",
                MainFormula(),
                DescribeRole.Theorem,
                "If phi(n) divides n - 1 for n greater than one, then n is prime, or n is odd "
                    + "and squarefree, satisfies the Korselt condition, and has all three stated "
                    + "divisibility and prime-factor conclusions. The squarefree step uses the "
                    + "Carmichael function on a hypothetical prime-square divisor. For exactly "
                    + "two distinct odd prime factors p and q, divisibility by (p-1)(q-1) would "
                    + "force it to divide (p-1)+(q-1), which is positive and strictly smaller."),
            Entry(
                "primeFactors_sub_one_prod_dvd_sub_one",
                "prime-factor-predecessor-product",
                "The prime-factor predecessor product divides n - 1",
                ProductFormula(),
                DescribeRole.Theorem,
                "Under the same hypotheses, the product of p - 1 over all prime factors divides "
                    + "n - 1. This named consequence follows from the structural alternative; "
                    + "in the prime case the product has the single factor n - 1."),
            Entry(
                "isKorselt_of_totient_dvd_sub_one",
                "lehmer-condition-implies-korselt",
                "Lehmer's condition implies the Korselt condition",
                KorseltConsequenceFormula(),
                DescribeRole.Theorem,
                "Every n greater than one whose totient divides n - 1 satisfies IsKorselt. "
                    + "For a prime this reduces to squarefreeness and the single divisor n - 1; "
                    + "for a composite it is one clause of the structural alternative."))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title,
        Formula formula, DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Root + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula KorseltDefinitionFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll("n", Iff(
            Call("IsKorselt", n),
            And(Call("Squarefree", n), PrimeFactorDivisibilities(n)))));
    }

    private static Formula MainFormula()
    {
        Formula n = F.Id("n");
        Formula primeFactors = Call("primeFactors", n);
        Formula compositeStructure = And(
            Call("Odd", n),
            Call("Squarefree", n),
            Call("IsKorselt", n),
            Divides(PrimeFactorProduct(n), Subtract(n, D(1))),
            Divides(Power(D(2), Call("card", primeFactors)), Subtract(n, D(1))),
            LessOrEqual(D(3), Call("card", primeFactors)));
        Formula premise = And(
            Less(D(1), n),
            Divides(Call("phi", n), Subtract(n, D(1))));
        Formula conclusion = Or(Call("Prime", n), compositeStructure);
        return Disp(ForAll("n", Implies(premise, conclusion)));
    }

    private static Formula ProductFormula()
    {
        Formula n = F.Id("n");
        Formula premise = And(
            Less(D(1), n),
            Divides(Call("phi", n), Subtract(n, D(1))));
        return Disp(ForAll("n", Implies(
            premise,
            Divides(PrimeFactorProduct(n), Subtract(n, D(1))))));
    }

    private static Formula KorseltConsequenceFormula()
    {
        Formula n = F.Id("n");
        Formula premise = And(
            Less(D(1), n),
            Divides(Call("phi", n), Subtract(n, D(1))));
        return Disp(ForAll("n", Implies(premise, Call("IsKorselt", n))));
    }

    private static Formula PrimeFactorDivisibilities(Formula n)
    {
        Formula p = F.Id("p");
        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("p"), Naturals())],
            Implies(
                Member(p, Call("primeFactors", n)),
                Divides(Subtract(p, D(1)), Subtract(n, D(1)))));
    }

    private static Formula PrimeFactorProduct(Formula n)
    {
        Formula p = F.Id("p");
        Formula index = Member(p, Call("primeFactors", n));
        return Seq(new Formula.Subscript(F.Prod, index), Sp, Parenthesized(Subtract(p, D(1))));
    }

    private static Formula ForAll(string name, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
        body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Relation(
        Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula item in rest)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        }
        return result;
    }

    private static Formula Less(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Member(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Power(Formula basis, Formula exponent) =>
        Seq(basis, Caret, Grp(exponent));

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
