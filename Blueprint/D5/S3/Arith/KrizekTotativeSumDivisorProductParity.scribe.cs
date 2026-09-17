using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class KrizekTotativeSumDivisorProductParityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/KrizekTotativeSumDivisorProductParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/krizek2016a280246");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive natural n, the product over the divisors of n of their "
            + "totative sums is odd exactly when the totative sum of n is odd.",
        H("Krizek's Totative-Sum Divisor-Product Parity Conjecture"),
        Blocks(
            Paragraph(Text(
                "All variables and values lie in the natural numbers. The range ending at "
                    + "n+1 contains 0 through n, and filtering by Coprime(n,k) leaves the "
                    + "totatives of n. The notation mod(p,4) below is natural-number "
                    + "remainder. The set divisors(0) is empty, while divisors(n) for "
                    + "positive n is the finite set of positive divisors.")),
            Node("totativeSum", "The sum of the totatives", TotativeSumFormula(),
                "The summand k ranges over exactly the values from zero through n that are "
                    + "coprime to n. The endpoints contribute correctly: zero is retained "
                    + "only at n=1, while n itself is retained only at n=1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("divisorTotativeProduct", "The divisor product", DivisorProductFormula(),
                "For each positive divisor d of n, the product contains one factor equal to "
                    + "the totative sum of d.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("two_mul_totativeSum", "The paired totative-sum identity", PairingFormula(),
                "When n is greater than one, subtraction from n pairs every reduced residue "
                    + "k with n-k. Each pair sums to n, and the number of residues is the "
                    + "Euler totient of n.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("odd_totativeSum_iff", "The odd totative-sum classification",
                ClassificationFormula(),
                "The boundary values one and two are odd. Above them, oddness forces a "
                    + "single odd prime factor, and the paired identity excludes primes "
                    + "congruent to one modulo four. Conversely, every positive power of a "
                    + "prime congruent to three modulo four has an odd totative sum.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "The divisor-product parity equivalence", ResultFormula(),
                "A finite natural product is odd exactly when each factor is odd. The odd "
                    + "totative-sum classification is closed under taking positive divisors, "
                    + "so oddness at n propagates to every divisor; the factor indexed by n "
                    + "gives the reverse implication.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a280246-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula TotativeSumFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula index = Seq(k, Sp, InMacro, Sp, Call("range", Add(n, D(1))), Comma, Sp,
            Call("Coprime", n, k));
        return Disp(ForAllNatural("n",
            Equal(Call("totativeSum", n), IndexedSum(index, k))));
    }

    private static Formula DivisorProductFormula()
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula index = Seq(d, Sp, InMacro, Sp, Call("divisors", n));
        return Disp(ForAllNatural("n",
            Equal(Call("divisorTotativeProduct", n),
                IndexedProduct(index, Call("totativeSum", d)))));
    }

    private static Formula PairingFormula()
    {
        Formula n = F.Id("n");
        Formula hypothesis = Less(D(1), n);
        Formula conclusion = Equal(Multiply(D(2), Call("totativeSum", n)),
            Multiply(n, Call("totient", n)));
        return Disp(ForAllNatural("n", Implies(hypothesis, conclusion)));
    }

    private static Formula ClassificationFormula()
    {
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula primePower = ExistsNaturals("p", "k", And(
            Call("Prime", p),
            Equal(new Formula.Modulo(p, D(4)), D(3)),
            LessOrEqual(D(1), k),
            Equal(n, Power(p, k))));
        Formula cases = Or(Equal(n, D(1)), Equal(n, D(2)), primePower);
        return Disp(ForAllNatural("n",
            Iff(Call("Odd", Call("totativeSum", n)), cases)));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula hypothesis = LessOrEqual(D(1), n);
        Formula conclusion = Iff(Call("Odd", Call("divisorTotativeProduct", n)),
            Call("Odd", Call("totativeSum", n)));
        return Disp(ForAllNatural("n", Implies(hypothesis, conclusion)));
    }

    private static Formula Naturals() => Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ForAllNatural(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals(), body);
    private static Formula ExistsNaturals(string first, string second, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create(first), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create(second), Naturals())
            ], body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, new Formula.LatexGroup([F.Id(name)])), [.. arguments]);
    private static Formula IndexedSum(Formula index, Formula term) =>
        Seq(new Formula.Subscript(F.Sum, index), Sp, term);
    private static Formula IndexedProduct(Formula index, Formula term) =>
        Seq(new Formula.Subscript(Prod, index), Sp, term);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));
    private static Formula Or(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.Or, result);
        return result;
    }
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
}
