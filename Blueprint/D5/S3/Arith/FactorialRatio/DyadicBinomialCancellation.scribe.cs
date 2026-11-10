using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class DyadicBinomialCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive index, the reduced denominator of the polarization-transfer "
            + "ratio is the odd binomial gap divided by its greatest common divisor with "
            + "the ceiling half-index.",
        H("The all-index denominator formula for OEIS A362534"),
        Blocks(Describe.Lean(
            DescribeId.Create("dyadic-binomial-cancellation-denominator-formula"),
            DeclarationHandle.Create(
                "D5/S3/Arith/FactorialRatio/DyadicBinomialCancellation.denominator_formula"),
            H("Exact reduced fractions for every positive index"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The functions f and g are the original rational-valued OEIS formulas "
                    + "from SabbaPolarizationTransferRefutation. For n at least one, let "
                    + "k be floor(n/2), m = n-k, B = choose(n,k), v the exponent of two "
                    + "in B, b = B/2^v and G = (2^n-B)/2^v. Then num(g) = G, "
                    + "den(f/g) = G/gcd(m,G), and num(f/g) = mb/gcd(m,G). "
                    + "The proof derives B strictly between zero and 2^n, hence v < n, "
                    + "positive odd b and G, and coprimality of b and G. The binomial "
                    + "identity n choose(n-1,k) = mB connects the normalized ratio to "
                    + "the original parity definitions. These are exact unbounded "
                    + "arithmetic statements, including n = 1 and n = 2. They do not "
                    + "formalize the physical derivation of either bound. This is the "
                    + "formalization of an existing written correction, not an additional "
                    + "claim of mathematical novelty or a new finite computation."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula And(params Formula[] terms)
    {
        Formula result = terms[^1];
        for (int i = terms.Length - 2; i >= 0; --i)
            result = new Formula.Logic(terms[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Statement()
    {
        Formula n = F.Id("n"), m = F.Id("m"), bcap = F.Id("B"),
            v = F.Id("v"), b = F.Id("b"), gap = F.Id("G");
        Formula half = Call("NatDiv", n, D(2));
        Formula power = new Formula.Power(D(2), v);
        Formula conditions = And(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n),
            Equal(m, new Formula.Binary(n, FormulaBinaryOperator.Subtract, half)),
            Equal(bcap, Call("choose", n, half)),
            Equal(v, Call("factorization", bcap, D(2))),
            Equal(b, Call("NatDiv", bcap, power)),
            Equal(gap, Call("NatDiv", new Formula.Binary(new Formula.Power(D(2), n),
                FormulaBinaryOperator.Subtract, bcap), power)));
        Formula ratio = new Formula.Fraction(Call("f", n), Call("g", n));
        Formula gcd = Call("gcd", m, gap);
        Formula result = And(
            Equal(Call("num", Call("g", n)), gap),
            Equal(Call("den", ratio), Call("NatDiv", gap, gcd)),
            Equal(Call("num", ratio), Call("NatDiv",
                new Formula.Binary(m, FormulaBinaryOperator.Multiply, b), gcd)));
        result = new Formula.Logic(Seq(Open, conditions, Close),
            FormulaLogicOperator.Implies, Seq(Open, result, Close));
        foreach (string variable in new[] { "G", "b", "v", "B", "m", "n" })
            result = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variable), Seq(Mathbb, Grp(F.Id("N"))), result);
        return Disp(result);
    }
}
