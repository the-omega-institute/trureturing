using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PrimeProducts;

internal sealed class DistinctPrimeFactorCountBoundDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero integer has at most its floor base-two logarithm many distinct prime factors.",
        H("The Distinct Prime Factor Count Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distinct-prime-factor-count-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/PrimeProducts/DistinctPrimeFactorCountBound."
                        + "distinct_prime_factor_count_bound"),
                H("Distinct prime factors obey a floor logarithmic bound"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d be nonzero. Every prime divisor of its absolute value is at "
                            + "least two, so their product is at least two raised to the "
                            + "number of distinct prime divisors.")),
                    Paragraph(Text(
                        "The product of the distinct prime divisors is the natural-number "
                            + "radical of the absolute value. The radical divides a nonzero "
                            + "natural number and is therefore at most that number.")),
                    Paragraph(Text(
                        "Combining the two inequalities and applying the defining adjunction "
                            + "for the natural floor logarithm gives the stated base-two "
                            + "bound."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula absolute = new Formula.Absolute(d);
        Formula omega = Call("omega", absolute);
        Formula primeProduct = Call("distinctPrimeProduct", absolute);
        Formula twoToOmega = new Formula.Power(Seq(D(2)), Grp(omega));
        Formula lower = new Formula.Relation(
            twoToOmega,
            FormulaRelationOperator.LessThanOrEqual,
            primeProduct);
        Formula upper = new Formula.Relation(
            primeProduct,
            FormulaRelationOperator.LessThanOrEqual,
            absolute);
        Formula logarithmic = new Formula.Relation(
            omega,
            FormulaRelationOperator.LessThanOrEqual,
            Call("floorLog2", absolute));
        Formula nonzero = new Formula.Relation(
            d,
            FormulaRelationOperator.NotEqual,
            D(0));
        Formula conclusion = new Formula.Logic(
            lower,
            FormulaLogicOperator.And,
            new Formula.Logic(upper, FormulaLogicOperator.And, logarithmic));

        return F.Disp(new Formula.Logic(
            nonzero,
            FormulaLogicOperator.Implies,
            conclusion));
    }
}
