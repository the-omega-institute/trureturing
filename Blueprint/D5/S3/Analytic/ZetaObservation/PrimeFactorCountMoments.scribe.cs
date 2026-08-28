using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class PrimeFactorCountMomentsDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeta-law distinct-prime count has the exact Bernoulli mean and variance.",
        H("Moments of the Distinct Prime-Factor Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-factor-count-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "primeFactorCount"),
                H("The distinct prime-factor count reuses Mathlib omega"),
                StatementSource.FromAuthor(CountDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named wrapper exposes FPOD's distinct-prime count while retaining "
                        + "Mathlib's totalized values at zero and one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-support-indicator-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "primeSupportIndicator"),
                H("A prime-support coordinate is a real indicator"),
                StatementSource.FromAuthor(IndicatorDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate is one exactly when the selected prime has positive "
                        + "factorization exponent, and zero otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-support-sum"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeFactorCount_eq_tsum_support"),
                H("The count is the pointwise sum of support indicators"),
                StatementSource.FromAuthor(CountSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural number, factorization support is finite. The count is "
                        + "therefore the prime-indexed sum of its zero-one coordinates, "
                        + "including at zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-expectation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_factor_count_expectation"),
                H("The zeta-law mean is the prime evidence sum"),
                StatementSource.FromAuthor(ExpectationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This is the full zeta-law result, not the assumption-based fallback. "
                            + "The repository's zeta probability measure and Bernoulli support "
                            + "coordinates are reused.")),
                    Paragraph(Text(
                        "Interchanging expectation and the countable sum uses the sharp "
                            + "summability theorem for the prime evidence series above one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-variance"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_factor_count_variance"),
                H("The variance is the sum of Bernoulli variances"),
                StatementSource.FromAuthor(VarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mutual independence comes from unique factorization through the "
                            + "existing prime-coordinate theorem. It is not a consequence of "
                            + "the index type merely being countable.")),
                    Paragraph(Text(
                        "The second moment separates diagonal Bernoulli terms from products of "
                            + "distinct coordinates. Both resulting prime series are summable "
                            + "when the exponent is above one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-degenerate-audit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_factor_count_degenerate_audit"),
                H("Zero, one, and a prime realize the basic degeneracies"),
                StatementSource.FromAuthor(DegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The count vanishes at zero and one and equals one at a prime. Empty and "
                        + "singleton finite support families are already covered by the mutual "
                        + "independence theorem used in the variance proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moment-threshold-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "moment_threshold_is_necessary"),
                H("Exponent one is a named nonsummable counterexample"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At exponent one the reciprocal-prime evidence family is not summable, "
                            + "so the strict threshold in the moment theorems cannot be "
                            + "weakened to a non-strict inequality.")),
                    Paragraph(Text(
                        "Prime distribution is load-bearing only for this analytic threshold. "
                            + "The Bernoulli moment algebra itself applies to any independent "
                            + "summable zero-one family."))),
                DescribeRole.Theorem))));

    private static Formula CountDefinitionFormula()
    {
        Formula n = F.Id("n");
        return F.Disp(Equal(Count(n), Call("omega", n)));
    }

    private static Formula IndicatorDefinitionFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula positive = new Formula.Relation(
            F.D(0), FormulaRelationOperator.LessThan, Call("factorExponent", n, p));
        return F.Disp(Equal(Indicator(p, n), Call("indicator", positive)));
    }

    private static Formula CountSumFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        return F.Disp(Equal(Count(n), SumPrimes(p, Indicator(p, n))));
    }

    private static Formula ExpectationFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula domain = new Formula.Relation(
            F.D(1), FormulaRelationOperator.LessThan, s);
        Formula result = Equal(
            Call("ExpectationUnderZeta", s, Count(F.Id("N"))),
            SumPrimes(p, PrimeEvidence(p, s)));
        return F.Disp(new Formula.Logic(
            domain,
            FormulaLogicOperator.Implies,
            result));
    }

    private static Formula VarianceFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula evidence = PrimeEvidence(p, s);
        Formula term = F.Seq(
            evidence,
            F.Sp, F.Cdot, F.Sp,
            F.Grp(F.D(1), F.Sp, F.Minus, F.Sp, evidence));
        Formula domain = new Formula.Relation(
            F.D(1), FormulaRelationOperator.LessThan, s);
        Formula result = Equal(
            Call("VarianceUnderZeta", s, Count(F.Id("N"))),
            SumPrimes(p, term));
        return F.Disp(new Formula.Logic(
            domain,
            FormulaLogicOperator.Implies,
            result));
    }

    private static Formula DegenerateFormula()
    {
        Formula p = F.Id("p");
        return F.Disp(And(
            Equal(Count(F.D(0)), F.D(0)),
            And(
                Equal(Count(F.D(1)), F.D(0)),
                Equal(Count(p), F.D(1)))));
    }

    private static Formula ThresholdFormula()
    {
        Formula p = F.Id("p");
        Formula family = F.Seq(
            p, F.Mapsto, F.Sp, PrimeEvidence(p, F.D(1)));
        return F.Disp(F.Seq(F.Neg, F.Sp, Call("Summable", family)));
    }

    private static Formula Count(Formula n) =>
        Call("PrimeFactorCount", n);

    private static Formula Indicator(Formula p, Formula n) =>
        Call("PrimeSupportIndicator", p, n);

    private static Formula PrimeEvidence(Formula p, Formula s) =>
        new Formula.Power(p, F.Grp(F.Seq(F.Minus, s)));

    private static Formula SumPrimes(Formula p, Formula term) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(p, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("P"))),
            F.Sp, term);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
