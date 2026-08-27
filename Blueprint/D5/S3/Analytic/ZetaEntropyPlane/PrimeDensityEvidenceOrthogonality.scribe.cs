using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class PrimeDensityEvidenceOrthogonalityDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime sparsity in the naturals is independent of evidence summability.",
        H("Prime Density Does Not Determine Evidence Summability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("natural-counting-ratio"),
                DeclarationHandle.Create(DeclarationPrefix + "naturalCountingRatio"),
                H("Natural counting ratio"),
                StatementSource.FromAuthor(NaturalCountingRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ratio counts members of a natural-number set between one and n, "
                        + "then divides by n. It is the explicit density surrogate used here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-natural-set"),
                DeclarationHandle.Create(DeclarationPrefix + "primeNaturals"),
                H("Prime naturals"),
                StatementSource.FromAuthor(PrimeNaturalsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sparse natural-number support is the named set of all prime values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("restricted-prime-evidence"),
                DeclarationHandle.Create(DeclarationPrefix + "restrictedPrimeEvidence"),
                H("Restricted prime evidence"),
                StatementSource.FromAuthor(RestrictedEvidenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Restriction multiplies the existing prime evidence by the support "
                        + "indicator. Outside the selected natural values it is zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-endpoint-counting-ratio"),
                DeclarationHandle.Create(DeclarationPrefix + "naturalCountingRatio_zero"),
                H("Every counting ratio is zero at zero"),
                StatementSource.FromAuthor(CountingRatioZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The interval is empty at n equal to zero, and totalized division returns "
                        + "zero. This records the endpoint degeneration explicitly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-counting-ratio-bridge"),
                DeclarationHandle.Create(DeclarationPrefix + "primeNaturals_countingRatio"),
                H("Prime support has the prime-counting ratio"),
                StatementSource.FromAuthor(PrimeCountingRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Counting the named prime set through n gives the usual prime-counting "
                        + "function, divided by n."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-prime-support-diverges"),
                DeclarationHandle.Create(DeclarationPrefix + "sparse_prime_support_diverges"),
                H("Sparse prime support has divergent reciprocal evidence"),
                StatementSource.FromAuthor(SparseDivergentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Chebyshev's bound makes the prime counting ratio vanish in the naturals. "
                        + "Euler's reciprocal-prime theorem still makes exponent one diverge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-prime-support-square-summable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "full_prime_support_square_evidence_summable"),
                H("Full prime support has summable square evidence"),
                StatementSource.FromAuthor(FullSummableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same support contains every prime, so it is full relative to the prime "
                        + "subtype. Exponent two is summable by the imported threshold theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-support-sparse-summable"),
                DeclarationHandle.Create(DeclarationPrefix + "empty_support_sparse_and_summable"),
                H("Empty support is sparse and summable"),
                StatementSource.FromAuthor(EmptySummableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Empty support also has zero counting ratio, but its restricted evidence is "
                        + "the zero family and is summable. Zero density permits both outcomes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-prime-support-summable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "singleton_prime_support_summable"),
                H("Singleton prime support is summable"),
                StatementSource.FromAuthor(SingletonSummableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-prime support has only one possibly nonzero term, so it is summable "
                        + "for every real exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("counting-density-is-insufficient"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "counting_density_not_sufficient_for_summability"),
                H("Counting density does not determine summability"),
                StatementSource.FromAuthor(InsufficiencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The combined statement records sparse divergence, full-support square "
                        + "convergence, and empty-support convergence in one public theorem."))),
                DescribeRole.Theorem))));

    private static Formula NaturalCountingRatioFormula()
    {
        Formula support = F.Id("S");
        Formula index = F.Id("n");
        Formula counted = Seq(
            Lvert, OpenBrace, F.Id("k"), Colon, D(1), Sp, Leq, Sp, F.Id("k"),
            Sp, Leq, Sp, index, Comma, Sp, F.Id("k"), Sp, InMacro, Sp,
            support, CloseBrace, Rvert);
        return Disp(new Formula.Relation(
            CountingRatio(support, index),
            FormulaRelationOperator.Equal,
            new Formula.Fraction(counted, index)));
    }

    private static Formula PrimeNaturalsFormula()
    {
        Formula prime = F.Id("p");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula set = Seq(
            OpenBrace, prime, Sp, InMacro, Sp, naturals, Sp, Mid, Sp,
            F.Id("Prime"), Open, prime, Close, CloseBrace);
        return Disp(new Formula.Relation(
            F.Id("P"),
            FormulaRelationOperator.Equal,
            set));
    }

    private static Formula RestrictedEvidenceFormula()
    {
        Formula support = F.Id("S");
        Formula exponent = F.Id("s");
        Formula prime = F.Id("p");
        Formula indicator = Seq(
            F.Id("chi"), Open, support, Comma, prime, Close);
        Formula right = new Formula.Binary(
            indicator,
            FormulaBinaryOperator.Multiply,
            Evidence(F.Id("P"), exponent, prime));
        return Disp(new Formula.Relation(
            Evidence(support, exponent, prime),
            FormulaRelationOperator.Equal,
            right));
    }

    private static Formula CountingRatioZeroFormula()
    {
        Formula support = F.Id("S");
        return Disp(Seq(
            Forall, Sp, support, Comma, Sp,
            new Formula.Relation(
                CountingRatio(support, D(0)),
                FormulaRelationOperator.Equal,
                D(0))));
    }

    private static Formula PrimeCountingRatioFormula()
    {
        Formula index = F.Id("n");
        Formula primeCount = Seq(Pi, Open, index, Close);
        return Disp(Seq(
            Forall, Sp, index, Comma, Sp,
            new Formula.Relation(
                CountingRatio(F.Id("P"), index),
                FormulaRelationOperator.Equal,
                new Formula.Fraction(primeCount, index))));
    }

    private static Formula SparseDivergentFormula() =>
        Disp(SparseDivergentBody());

    private static Formula FullSummableFormula() =>
        Disp(FullSummableBody());

    private static Formula EmptySummableFormula() =>
        Disp(EmptySummableBody());

    private static Formula SingletonSummableFormula()
    {
        Formula prime = F.Id("q");
        Formula exponent = F.Id("s");
        Formula singleton = Seq(OpenBrace, prime, CloseBrace);
        return Disp(Seq(
            Forall, Sp, prime, Comma, Sp, exponent, Comma, Sp,
            IsSummable(singleton, exponent)));
    }

    private static Formula InsufficiencyFormula() =>
        Disp(And(
            SparseDivergentBody(),
            And(FullSummableBody(), EmptySummableBody())));

    private static Formula SparseDivergentBody()
    {
        Formula primes = F.Id("P");
        return And(
            DensityLimit(primes),
            Not(IsSummable(primes, D(1))));
    }

    private static Formula FullSummableBody()
    {
        Formula primes = F.Id("P");
        Formula prime = F.Id("p");
        Formula full = Seq(
            Forall, Sp, prime, Colon, Sp, F.Id("Primes"), Comma, Sp,
            prime, Sp, InMacro, Sp, primes);
        return And(Seq(Open, full, Close), IsSummable(primes, D(2)));
    }

    private static Formula EmptySummableBody() =>
        And(DensityLimit(Emptyset), IsSummable(Emptyset, D(1)));

    private static Formula DensityLimit(Formula support)
    {
        Formula index = F.Id("n");
        return Seq(
            Lim, Underscore, Grp(index, To, Infty), Sp,
            CountingRatio(support, index), Sp, Eq, Sp, D(0));
    }

    private static Formula CountingRatio(Formula support, Formula index) =>
        Seq(new Formula.Subscript(F.Id("r"), support), Open, index, Close);

    private static Formula Evidence(
        Formula support,
        Formula exponent,
        Formula prime) =>
        Seq(F.Id("e"), Open, support, Comma, exponent, Comma, prime, Close);

    private static Formula EvidenceFamily(Formula support, Formula exponent) =>
        Seq(F.Id("e"), Open, support, Comma, exponent, Close);

    private static Formula IsSummable(Formula support, Formula exponent) =>
        new Formula.Apply(F.Id("Summable"), [EvidenceFamily(support, exponent)]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Not(Formula value) =>
        Seq(Neg, Sp, value);
}
