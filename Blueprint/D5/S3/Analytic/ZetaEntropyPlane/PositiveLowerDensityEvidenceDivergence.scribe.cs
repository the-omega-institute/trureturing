using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaEntropyPlane;

internal sealed class PositiveLowerDensityEvidenceDivergenceDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive lower prime density forces reciprocal evidence divergence.",
        H("Positive Lower Density Evidence Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-relative-counting-ratio"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeRelativeCountingRatio"),
                H("Prime-relative counting ratio"),
                StatementSource.FromAuthor(PrimeRelativeCountingRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ratio counts selected members among the first n primes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-lower-relative-density"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "HasPositiveLowerRelativeDensity"),
                H("Positive lower relative density"),
                StatementSource.FromAuthor(PositiveLowerDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Eventually, selected prime indices occupy a fixed positive fraction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-endpoint-relative-ratio"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeRelativeCountingRatio_zero"),
                H("Every prime-relative ratio is zero at zero"),
                StatementSource.FromAuthor(ZeroEndpointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At n equal to zero, totalized division makes every ratio zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-relative-ratio-zero"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "empty_primeRelativeCountingRatio_tendsto_zero"),
                H("Empty support has zero relative ratio"),
                StatementSource.FromAuthor(EmptyRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty support has prime-relative counting ratio tending to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-not-positive-lower-density"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "empty_not_hasPositiveLowerRelativeDensity"),
                H("Empty support has no positive lower density"),
                StatementSource.FromAuthor(EmptyNotPositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An eventually positive counting fraction excludes empty support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-support-positive-lower-density"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "primeNaturals_hasPositiveLowerRelativeDensity"),
                H("Full prime support has positive lower density"),
                StatementSource.FromAuthor(FullPositiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All prime indices are selected, so the relative density is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("restricted-reciprocal-divergence"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "restricted_reciprocal_evidence_not_summable"),
                H("Restricted reciprocal evidence diverges"),
                StatementSource.FromAuthor(RestrictedDivergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positive lower density yields a linear enumeration bound and divergence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventual-lower-bound-divergence"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "positive_lower_density_evidence_not_summable"),
                H("An eventual reciprocal lower bound forces divergence"),
                StatementSource.FromAuthor(EvidenceDivergenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive c over p lower bound transfers reciprocal divergence to e."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-evidence-summable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_prime_evidence_summable"),
                H("Zero prime evidence is summable"),
                StatementSource.FromAuthor(ZeroSummableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant-zero family records the trivial-map degeneration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-coefficient-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "positive_coefficient_is_necessary"),
                H("A positive coefficient is necessary"),
                StatementSource.FromAuthor(CoefficientNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At c equal to zero, full support permits summable zero evidence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-density-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "positive_lower_density_is_necessary"),
                H("Positive lower density is necessary"),
                StatementSource.FromAuthor(DensityNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Empty support makes the lower bound vacuous and zero evidence summable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocal-bound-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "reciprocal_lower_bound_is_necessary"),
                H("The reciprocal lower bound is necessary"),
                StatementSource.FromAuthor(LowerBoundNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Zero evidence on full support violates the coefficient-one bound."))),
                DescribeRole.Theorem))));

    private static Formula PrimeRelativeCountingRatioFormula()
    {
        Formula support = F.Id("S");
        Formula index = F.Id("n");
        return Disp(new Formula.Relation(
            Ratio(support, index),
            FormulaRelationOperator.Equal,
            new Formula.Fraction(Count(support, index), index)));
    }

    private static Formula PositiveLowerDensityFormula()
    {
        Formula support = F.Id("S");
        Formula coefficient = F.Id("m");
        Formula index = F.Id("n");
        Formula bound = new Formula.Relation(
            index,
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Binary(
                coefficient,
                FormulaBinaryOperator.Multiply,
                Count(support, index)));
        return Disp(Seq(
            Exists, Sp, coefficient, Sp, Gt, Sp, D(0), Comma, Sp,
            Forall, Sp, index, Sp, To, Sp, Infty, Comma, Sp, bound));
    }

    private static Formula EmptyRatioFormula()
    {
        Formula index = F.Id("n");
        return Disp(Seq(
            Lim, Underscore, Grp(index, To, Infty), Sp,
            Ratio(Emptyset, index), Sp, Eq, Sp, D(0)));
    }

    private static Formula ZeroEndpointFormula()
    {
        Formula support = F.Id("S");
        return Disp(new Formula.Relation(
            Ratio(support, D(0)),
            FormulaRelationOperator.Equal,
            D(0)));
    }

    private static Formula EmptyNotPositiveFormula() =>
        Disp(Not(PositiveDensity(Emptyset)));

    private static Formula FullPositiveFormula() =>
        Disp(PositiveDensity(F.Id("P")));

    private static Formula RestrictedDivergenceFormula()
    {
        Formula support = F.Id("S");
        return Disp(Seq(
            PositiveDensity(support), Sp, Implies, Sp,
            Not(IsSummable(RestrictedEvidence(support)))));
    }

    private static Formula EvidenceDivergenceFormula()
    {
        Formula support = F.Id("S");
        Formula evidence = F.Id("e");
        Formula coefficient = F.Id("c");
        Formula lowerBound = Seq(
            coefficient, Sp, Gt, Sp, D(0), Comma, Sp,
            F.Id("eventually"), Open,
            new Formula.Fraction(coefficient, F.Id("p")),
            Sp, Leq, Sp, evidence, Close);
        return Disp(Seq(
            PositiveDensity(support), Comma, Sp, lowerBound, Sp, Implies, Sp,
            Not(IsSummable(evidence))));
    }

    private static Formula ZeroSummableFormula() =>
        Disp(IsSummable(D(0)));

    private static Formula CoefficientNecessaryFormula() =>
        Disp(And(
            PositiveDensity(F.Id("P")),
            And(BoundAt(D(0), F.Id("P"), D(0)), IsSummable(D(0)))));

    private static Formula DensityNecessaryFormula() =>
        Disp(And(
            Not(PositiveDensity(Emptyset)),
            And(BoundAt(D(1), Emptyset, D(0)), IsSummable(D(0)))));

    private static Formula LowerBoundNecessaryFormula() =>
        Disp(And(
            PositiveDensity(F.Id("P")),
            And(Not(BoundAt(D(1), F.Id("P"), D(0))), IsSummable(D(0)))));

    private static Formula Ratio(Formula support, Formula index) =>
        Seq(F.Id("r"), Open, support, Comma, index, Close);

    private static Formula Count(Formula support, Formula index) =>
        Seq(F.Id("A"), Open, support, Comma, index, Close);

    private static Formula PositiveDensity(Formula support) =>
        new Formula.Apply(F.Id("PositiveLowerDensity"), [support]);

    private static Formula RestrictedEvidence(Formula support) =>
        Seq(F.Id("e"), Open, support, Comma, D(1), Close);

    private static Formula IsSummable(Formula evidence) =>
        new Formula.Apply(F.Id("Summable"), [evidence]);

    private static Formula BoundAt(
        Formula coefficient,
        Formula support,
        Formula evidence) =>
        Seq(
            F.Id("bound"), Open, coefficient, Comma, support, Comma,
            evidence, Close);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Not(Formula value) =>
        Seq(Neg, Sp, value);
}
