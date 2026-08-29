using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class MinimalSufficientRelationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-size positive zeta samples have a parameter-independent likelihood ratio "
            + "exactly when their products agree.",
        H("Minimal Sufficient Relation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeta-parameter-definition"),
                DeclarationHandle.Create(Prefix + "ZetaParameter"),
                H("Admissible zeta parameters lie above one"),
                StatementSource.FromAuthor(ZetaParameterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named parameter type records the normalization threshold."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sample-product-definition"),
                DeclarationHandle.Create(Prefix + "sampleProduct"),
                H("The sample product is the multiplicative statistic"),
                StatementSource.FromAuthor(SampleProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A finite natural-number sample is summarized by its product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("total-log-energy-definition"),
                DeclarationHandle.Create(Prefix + "totalLogEnergy"),
                H("Total log energy sums the logarithms of sample entries"),
                StatementSource.FromAuthor(TotalLogEnergyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the additive form of the multiplicative statistic."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeta-sample-likelihood-definition"),
                DeclarationHandle.Create(Prefix + "zetaSampleLikelihood"),
                H("The sample likelihood is the product of zeta point masses"),
                StatementSource.FromAuthor(SampleLikelihoodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The joint likelihood uses the repository zeta Gibbs PMF."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeta-likelihood-ratio-definition"),
                DeclarationHandle.Create(Prefix + "zetaLikelihoodRatio"),
                H("The likelihood ratio compares two sample likelihoods"),
                StatementSource.FromAuthor(LikelihoodRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ratio remains defined for unequal samples and zero entries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parameter-independence-definition"),
                DeclarationHandle.Create(Prefix + "zetaRatioParameterIndependent"),
                H("Parameter independence means equality at every two parameters"),
                StatementSource.FromAuthor(ParameterIndependentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This named relation is the minimal-sufficiency criterion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeta-sample-likelihood-closed-form"),
                DeclarationHandle.Create(Prefix + "zeta_sample_likelihood_eq"),
                H("The joint likelihood separates weight and normalization"),
                StatementSource.FromAuthor(LikelihoodClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One inverse partition factor appears for every sample entry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-size-likelihood-ratio"),
                DeclarationHandle.Create(
                    Prefix + "zeta_likelihood_ratio_eq_product_ratio_rpow"),
                H("Equal sample sizes cancel the partition function"),
                StatementSource.FromAuthor(RatioClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After cancellation only the ratio of sample products remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sample-product-minimal-sufficient-relation"),
                DeclarationHandle.Create(
                    Prefix + "sample_product_is_minimal_sufficient_relation"),
                H("The product characterizes parameter-independent ratios"),
                StatementSource.FromAuthor(MinimalRelationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive samples of equal length, independence is equivalent "
                        + "to equality of products."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("total-log-energy-log-product"),
                DeclarationHandle.Create(
                    Prefix + "total_log_energy_eq_log_sample_product"),
                H("Total log energy is the logarithm of the sample product"),
                StatementSource.FromAuthor(LogEnergyClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Nonzero entries make the logarithmic product identity valid."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-equality-log-energy-equality"),
                DeclarationHandle.Create(
                    Prefix + "sample_product_eq_iff_total_log_energy_eq"),
                H("Product equality is equivalent to log-energy equality"),
                StatementSource.FromAuthor(ProductEnergyEquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strict monotonicity of the logarithm identifies both statistics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-samples-parameter-independent"),
                DeclarationHandle.Create(Prefix + "empty_samples_parameter_independent"),
                H("Empty samples have the neutral statistic and constant ratio"),
                StatementSource.FromAuthor(EmptySamplesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty product is one and the empty log-energy sum is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-parameter-independence"),
                DeclarationHandle.Create(Prefix + "singleton_parameter_independent_iff"),
                H("Singleton independence is equality of the entries"),
                StatementSource.FromAuthor(SingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The one-sample case reduces the product criterion to equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-entry-neutrality"),
                DeclarationHandle.Create(Prefix + "one_entry_is_neutral"),
                H("An entry equal to one changes neither statistic"),
                StatementSource.FromAuthor(OneNeutralFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication by one and addition of log one are neutral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("permutation-parameter-independence"),
                DeclarationHandle.Create(Prefix + "perm_samples_parameter_independent"),
                H("Permuting a positive sample preserves its likelihood relation"),
                StatementSource.FromAuthor(PermutationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal multisets have equal products, lengths, and likelihoods."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ratio-changes-between-two-and-three"),
                DeclarationHandle.Create(
                    Prefix + "likelihood_ratio_changes_between_two_and_three"),
                H("A concrete unequal-product ratio varies with the parameter"),
                StatementSource.FromAuthor(RatioWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Samples two and one give distinct ratios at parameters two and three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("numerator-nonzero-necessary"),
                DeclarationHandle.Create(Prefix + "numerator_nonzero_is_necessary"),
                H("Numerator nonzeroness is necessary"),
                StatementSource.FromAuthor(NumeratorZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A zero numerator makes the ratio constant despite unequal products."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("denominator-nonzero-necessary"),
                DeclarationHandle.Create(Prefix + "denominator_nonzero_is_necessary"),
                H("Denominator nonzeroness is necessary"),
                StatementSource.FromAuthor(DenominatorZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Totalized division at a zero denominator defeats the criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-sample-size-necessary"),
                DeclarationHandle.Create(Prefix + "equal_sample_size_is_necessary"),
                H("Equal sample size is necessary for cancellation"),
                StatementSource.FromAuthor(EqualSizeNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The samples one and empty have equal products but differing "
                        + "normalization powers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-temperature-bound-necessary"),
                DeclarationHandle.Create(
                    Prefix + "inverse_temperature_bound_is_necessary"),
                H("The inverse-temperature threshold is necessary"),
                StatementSource.FromAuthor(ParameterBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At parameter one the partition function is infinite."))),
                DescribeRole.Theorem))));

    private static Formula ZetaParameterFormula()
    {
        Formula s = F.Id("s");
        return F.Disp(Equal(Call("ZetaParameter"), Call("Subtype", GreaterThanOne(s))));
    }

    private static Formula SampleProductFormula()
    {
        Formula sample = F.Id("N"), n = F.Id("n");
        Formula product = F.Seq(
            F.Prod, F.Underscore, F.Grp(n, F.InMacro, F.Sp, sample), F.Sp, n);
        return F.Disp(Equal(Call("SampleProduct", sample), product));
    }

    private static Formula TotalLogEnergyFormula()
    {
        Formula sample = F.Id("N"), n = F.Id("n");
        Formula sum = F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.InMacro, F.Sp, sample), F.Sp, Call("Log", n));
        return F.Disp(Equal(Call("TotalLogEnergy", sample), sum));
    }

    private static Formula SampleLikelihoodFormula()
    {
        Formula sample = F.Id("N"), n = F.Id("n"), s = F.Id("s");
        Formula product = F.Seq(
            F.Prod, F.Underscore, F.Grp(n, F.InMacro, F.Sp, sample), F.Sp,
            Call("ZetaPointMass", s, n));
        return F.Disp(Equal(Likelihood(s, sample), product));
    }

    private static Formula LikelihoodRatioFormula()
    {
        Formula s = F.Id("s"), numerator = F.Id("N"), denominator = F.Id("M");
        Formula ratio = new Formula.Fraction(
            Likelihood(s, numerator), Likelihood(s, denominator));
        return F.Disp(Equal(Ratio(s, numerator, denominator), ratio));
    }

    private static Formula ParameterIndependentFormula()
    {
        Formula numerator = F.Id("N"), denominator = F.Id("M");
        Formula s = F.Id("s"), t = F.Id("t");
        Formula equality = Equal(
            Ratio(s, numerator, denominator), Ratio(t, numerator, denominator));
        return F.Disp(Equal(
            Independent(numerator, denominator), Call("ForAllParameters", s, t, equality)));
    }

    private static Formula LikelihoodClosedFormula()
    {
        Formula s = F.Id("s"), sample = F.Id("N"), length = Call("Length", sample);
        Formula weight = Call(
            "Rpow", Call("SampleProduct", sample), F.Seq(F.Minus, s));
        Formula normalization = Call("Rpow", Call("InversePartition", s), length);
        return F.Disp(Equal(
            Likelihood(s, sample), F.Seq(weight, F.Sp, F.Cdot, F.Sp, normalization)));
    }

    private static Formula RatioClosedFormula()
    {
        Formula s = F.Id("s"), numerator = F.Id("N"), denominator = F.Id("M");
        Formula premise = Equal(Call("Length", numerator), Call("Length", denominator));
        Formula baseRatio = new Formula.Fraction(
            Call("SampleProduct", denominator), Call("SampleProduct", numerator));
        Formula conclusion = Equal(
            Ratio(s, numerator, denominator), Call("Rpow", baseRatio, s));
        return F.Disp(Implies(premise, conclusion));
    }

    private static Formula MinimalRelationFormula()
    {
        Formula numerator = F.Id("N"), denominator = F.Id("M");
        Formula positive = And(
            Call("PositiveSample", numerator), Call("PositiveSample", denominator));
        Formula sameLength = Equal(Call("Length", numerator), Call("Length", denominator));
        Formula criterion = Iff(
            Independent(numerator, denominator),
            Equal(Call("SampleProduct", numerator), Call("SampleProduct", denominator)));
        return F.Disp(Implies(And(positive, sameLength), criterion));
    }

    private static Formula LogEnergyClosedFormula()
    {
        Formula sample = F.Id("N");
        Formula conclusion = Equal(
            Call("TotalLogEnergy", sample), Call("Log", Call("SampleProduct", sample)));
        return F.Disp(Implies(Call("PositiveSample", sample), conclusion));
    }

    private static Formula ProductEnergyEquivalenceFormula()
    {
        Formula first = F.Id("N"), second = F.Id("M");
        Formula positive = And(Call("PositiveSample", first), Call("PositiveSample", second));
        Formula products = Equal(
            Call("SampleProduct", first), Call("SampleProduct", second));
        Formula energies = Equal(
            Call("TotalLogEnergy", first), Call("TotalLogEnergy", second));
        return F.Disp(Implies(positive, Iff(products, energies)));
    }

    private static Formula EmptySamplesFormula()
    {
        Formula empty = Call("EmptySample");
        Formula product = Equal(Call("SampleProduct", empty), F.D(1));
        Formula energy = Equal(Call("TotalLogEnergy", empty), F.D(0));
        return F.Disp(And(product, And(energy, Independent(empty, empty))));
    }

    private static Formula SingletonFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m");
        Formula samples = Independent(Call("Singleton", n), Call("Singleton", m));
        return F.Disp(Implies(
            And(Call("Positive", n), Call("Positive", m)), Iff(samples, Equal(n, m))));
    }

    private static Formula OneNeutralFormula()
    {
        Formula sample = F.Id("N"), extended = Call("Cons", F.D(1), sample);
        Formula product = Equal(
            Call("SampleProduct", extended), Call("SampleProduct", sample));
        Formula energy = Equal(
            Call("TotalLogEnergy", extended), Call("TotalLogEnergy", sample));
        return F.Disp(And(product, energy));
    }

    private static Formula PermutationFormula()
    {
        Formula first = F.Id("N"), second = F.Id("M");
        Formula premise = And(Call("Permutation", first, second), Call("PositiveSample", first));
        return F.Disp(Implies(premise, Independent(first, second)));
    }

    private static Formula RatioWitnessFormula()
    {
        Formula atTwo = Ratio(F.D(2), Call("Singleton", F.D(2)), Call("Singleton", F.D(1)));
        Formula atThree = Ratio(
            F.D(3), Call("Singleton", F.D(2)), Call("Singleton", F.D(1)));
        return F.Disp(NotEqual(atTwo, atThree));
    }

    private static Formula NumeratorZeroFormula()
    {
        Formula zero = Call("Singleton", F.D(0)), one = Call("Singleton", F.D(1));
        Formula products = NotEqual(Call("SampleProduct", zero), Call("SampleProduct", one));
        Formula violatesHypothesis = F.Seq(
            F.Neg, F.Sp, Call("PositiveSample", zero));
        return F.Disp(And(
            violatesHypothesis, And(Independent(zero, one), products)));
    }

    private static Formula DenominatorZeroFormula()
    {
        Formula zero = Call("Singleton", F.D(0)), one = Call("Singleton", F.D(1));
        Formula products = NotEqual(Call("SampleProduct", one), Call("SampleProduct", zero));
        Formula violatesHypothesis = F.Seq(
            F.Neg, F.Sp, Call("PositiveSample", zero));
        return F.Disp(And(
            violatesHypothesis, And(Independent(one, zero), products)));
    }

    private static Formula EqualSizeNecessaryFormula()
    {
        Formula one = Call("Singleton", F.D(1)), empty = Call("EmptySample");
        Formula products = Equal(Call("SampleProduct", one), Call("SampleProduct", empty));
        return F.Disp(And(products, F.Seq(F.Neg, F.Sp, Independent(one, empty))));
    }

    private static Formula ParameterBoundFormula()
    {
        Formula invalid = F.Seq(F.Neg, F.Sp, GreaterThanOne(F.D(1)));
        Formula divergent = Equal(Call("Partition", F.D(1)), F.Infty);
        return F.Disp(And(invalid, divergent));
    }

    private static Formula Likelihood(Formula s, Formula sample) =>
        Call("ZetaSampleLikelihood", s, sample);

    private static Formula Ratio(Formula s, Formula numerator, Formula denominator) =>
        Call("ZetaLikelihoodRatio", s, numerator, denominator);

    private static Formula Independent(Formula numerator, Formula denominator) =>
        Call("ParameterIndependent", numerator, denominator);

    private static Formula GreaterThanOne(Formula value) =>
        new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, value);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
