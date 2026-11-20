using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ChenFixedOrder;

internal sealed class GaussianLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/ChenFixedOrder/GaussianLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Gaussian limit for the balanced-sign estimator under uniform fixed-size sampling.",
        H("Gaussian limit for balanced finite populations"),
        Blocks(
            Paragraph(Text(
                "At stage m the sample size n is (m+1)^2. The two strata each contain n^3 labels, "
                    + "with values +1 and -1 respectively. The population mean is zero. For both "
                    + "ordered draws and subsets of size n, the estimator is the sample mean "
                    + "minus the population mean, multiplied by the square root of n.")),
            Describe.Lean(
                DescribeId.Create("chen-with-replacement-gaussian-limit"),
                DeclarationHandle.Create(Prefix + "withReplacement_tendsto"),
                H("Independent draws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The uniform label law gives each sign probability 1/2. Its independent "
                        + "product, mapped coordinatewise to signs, agrees with the corresponding "
                        + "finite restriction of the infinite Bernoulli product. The centered "
                        + "estimator is the normalized partial sum in the i.i.d. central limit "
                        + "theorem, along the subsequence of square sample sizes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chen-draw-collision-bound"),
                DeclarationHandle.Create(Prefix + "collisionMass_le"),
                H("Collision probability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each pair of distinct draw positions has equal labels with probability at "
                        + "most the inverse population size. The union bound over the ordered "
                        + "position pairs gives at most n^2/(2n^3), which tends to zero. The event "
                        + "of distinct labels has positive probability at every stage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chen-distinct-draw-test-bound"),
                DeclarationHandle.Create(Prefix + "distinctLaw_test_bound"),
                H("Effect of conditioning"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any measurable real test bounded in absolute value by C, the difference "
                        + "between its conditional and unconditional estimator expectations has "
                        + "absolute value at most twice C times the collision probability. This "
                        + "follows by splitting the unconditional integral over the distinct "
                        + "event and its complement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chen-distinct-draw-gaussian-limit"),
                DeclarationHandle.Create(Prefix + "distinctLaw_tendsto"),
                H("Conditioned estimator law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each bounded continuous test, the difference from its with-replacement "
                        + "expectation tends to zero. The estimator law given distinct labels "
                        + "therefore converges weakly to the standard Gaussian."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chen-uniform-subset-gaussian-limit"),
                DeclarationHandle.Create(Prefix + "uniformSampleLaw_tendsto"),
                H("Estimator law on uniform subsets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite sampling transport theorem maps the conditioned draw law to "
                        + "the uniform law on subsets of size n by erasing positions. This "
                        + "preserves the sum of the values when the labels are distinct. The "
                        + "resulting estimator law, whose underlying measure is the baseline "
                        + "of the density bridge, converges weakly to the standard Gaussian."))),
                DescribeRole.Theorem))));
}
