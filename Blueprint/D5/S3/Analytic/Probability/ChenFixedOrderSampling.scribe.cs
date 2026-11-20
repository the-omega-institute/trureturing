using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class ChenFixedOrderSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Probability/ChenFixedOrderSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fixed-size sampling and the stratum inclusion identities for Chen's fixed-order problem.",
        H("Fixed-size samples from two balanced strata"),
        Blocks(
            Paragraph(Text(
                "At stage m the sample size is (m+1)^2. Each of the two strata has the cube "
                    + "of the sample size in labels. Values are +1 in the first stratum and -1 "
                    + "in the second. The estimator centers the sample mean at the population "
                    + "mean and multiplies by the square root of the sample size.")),
            Result("chen-positive-sample-size", "sampleSize_pos", "Positive sample size",
                "The sample size is positive at every stage."),
            Result("chen-zero-population-mean", "populationMean_eq_zero", "Population mean",
                "The two strata have equal size and opposite values, so the population mean is zero."),
            Result("chen-erase-order-image", "eraseOrder_val", "Erasing order on distinct draws",
                "For each injective ordered draw, its unordered sample is exactly the "
                    + "finite image of the draw."),
            Result("chen-condition-and-erase-order", "map_eraseOrder_cond_uniform",
                "Uniform law on fixed-size subsets",
                "Condition the uniform law of ordered draws on having distinct labels, "
                    + "then erase order. Every subset of the required size has the same "
                    + "number of orderings, giving the uniform subset law."),
            Result("chen-inclusion-polynomial", "exists_inclusionPolynomial",
                "Inclusion polynomial",
                "For every prescribed subset A, there is a polynomial of degree at most "
                    + "the cardinality of A such that, for every real function f, the "
                    + "uniform sample integral of f of the estimator over samples containing A "
                    + "equals its full uniform sample integral weighted by that polynomial "
                    + "of the estimator. On each cell of fixed positive-stratum count, the "
                    + "inclusion fraction is the product of two ratios of binomial coefficients. "
                    + "The two counts are affine in the estimator, giving the degree bound."))));

    private static DocumentBlock.Describe Result(string id, string declaration, string title, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
