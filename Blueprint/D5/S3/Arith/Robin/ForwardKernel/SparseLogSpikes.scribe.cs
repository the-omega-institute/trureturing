using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class SparseLogSpikesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/SparseLogSpikes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometrically separated logarithmic spikes give a continuous perturbation with controlled amplitudes.",
        H("Sparse logarithmic spikes"),
        Blocks(
            Paragraph(Text(
                "The centers are X_n=10^n, the radii are X_n^a and X_n^b, and "
                + "the amplitudes are sqrt(X_n*log(X_n)/log(log(X_n))). An admissible "
                + "starting index makes every outer radius at most X_n/10. "
                + "The existing support separation and locally finite support family "
                + "allow the sum to be treated as a finite sum near every point.")),
            Describe.Lean(
                DescribeId.Create("spike-support-tenth"),
                DeclarationHandle.Create(Prefix + "spike_support_tenth"),
                H("Support near the center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every admissible spike is supported in [0.9*X_n,1.1*X_n]. "
                    + "This locates the centers that can contribute to a variance integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-continuous"),
                DeclarationHandle.Create(Prefix + "perturbation_continuous"),
                H("Continuity of the sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an admissible start the perturbation is continuous. The sum has "
                    + "finite support at each point, so its infinite sum equals its finite-support "
                    + "sum, and the locally finite family of continuous summands gives continuity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-locally-bounded-measurable"),
                DeclarationHandle.Create(Prefix + "perturbation_locallyBoundedMeasurable"),
                H("Local boundedness and measurability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The perturbation is Borel measurable and bounded on every closed finite "
                    + "interval. These are the regularity hypotheses used when perturbing variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-eq-spike-on"),
                DeclarationHandle.Create(Prefix + "perturbation_eq_spike_on"),
                H("Isolation on three center lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n at or above the starting index and x in [X_n,3*X_n], "
                    + "the perturbation equals its n-th spike. Every earlier and every later "
                    + "spike vanishes throughout this interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-forward-eq-spike"),
                DeclarationHandle.Create(Prefix + "perturbation_forward_eq_spike"),
                H("Isolation of complete forward ranges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x in [X_n,2*X_n] and 0<=u<=2*X_n^b, the value at x+u "
                    + "is exactly the n-th spike. This covers all forward increments in "
                    + "the transport of the two moving lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplitude-ratio-tendsto"),
                DeclarationHandle.Create(Prefix + "amplitude_ratio_tendsto"),
                H("The amplitude ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ratio of consecutive amplitudes tends to sqrt(10). The identity "
                    + "log(X_(n+1))=log(X_n)+log(10) reduces both logarithmic correction "
                    + "factors to ratios tending to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("amplitude-partial-sum-bound"),
                DeclarationHandle.Create(Prefix + "amplitude_partial_sum_bound"),
                H("Summing the amplitudes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a fixed positive constant C such that, for all sufficiently "
                    + "large m, the sum of amplitudes from zero through m is at most C times "
                    + "the m-th amplitude. Consecutive amplitudes eventually at least double; "
                    + "a fixed initial sum is absorbed in C. This supplies the coefficient "
                    + "estimate for the sparse perturbation variance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("perturbation-pointwise-bound"),
                DeclarationHandle.Create(Prefix + "perturbation_pointwise_bound"),
                H("Pointwise growth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a<b, the perturbation is O(sqrt(x)*(log(x))^(3/2)/sqrt(log(log(x)))) "
                    + "as x tends to infinity. At a nonzero point only one spike contributes. "
                    + "Its depth is at most (b-a)*log(X_n), and x and X_n differ by at most "
                    + "a factor of two on its support. The logarithmic factors are compared "
                    + "explicitly there. This gives the pointwise estimate in the final "
                    + "near-optimality theorem."))),
                DescribeRole.Theorem))));
}
