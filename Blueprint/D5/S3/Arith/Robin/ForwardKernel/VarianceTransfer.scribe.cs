using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class VarianceTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact integrability and square-norm estimates for profile averages.",
        H("Variance transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profile-average-eq-unit-integral"),
                DeclarationHandle.Create(Prefix + "profileAverage_eq_unit_integral"),
                H("The unit-interval formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real length h, including h=0, the normalized profile primitive equals the integral of g(s) times the increment of length s*h over the unit interval, divided by h. The substitution u=s*h proves the identity; totalized division handles zero length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("profile-cauchy-schwarz"),
                DeclarationHandle.Create(Prefix + "profile_cauchy_schwarz"),
                H("Weighted Cauchy-Schwarz"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If g is integrable on the unit interval and k is measurable and bounded in absolute value by a nonnegative M, then the square of the integral of g*k is at most the integral of absolute g times the integral of absolute g times k squared. Apply Cauchy-Schwarz to the square root of absolute g and its product with absolute k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interval-cauchy-schwarz"),
                DeclarationHandle.Create(Prefix + "interval_cauchy_schwarz"),
                H("Interval Cauchy-Schwarz"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For b>0, if f and f squared are integrable on [0,b], the square of the integral of f is at most b times the integral of f squared."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("logarithmic-variance-mono"),
                DeclarationHandle.Create(Prefix + "logarithmic_variance_mono"),
                H("Monotonicity of the variance majorant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real function t*log(2/t)^2 is increasing on (0,1/16]. Its derivative is log(2/t)^2-2*log(2/t), which is nonnegative on this interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-increment-integrable"),
                DeclarationHandle.Create(Prefix + "unit_increment_integrable"),
                H("Integrability of profile-weighted increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a locally bounded measurable E and an integrable unit profile g, the function g(s)*(E(x+s*h)-E(x)) is integrable on the unit interval for every real h and x. Compactness bounds the increment, so multiplication by it preserves integrability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("increment-comp-integrable-on"),
                DeclarationHandle.Create(Prefix + "increment_comp_integrableOn"),
                H("Compact integrability of increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If E is locally bounded and measurable, continuous real choices of step and starting point give integrable increments on any compact set, for any Borel measure finite on compact sets. Compact images bound both evaluations of E."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("increment-product-comp-integrable-on"),
                DeclarationHandle.Create(Prefix + "increment_product_comp_integrableOn"),
                H("Compact integrability of products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two increments of a locally bounded measurable E, each with continuous step and starting point, have integrable product on any compact set with a Borel measure finite on compact sets. This includes rectangular parameter domains used to exchange integrals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("increment-sq-rectangle-integrable"),
                DeclarationHandle.Create(Prefix + "increment_sq_rectangle_integrable"),
                H("Joint square integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a finite rectangle, the square of an increment is integrable with respect to the product of the two restricted Lebesgue measures when the starting point is the first coordinate and the step is any continuous function of both coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lp-norm-two-eq-interval-l2"),
                DeclarationHandle.Create(Prefix + "lpNorm_two_eq_intervalL2"),
                H("Interval L2 and lpNorm conversion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an almost everywhere measurable real function on an ordered finite interval, its lpNorm at exponent two on the restricted interval measure equals the square-root interval L2 norm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("interval-l2-reverse-triangle"),
                DeclarationHandle.Create(Prefix + "interval_l2_reverse_triangle"),
                H("The reverse triangle inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For square-integrable real functions f and g on an ordered interval [a,b], the absolute difference between the square roots of their square integrals is at most the square root of the square integral of f-g. This follows from the two triangle inequalities for the L2 norm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-min-unit-square"),
                DeclarationHandle.Create(Prefix + "integral_min_unit_square"),
                H("The covariance constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The iterated integral of min(s,t) over the unit square equals 1/3. Splitting the inner integral at t=s gives s-s^2/2."))),
                DescribeRole.Theorem))));
}
