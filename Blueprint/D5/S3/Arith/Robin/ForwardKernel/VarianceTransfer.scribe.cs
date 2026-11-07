using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class VarianceTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/VarianceTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact integrability and square-norm estimates for triangular primitives.",
        H("Variance transfer"),
        Blocks(
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
                DescribeId.Create("triangular-primitive-measurable"),
                DeclarationHandle.Create(Prefix + "triangularPrimitive_measurable"),
                H("Measurability of triangular primitives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each fixed real length, the triangular primitive of a locally bounded measurable error function is measurable in its starting point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("triangular-primitive-sq-interval-integrable"),
                DeclarationHandle.Create(Prefix + "triangularPrimitive_sq_intervalIntegrable"),
                H("Integrability of triangular squares"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The square of a fixed-length triangular primitive is integrable on every finite oriented interval. A uniform bound for increments on the parameter rectangle bounds the primitive."))),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-length-triangular-square-bound"),
                DeclarationHandle.Create(Prefix + "small_length_triangular_square_bound"),
                H("The small-length estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If E is locally bounded and measurable and satisfies the short-interval mean-square bound, there is C>0 such that, for every sufficiently large X and every 0<U<=X/16, the integral of B_U(x)^2 over [X,2X] is at most C*X*U^3*log(2*X/U)^2. Cauchy-Schwarz, the substitution u=x*theta, enlargement to a fixed rectangle, and Fubini reduce this to the short-interval bound. Monotonicity of theta*log(2/theta)^2 on (0,1/16] bounds its integral."))),
                DescribeRole.Theorem))));
}
