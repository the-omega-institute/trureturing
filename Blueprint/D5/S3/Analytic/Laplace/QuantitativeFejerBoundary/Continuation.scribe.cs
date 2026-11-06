using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace.QuantitativeFejerBoundary;

internal sealed class ContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/Continuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Laplace transforms and paired pole sums admit analytic continuation on right strips.",
        H("Continuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("has-log-envelope"),
                DeclarationHandle.Create(Prefix + "HasLogEnvelope"),
                H("A one-sided logarithmic envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real function has a logarithmic envelope if either it or its negative is bounded above on the nonnegative ray by kappa times log(exp(1)+u) plus C, with kappa and C nonnegative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("admissible"),
                DeclarationHandle.Create(Prefix + "Admissible"),
                H("Fejer kernels with bounded Fourier support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An admissible pair consists of a Fejer kernel of bandwidth b and its tent Fourier weight with b at most M, or a notched Fejer kernel with notch ordinate U greater than twice b and U+b at most M."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ray-measure"),
                DeclarationHandle.Create(Prefix + "rayMeasure"),
                H("A weighted measure on the nonnegative ray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real function q, the ray measure is Lebesgue measure restricted to the nonnegative ray, with density given by the nonnegative extended-real value of q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ray-integrable-iff"),
                DeclarationHandle.Create(Prefix + "ray_integrable_iff"),
                H("Weighted exponential integrability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For measurable q nonnegative on the nonnegative ray, exp(t*u) is integrable against its ray measure exactly when q(u)*exp(t*u) is Lebesgue integrable on that ray."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-mgf"),
                DeclarationHandle.Create(Prefix + "ray_mgf"),
                H("The moment generating function as a Laplace transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For measurable q nonnegative on the nonnegative ray, the complex moment generating function of its ray measure at -s equals the Laplace transform of q at s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ray-nonneg"),
                DeclarationHandle.Create(Prefix + "ray_nonneg"),
                H("Nonnegative support of the ray measure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coordinate is nonnegative almost everywhere with respect to every ray measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exp-integrable"),
                DeclarationHandle.Create(Prefix + "exp_integrable"),
                H("Exponential decay on the nonnegative ray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive sigma, exp(-sigma*u) is integrable over the nonnegative ray."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("affine-integrable"),
                DeclarationHandle.Create(Prefix + "affine_integrable"),
                H("Exponentially damped affine functions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every affine real function multiplied by exp(-sigma*u) is integrable over the nonnegative ray whenever sigma is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laplace-integrable"),
                DeclarationHandle.Create(Prefix + "laplace_integrable"),
                H("Absolute convergence of the complex Laplace integrand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If q is measurable and q(u)*exp(-Re(s)*u) is integrable over the nonnegative ray, then q(u)*exp(-s*u) is integrable there as a complex function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strip"),
                DeclarationHandle.Create(Prefix + "strip"),
                H("A bounded right strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The strip consists of complex s with real part strictly between zero and one and imaginary part of absolute value less than one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("continuation"),
                DeclarationHandle.Create(Prefix + "continuation"),
                H("A finite pole expression for continuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a spectrum S and remainder J, the continuation is minus one half of the paired pole sum over ordinates at most eight, plus the regular part with parameter four."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("continuation-holomorphic"),
                DeclarationHandle.Create(Prefix + "continuation_holomorphic"),
                H("Holomorphy of the continued pole expression"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive spectrum with logarithmic counting asymptotics and paired Laplace data, the finite pole continuation is complex differentiable on the bounded right strip."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuation-initial"),
                DeclarationHandle.Create(Prefix + "continuation_initial"),
                H("Agreement on the initial convergence strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under logarithmic counting asymptotics and paired Laplace data, the Laplace transform agrees with the finite pole continuation whenever the real part lies strictly between one half and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-convergence"),
                DeclarationHandle.Create(Prefix + "positive_convergence"),
                H("Positivity extends Laplace convergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a measure be supported almost everywhere on the nonnegative ray and suppose its damped exponentials are integrable for every sigma greater than one half. If its complex transform agrees there with a holomorphic function on the bounded right strip, the damped exponentials are integrable for every positive sigma."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("affine-mgf-holomorphic"),
                DeclarationHandle.Create(Prefix + "affine_mgf_holomorphic"),
                H("Holomorphic transforms of nonnegative affine densities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An affine density nonnegative on the nonnegative ray has a complex moment generating function at -s that is complex differentiable throughout the bounded right strip."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laplace-sub-const-mul"),
                DeclarationHandle.Create(Prefix + "laplace_sub_const_mul"),
                H("Linearity of convergent Laplace transforms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For measurable a and f whose Laplace integrands are absolutely integrable at s, the Laplace transform of a-e*f equals the transform of a minus e times the transform of f."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-strip"),
                DeclarationHandle.Create(Prefix + "rightStrip"),
                H("The full right strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The full right strip consists of all complex numbers whose real parts lie strictly between zero and one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("right-strip-open"),
                DeclarationHandle.Create(Prefix + "rightStrip_open"),
                H("Openness of the full right strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set of complex numbers with real part strictly between zero and one is open."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-strip-convex"),
                DeclarationHandle.Create(Prefix + "rightStrip_convex"),
                H("Convexity of the full right strip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set of complex numbers with real part strictly between zero and one is convex over the reals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laplace-holomorphic"),
                DeclarationHandle.Create(Prefix + "laplace_holomorphic"),
                H("Holomorphy from absolute Laplace convergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A measurable real function whose damped integrands are integrable on the nonnegative ray for every positive real parameter has a complex differentiable Laplace transform throughout the full right strip."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-tsum-holomorphic"),
                DeclarationHandle.Create(Prefix + "pole_tsum_holomorphic"),
                H("Holomorphy of the full paired pole sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive spectrum with logarithmic counting asymptotics, the sum of all paired pole terms is complex differentiable throughout the full right strip, away from the poles. At a pole the Lean expression uses the convention 1/0 = 0."))),
                DescribeRole.Theorem))));
}
