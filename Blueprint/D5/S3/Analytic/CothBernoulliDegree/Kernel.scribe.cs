using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.CothBernoulliDegree;

internal sealed class KernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivative certificates and estimates for rational kernels.",
        H("Rational kernels"), Blocks(
            Describe.Lean(DescribeId.Create("coth-kernel-deriv-n"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Kernel.kernel_deriv_N"),
                H("The rational derivative certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive scale a, the Nth derivative of t^(N+2)/(t^2+a^2) equals N! times one minus the real part of (1+i t/a)^(-(N+1)). The proof differentiates a complex rational function and takes its real part. Its recurrence separates a polynomial term from a simple pole."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coth-kernel-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Kernel.kernel_deriv_N_pos"),
                H("Strict positivity on the positive ray"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When a and t are positive, the modulus of 1+i t/a is greater than one. Its negative power has real part strictly below one, so the Nth derivative in the certificate is strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coth-kernel-deriv-succ"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Kernel.kernel_deriv_succ"),
                H("The phase and amplitude formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative of order N+1 equals (N+1)!/a times (1+(t/a)^2)^(-(N+2)/2) times sin((N+2) arctan(t/a)). The scale factor is exactly a^(-1). This follows by differentiating the complex certificate and applying the polar form of a complex power."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coth-kernel-phase-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Kernel.phase_bound"),
                H("A uniform negative phase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real M at least five, the product of (1+(5/M)^2)^(-M/2) and sin(M arctan(5/M)) is at most -1/8. The arctangent lies above its chord on [0,1], while log(1+x^2) lies below its chord. These give a phase between 5 pi/4 and 5 and an amplitude at least sqrt(2)/8. The sine is at most -sqrt(2)/2 throughout that interval. Equality holds at M=5."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coth-kernel-tail-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Kernel.tail_bound"),
                H("The reciprocal-power tail"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n at least two, the sum over natural k of 1/(k+2)^(2n+1) is at most 1/16. Each term is bounded by (1/(k+1)-1/(k+2))/16. The latter series telescopes; bounded nonnegative partial sums yield the asserted infinite-sum inequality."))),
                DescribeRole.Theorem))));
}
