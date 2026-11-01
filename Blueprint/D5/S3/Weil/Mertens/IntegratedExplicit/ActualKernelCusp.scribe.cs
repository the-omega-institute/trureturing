using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualKernelCuspDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete arithmetic kernel has an explicit quadratic error after its logarithmic cusp and linear coefficient are removed.",
        H("A quadratic cusp remainder for the actual arithmetic kernel"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-kernel-cusp-coefficient"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp.c"),
                H("The linear coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real constant c is (EulerGamma-1+log(2*pi))/2. EulerGamma is Mathlib's real Euler-Mascheroni constant."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-kernel-cusp-remainder"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp.R"),
                H("Subtracting the full cusp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real t, R(t)=K(t)-M-(t/2)*log(t)-c*t, where K is ActualKernelLocalPositivity.K and M is ActualReciprocalSquareBounds.firstLiMass=2+EulerGamma-log(4*pi). The complete Mangoldt ramps and the entire trivial-zero series remain in K. R(0)=0 with Mathlib's total real logarithm convention."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-kernel-cusp-uniform"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp.cusp_remainder_bound"),
                H("A uniform error on an explicit interval"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real t satisfying 0<t and t<=1/2, abs(R(t))<=2*t^2. Both the constant 2 and the closed upper endpoint 1/2 are explicit. There is no Riemann-hypothesis premise.")),
                    Paragraph(Text("The interval lies below log(2), so the existing exact local formula applies. Elementary exponential, Euler-constant, logarithmic and complete trivial-tail bounds give -3<=K(t)<=5 and 1<=exp(t/2)<=2. The exponential tangent inequalities imply -1<=1/(exp(x)-1)-1/x<=0 for every positive x. After multiplication by exp(-t/2), the singular quotient minus 1/(2*t) lies between -5/4 and zero. Consequently the renormalized curvature has absolute value at most 4.")),
                    Paragraph(Text("For 0<t<log(2), R'(t)=D1(t)-(log(t)+1)/2-c and R''(t)=D2(t)-1/(2*t). The right limit of R' is zero. The mean value bound on positive subintervals, followed by the endpoint limit, gives abs(R'(t))<=4*t. The functions 2*t^2+R(t) and 2*t^2-R(t) are then increasing from zero, proving the stated quadratic bound. Differentiability of K at zero and integrability of 1/t are not used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-kernel-cusp-exact-coefficient"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp.cusp_quadratic_limit"),
                H("The exact second-order coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("As the real variable t tends to zero through positive values, R(t)/t^2 tends to (M-7)/8. Thus the uniform quadratic remainder has a specified asymptotic coefficient, strengthening the local O(t^2*abs(log(t))) expansion.")),
                    Paragraph(Text("The existing ratio t/(1-exp(-2*t))->1/2 identifies log(1-exp(-2*t))-log(t)->log(2). Combining the exponential slope at zero with t*log(t)->0 identifies the limit of R'. The finite part exp(-t/2)/(exp(2*t)-1)-1/(2*t) is treated as the quotient with numerator 2*t*exp(-t/2)-exp(2*t)+1 and denominator 2*t*(exp(2*t)-1). Both vanish through first order; their second derivatives at zero are -6 and 8. Two right-sided applications of l'Hopital give the finite part -3/4, hence R''(t)->(M-7)/4. Two further right-sided applications give the coefficient (M-7)/8.")),
                    Paragraph(Text("These estimates concern a fixed neighborhood of the origin for the literal arithmetic kernel. They provide quantitative local input for positivity and Schur-insertion arguments. Uniform Schur control across arbitrarily distant blocks, global positive definiteness, and the full Robin residual remain separate mathematical obligations."))),
                DescribeRole.Theorem))));
}
