using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;
internal sealed class ActualKernelMomentMixtureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual-K moment certificate.",
        H("Original full-kernel certificate source"), Blocks(
            Describe.Lean(DescribeId.Create("complete-positive-mixture-head-gamma"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_head_gamma"),
                H("Finite Gamma head below the complete mixture"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D>0, q>=1, m>=1 and delta_q<=1/m, the first M terms give Re Q_P >= E sum_{n<M} c_n 2lambda_n/(1+lambda_n^2/m), with the literal positive mixture coefficients and rates. Each term consumes the division-free Gamma gap certificate; positive energy permits cancellation inside that branch, while E=0 follows from the nonnegative exponential form. The existing complete-tail theorem keeps every omitted term nonnegative. The small-window endpoints consume M=20 with m=138 and m=1600."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-positive-mixture-logarithmic"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_logarithmic"),
                H("complete positive mixture logarithmic"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete actual P(t)=exp(-abs(t)/2)trivialT(abs(t)) has Re Q_P >= (log(q/D)-1)E for q>=1, q/D>=8 and atomic moments 0,...,q zero. The retained compiled exponential-moment supplier is consumed at every actual rate 2k+1/2. Absolute coefficient domination justifies quadratic interchange, and every tail form is nonnegative. For M=floor(q/D), A_M=H_(2M+1)-1 and the exact loss is delta_q(2M^2+3M+A_M/4). Harmonic and log/floor bounds give the coefficient without dividing by E."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-p-multiplier-logarithmic-bounds"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.pMultiplier_logarithmic_bounds"),
                H("The complete logarithmic multiplier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real frequency xi, pMultiplier is the complete sum over n>=0 of (2 rate_n trivialCoeff_n) xi^2/(rate_n^2+xi^2), where rate_n=2(n+1)+1/2. The series is summable and nonnegative, its value at zero is exactly zero, and log(2+abs(xi))-log(13)/2 <= pMultiplier(xi) <= log(2+abs(xi))+1-log(2). The lower comparison is allowed to be negative.")),
                    Paragraph(Text("Writing X=abs(xi), the actual summand lies between f_X(n+3/2) and f_X(n+1), with f_X(u)=X^2/(u(4u^2+X^2)). The nonnegative decreasing comparison function has integral log(1+X^2/(4c^2))/2 on [c,infinity). The integral test bounds the full series below by log(1+X^2/9)/2 and above by X^2/(4+X^2)+log(1+X^2/4)/2. The exact square (2X/3-3)^2 gives the stated lower constant. No finite-head substitution occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-p-actual-spectral-identity"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentMixture.complete_positive_mixture_spectral_identity"),
                H("The actual Fourier identity for the literal complete P"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite index type, D>=0, inclusive nodes x_i in [0,D], and complex coefficients with sum a_i=0, pMultiplier is integrable against OriginalActualFourier.rho(prefix x a), and Re(quadratic x a P)=integral pMultiplier d rho(prefix x a). The measure is the literal Lebesgue density abs(Ahat)^2/(2 pi), with Ahat(A)(xi)=integral A(u)exp(-i xi u)du. Empty index types, D=0 and repeated nodes are included.")),
                    Paragraph(Text("The original complex angular-resolvent theorem supplies every positive rate by variable scaling, giving the numerator 2 lambda with normalization 1/(2 pi). The identity i xi Ahat=sum a_i exp(-i xi x_i) is squared without division by xi; the resulting finite expansion has conjugate(a_i)a_j exp(i xi(x_i-x_j)). Finite Fubini gives each exponential energy. Nonnegative Tonelli and the existing absolutely convergent quadratic mixture exchange the complete series and integral, including every tail term. No parity, extra moment, assumed analytic bound or Plancherel-mass premise is used.")),
                    Paragraph(Text("The two endpoints add the exact full-series logarithmic estimate and the normalized identity for the actual Fourier measure. The original moment certificate remains a separate retained statement. Typed Reg source laws preserve the full endpoint telescopes; audit acceptance is determined by the current scoped report. This identity does not assert RH, zero-free regions or the still-open prime-continuum coupling."))),
                DescribeRole.Theorem))));
}
