using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalSignedPrimeTranslationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/OriginalSignedPrimeTranslation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted Young integral estimate applies to arbitrary complex MemLp functions on the Lebesgue Ioc window. A variable arithmetic table and a connected closed-cell chain provide coefficient bounds for both original translations.",
        H("OriginalSignedPrimeTranslation"),
        Blocks(
                Paragraph(Text("The weighted Young integral estimate applies to arbitrary complex MemLp functions on the Lebesgue Ioc window. A variable arithmetic table and a connected closed-cell chain provide coefficient bounds for both original translations.")),
                Paragraph(Text("The weight h(x)=cosh(x/2) is positive. rho(a,s,x) is the indicator of the actual Ioc overlap multiplied by h(x+s)/h(x). The ratio is bounded by exp(abs(s)/2); this supplies integrability of rho*norm(f)^2 from MemLp. The existing PeriodicEnergyTransport.zero_extension_memLp and l2_complex_correlation_integrable supply the zero-extension and correlation facts.")),
                Paragraph(Text("The pointwise weighted Young inequality gives 2*norm(conj(f(x))*compression(a,s,f,x)) bounded by rho(a,s,x)*norm(f(x))^2 plus the opposite-shift weighted square evaluated at x+s. Integrating and using translation invariance removes x+s from the second integral. Applying the same estimate to -s and the complex triangle inequality handles both original translations. This is a continuous translation proof, not a finite matrix theorem.")),
                Paragraph(Text("The two cosh identities retain log(p)/sqrt(q): the plus coefficient is log(p)*(exp(x)+1/q)/(exp(x)+1), and the minus coefficient is log(p)*(exp(x)/q+1)/(exp(x)+1). They follow by expanding cosh, exp(log(q)/2)=sqrt(q), and field algebra with positive denominators. row_coefficient_bounds then applies the two independently checked log ceilings.")),
                Paragraph(Text("The closed envelope is reflected only as a function of x to reduce the row-sum comparison to r=exp(abs(x)) in [1,71]. No evenness or reality hypothesis is imposed on f. Complete support and nodup replace the original finite prime sum by the certificate rows. The inclusive q=5041 weight is retained; only its two endpoint compressions vanish at 2*a<=log(5041).")),
                Paragraph(Text("memLp_quadratic_prime80 is genuinely parametric in both row data and closed-cell data. Its conclusion is the original primeQuadratic bound for arbitrary complex f, any a<=log(71), and every M<=5041. The proof integrates the actual row estimate and keeps the Lebesgue Ioc norm identity. It proves the arbitrary L2 closure directly; a finite Fourier-head density argument is unnecessary.")),
                Describe.Lean(DescribeId.Create("prime-bilinear"),
                    DeclarationHandle.Create(Owner + "prime_bilinear"), H("prime bilinear"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The existing finite sum is distributed through the actual complex integral, with each integrability premise explicit."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("halfWindow"),
                    DeclarationHandle.Create(Owner + "halfWindow"), H("halfWindow"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The half-window log(71), so twice the half-window equals log(5041)."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-prime-integral"),
                    DeclarationHandle.Create(Owner + "original_prime_integral"), H("original prime integral"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The existing physical action/compression identity identifies the negative original symmetric integral with negative primeQuadratic."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("log-5041"),
                    DeclarationHandle.Create(Owner + "log_5041"), H("log 5041"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The identity 5041=71^2 aligns the inclusive endpoint with twice log(71)."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("memLp-quadratic-prime80"),
                    DeclarationHandle.Create(Owner + "memLp_quadratic_prime80"), H("memLp quadratic prime80"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The substantive variable-certificate inference bounds primeQuadratic on arbitrary complex MemLp functions, with both signed translations and the true Ioc/dx normalization."))), DescribeRole.Theorem))));
}
