using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualKernelLocalPositivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common short window gives strict positivity for every finite configuration of the complete arithmetic kernel.",
        H("Local strict positivity of the actual prime kernel"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-prime-kernel"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.K"),
                H("The complete arithmetic kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real t, K(t)=exp(-abs(t)/2) times the quantity (U(exp(abs(t)))-log(2*pi)+trivialT(abs(t))). Here U is CompleteMertensPeak.U, with its complete inclusive Mangoldt ramps, and trivialT is the full trivial-zero series with coefficients 1/(2*(n+1)*(2*(n+1)+1)). The value K(0) is the strictly positive first Li mass. The definition is even."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-prime-kernel-positive-density"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.D2"),
                H("The literal local density"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D2(t)=K(t)/4-exp(t/2)+exp(-t/2)/(exp(2t)-1). Its defining formula is total on the real line; the positivity and mixing statements use the positive local window. ActualKernelDyadicCoercivity consumes this same density."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-prime-kernel-weighted-density-limit"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.weighted_D2_limit"),
                H("The weighted density at zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("As t tends to zero from above, t*D2(t) tends to 1/2. The actual dyadic consumer uses this exact limit to choose a smaller eta on which D2(t)>=1/(4t); no numerical eta is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-prime-kernel-positive-representer"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.actual_positive_representer"),
                H("The original positive tent representation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist delta,r,L with 0<delta<log(2), r>0 and L>delta. D2 is positive on (0,delta], s*D2(s) is integrable there, and for every |t|<=delta the weighted tent is integrable and K(t)=integral_(0,delta] max(s-|t|,0)*D2(s)+r*max(L-|t|,0). The quantitative consumer retains this representation on delta and restricts only the positive mixing contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-prime-kernel-interval-vector"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.intervalVector"),
                H("Closed interval vectors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The interval vector is the complex indicator of [a,a+s]. The averaged-box consumer compares it with [a,a+s) almost everywhere, retaining the original triangle identity."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-prime-kernel-triangle-quadratic"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.triangle_quadratic"),
                H("The exact finite complex triangle identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real s, every finite Fin(n) real node family and every complex coefficient family, the squared norm of the interval-vector sum is integrable, and its complex integral equals the Hermitian quadratic form with entries max(s-|x_i-x_j|,0). The dyadic consumer directly reuses this identity, with a finite-endpoint almost-everywhere comparison to its half-open box sum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-prime-kernel-local-posdef"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.exists_window_posDef"),
                H("One window for all finite complex quadratic forms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There exists one real delta with 0<delta<log(2), such that for every natural n at least one and every injective real node map x:Fin(n)->Real satisfying abs(x(i)-x(j))<=delta for every pair, the complex matrix with entries K(x(i)-x(j)) is strictly positive definite. Equivalently, its Hermitian quadratic form is strictly positive for every nonzero family of complex coefficients. The window is chosen before n and x. The diameter inequality is closed, includes n=1, and imposes no lower bound on node separation.")),
                    Paragraph(Text("On the positive prime-free window the complete arithmetic formula has derivatives D1=K/2-exp(t/2)+exp(-t/2)*(log(2*pi)+log(1-exp(-2*t))/2) and D2=K/4-exp(t/2)+exp(-t/2)/(exp(2*t)-1). The exponential moment derivative and the ordinary logarithmic power series give these identities without truncating either arithmetic correction. Continuity at zero, D1 tending to negative infinity, t*D1 tending to zero and t*D2 tending to one half select a common interval with K>0, D1<0 and D2>0.")),
                    Paragraph(Text("Put r=-D1(delta) and L=delta+K(delta)/r. Both r>0 and L>delta hold. For every abs(t)<=delta, K(t) is the integral over 0<s<=delta of max(s-abs(t),0)*D2(s), plus r*max(L-abs(t),0). Only the weighted density s*D2(s) is asserted integrable. The zero endpoint follows from the primitive s*D1(s)-K(s) and its actual limit, rather than integrability of D2 itself.")),
                    Paragraph(Text("The arithmetic inputs are U_eq_complete_ramps, U_exp_continuous, trivialCoeff_hasSum, trivialT_continuousOn, firstLiMass_split and first_li_coefficient_pos. Differentiation reuses the original ExpRatioCM.Series weightedSeries, summable_weighted and hasDerivAt_weighted, the pinned Mathlib logarithmic power series, and log_one_sub_exp_derivatives. The endpoint integral reuses Mathlib intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto; positive mixtures reuse PositiveDefinite.Closure.integral. These general suppliers do not identify the actual positive representer on their own.")),
                    Paragraph(Text("A triangle is the overlap integral of translated interval indicators. Thus its complex quadratic form is an integral of a squared modulus. For a nonzero coefficient family the leftmost node carrying a nonzero coefficient has a positive interval on which only that coefficient contributes. The wide atom supplies strict positivity; the positive density supplies a positive semidefinite remainder.")),
                    Paragraph(Text("This is an unconditional local arithmetic statement. Global positivity, the Riemann hypothesis and the complete signed Robin residual are not conclusions of this theorem."))),
                DescribeRole.Theorem))));
}
