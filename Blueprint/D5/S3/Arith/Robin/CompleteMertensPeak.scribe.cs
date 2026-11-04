using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class CompleteMertensPeakDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/CompleteMertensPeak.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete cumulative and literal arithmetic-kernel peaks locate strict finite Robin violations.",
        H("Complete Mertens peaks and finite Robin witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-mertens-peak"),
                DeclarationHandle.Create(Prefix + "complete_mertens_peak"),
                H("A complete cumulative peak gives an actual lcm witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Weil/johnstonyang2022pnt"),
                    LibraryNoteRef.Create("D5/L/Analytic/lay2015mertenssignchanges")),
                Blocks(
                    Paragraph(Text(
                        "Assume the complete Chebyshev error bound of Johnston–Yang and the exact "
                        + "complete-prime-power identity from Lay's Lemma 4. For A>=10000, set "
                        + "L=log(A), B=exp(4*(L+20)^2), and "
                        + "U(A)=A*sum(Lambda(n)/n,0<n<=floor(A))-psi(A)-A*log(A)+(1+gamma)*A. "
                        + "If U(A)>sqrt(A)*(4*L^2/(1+L)+9), there is a real t in [A,B] such that "
                        + "N=lcm(1,...,floor(t)) satisfies 5040<N<=exp(B*log(B)) and "
                        + "sigma(N)/N>exp(gamma)*log(log(N)).")),
                    Paragraph(Text(
                        "The two literature statements enter as hypotheses: Johnston–Yang, "
                        + "arXiv:2204.01980v2, Theorem 1.1, equation (1.3), and Lay, "
                        + "arXiv:1505.03589v1, the unnumbered identity in the proof of Lemma 4. "
                        + "The finite witness conclusion is derived here.")),
                    Paragraph(Text(
                        "The unconditional WeightedPrimeLimit.chebyshev_error_kernel_integrable "
                        + "supplies absolute integrability of the actual complete error kernel. "
                        + "Fubini on the triangle A<s<u gives "
                        + "integral Q(s)/(s*log(s)^2)=Q(A)/log(A)-integral f(u)/log(u), "
                        + "where f(u)=(psi(u)-u)/u^2. Substituting Lay's identity into the complete "
                        + "Mertens formula cancels the Euler constant and proves "
                        + "E₂Λ(t)=(psi(t)-t)/(t*log(t))-I(t), with the auxiliary notation "
                        + "I(t)=integral(f(u)*r(u),u>t) and r(t)=(1+log(t))/log(t)^2.")),
                    Paragraph(Text(
                        "The complete weighted Mertens identity relates E₂Λ to I. Completing each "
                        + "prime's positive logarithmic series gives E₂Λ<=-E₃. If E₃ never crosses "
                        + "the actual-lcm response threshold on [A,B], these two facts imply "
                        + "I(t)>=-4/sqrt(t). Absolute continuity of the integral primitives gives "
                        + "Q(A)=I(A)/r(A)+integral(w(t)*I(t),A,B)+Q(B)-I(B)/r(B), "
                        + "where w(t)=log(t)*(log(t)+2)/(t*(1+log(t))^2).")),
                    Paragraph(Text(
                        "Positivity and monotonicity of r bound the absolute far-end difference "
                        + "by twice the unweighted absolute Chebyshev tail. Logarithmic and "
                        + "square-root substitutions reduce that tail to the fifth exponential "
                        + "moment. Comparing with the derivative of -(5/2)*z^5*exp(-4*z/5) "
                        + "bounds the far-end difference by 100*z^5*exp(-4*z/5), which at B is "
                        + "less than 1/(2*sqrt(A)). Integrating 0<=w(t)<=1/t then gives "
                        + "Q(A)>-(4/r(A)+17/2)/sqrt(A), contradicting U(A)=-A*Q(A) and the peak. "
                        + "The existing common_robin_response supplies the actual integer witness "
                        + "and its size bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-kernel-peak-robin-violation"),
                DeclarationHandle.Create(Prefix + "actual_kernel_peak_robin_violation"),
                H("A literal complete arithmetic-kernel peak gives a finite Robin violation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real y>=log(10000), assume "
                        + "exp(-y/2)*(U(exp(y))-log(2*pi)+trivialT(y))>4*y+9. "
                        + "Then there exists a finite real t>=exp(y) such that the actual integer "
                        + "N=Nat.lcmUpto(floorNat(t)) satisfies N>5040 and "
                        + "divisorRatio(N)>exp(gamma)*log(log(N)). The cumulative U is the complete "
                        + "Mangoldt expression above, trivialT is the full correction from "
                        + "IntegratedExplicit.TrivialZeroLaplace, pi is Real.pi and gamma is "
                        + "Real.eulerMascheroniConstant. The statement has no Johnston–Yang, "
                        + "Lay-identity or tail-integrability premise and gives no explicit upper time bound.")),
                    Paragraph(Text(
                        "Set A=exp(y). The existing full-series bound trivialT_le_mass gives "
                        + "trivialT(y)<=1-log(2)<log(2*pi). Multiplication by exp(y/2), together "
                        + "with sqrt(exp(y))=exp(y/2) and 4*y^2/(1+y)<=4*y for y>=0, therefore "
                        + "turns the literal premise into U(A)>sqrt(A)*(4*log(A)^2/(1+log(A))+9). "
                        + "This uses the literal expression directly and requires no identification "
                        + "with an independently defined zero-sum kernel.")),
                    Paragraph(Text(
                        "WeightedPrimeLimit.chebyshev_error_kernel_integrable supplies absolute "
                        + "integrability on (1,infinity). CompleteChebyshevTailIdentity."
                        + "complete_chebyshev_tail_identity supplies the exact normalized Q identity "
                        + "for every real endpoint at least two. Mathlib's tendsto_integral_Ioi_zero "
                        + "then selects a finite B>=A with twice the absolute Chebyshev tail "
                        + "below 1/(2*sqrt(A)). The private finite_mertens_peak is the shared original "
                        + "finite-window contradiction: it consumes this B in finite_kernel_change, "
                        + "finite_lower_bound and tail_difference_bound, and finishes with the same "
                        + "common_robin_response at the actual prefix-lcm integer. The private "
                        + "qualitative_mertens_peak is consumed here; no standalone criterion alias "
                        + "or duplicate finite proof is introduced.")),
                    Paragraph(Text(
                        "The quantitative theorem above retains both its exact hypotheses and its "
                        + "explicit real and integer upper bounds. Its Johnston–Yang majorant and "
                        + "far_tail_small still pay the specified B=exp(4*(log(A)+20)^2). "
                        + "The new conclusion is conditional on the displayed literal arithmetic "
                        + "peak. Existence of that peak, any implication from failure of RH to such "
                        + "a peak, and an unconditional Robin counterexample remain open."))),
                DescribeRole.Theorem))));
}
