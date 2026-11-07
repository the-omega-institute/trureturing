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
            DescribeId.Create("unconditional-complete-mertens-ledger"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/CompleteMertensPeak.complete_mertens_ledger"),
            H("The unconditional full weighted ledger"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real t>=2, the actual complete Chebyshev error kernel and its existing WeightedTailTransport logarithmic weight are integrable on (t,infinity), and E2Lambda(t)=(psi(t)-t)/(t*log(t))-WeightedTailTransport.weightedTail(psiErrorKernel,t). WeightedPrimeLimit supplies absolute integrability and CompleteChebyshevTailIdentity supplies the complete normalized identity internally. There is no public hLay, normalization or integrability hypothesis, and no new integral owner. The existing calculus and both existing internal consumers are retained."))), DescribeRole.Theorem),

            Paragraph(Text("Conditional fixed-B0 application of the positive-U composite. Assume an actual nontrivial rho0 with beta=Re(rho0)>1/2 and gamma=Im(rho0)>0. Use delta, D, m0, m1 and A from the complete positive-U derivation in the WholeFormula, ActualZeroLaplace, ActualReciprocalSquareBounds, ZeroPowerSum and CountableGaussianQuadraticFourthMoment expositions. Separately assume hJY: for EVERY REAL u>=2, |Chebyshev.psi(u)-u|<=(939/100)*u*(log(u))^(303/200)*exp(-(4137/5000)*sqrt(log(u))), where the real exponent is Real.rpow. This is the exact additional quantitative Johnston-Yang premise used by complete_mertens_peak. No instance of it and no implication to it from the zero premises is asserted.")),
            Paragraph(Text("The height and strip bounds give D>20 and 0<delta<1/2, hence m0>160000. Since exp(x)>=1+x, exp(4*m0)>10000 and therefore A>=10000. Write L=log(A)>=0. The bound L^2/(1+L)<=L converts U(A)>sqrt(A)*(4*L+9) into the exact weaker peak premise U(A)>sqrt(A)*(4*L^2/(1+L)+9) of complete_mertens_peak. WeightedPrimeLimit.chebyshev_error_kernel_integrable supplies absolute integrability of the actual complete Chebyshev-error kernel on (1,infinity) unconditionally. Applying CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity at EVERY real endpoint t>=2 supplies hLay with Q the literal complete tail integral. Thus hLay and integrability are discharged by existing results; hJY remains explicit.")),
            Paragraph(Text("Applying complete_mertens_peak with hJY and this derived hLay produces a real t in [A,B(A)], B(A)=exp(4*(log(A)+20)^2), and the ACTUAL integer N=Nat.lcmUpto(floorNat(t)). It gives 5040<N, divisorRatio(N)>exp(gammaE)*log(log(N)), and (N:real)<=exp(B(A)*log(B(A))). Here divisorRatio(N)=(ArithmeticFunction.sigma 1 N:real)/N and gammaE=Real.eulerMascheroniConstant. Since A<=exp(28*m1), we have 0<=L<=28*m1. Consequently 1<=B(A)<=B0=exp(4*(28*m1+20)^2) and 0<=log(B(A))<=log(B0). Nonnegative product comparison gives B(A)*log(B(A))<=B0*log(B0), hence the ORIGINAL fixed bound (N:real)<=exp(B0*log(B0)).")),
            Paragraph(Text("The preceding paragraph describes the older hJY-dependent route. The new OriginalLocalA module separately closes the unchanged original implication without hJY via a proved signed endpoint. In particular the all-real JY bound is an additional analytic supplier, not a registration, a numerical sample, or a consequence of the full explicit formula. The separate existing literal-kernel theorem below has its own premise and qualitative finite-time conclusion; it does not supply this specified B0 bound. Neither RH nor existence of an off-critical zero nor an unconditional Robin counterexample is claimed.")),

            Describe.Lean(
                DescribeId.Create("completemertenspeak-finite-signed-endpoint"),
                DeclarationHandle.Create(Prefix + "finite_mertens_peak_of_signed_endpoint"),
                H("A finite signed endpoint forces a strict Mertens peak"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For A>=10000 and B>=A, the signed lower bound Q(B)-I(B)/r(B)>-1/(2*sqrt(A)), together with the complete Lay identity and the displayed positive U(A) peak, forces a real t in [A,B] whose actual prefix lcm is strictly greater than 5040 and strictly violates Robin. The finite no-peak contradiction retains the sign of the far endpoint. It uses no JY majorant and proves N<=exp(B*log(B)). OriginalLocalA supplies that signed endpoint at B=exp(y) and pays the original local and global bounds. This is a new alternative to the earlier absolute-tail route; its existing quantitative theorem still retains hJY."))),
                DescribeRole.Theorem),

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
                        + "peak. The separate OriginalLocalA theorem supplies the actual off-critical-zero "
                        + "implication via the new signed endpoint. Existence of such a zero and an "
                        + "unconditional Robin counterexample remain open."))),
                DescribeRole.Theorem))));
}
