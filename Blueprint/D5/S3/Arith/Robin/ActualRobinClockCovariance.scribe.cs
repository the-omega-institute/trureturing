using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualRobinClockCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite Robin log kernel has quantitative activation-shell variation and centered covariance bounds, consumed by the finite coefficient budget.",
        H("Quantitative Covariance of the Actual Finite Robin Log Kernel"),
        Blocks(
            Paragraph(Text(
                "For t>1 define g(t)=1/(t log t), and for A>1 and x>=1 define W(A,x) as the sum of log(k) times "
                + "max(g(k*x)-g(A),0) over integers 2<=k<=floor(A). The common "
                + "ambient floor equals this literal definition when 1<A<=b and "
                + "x>=1. For ordered clocks 1<A'<=A<=b and x>=1, the exact relative "
                + "activation W(A,x)-W(A',x) is the integral from A' to A of "
                + "(log(t)+1)/(t^2 log(t)^2) times the sum of log(k) over "
                + "2<=k<=floor(b), k*x<t. Replacing the strict activation test "
                + "at its finitely many endpoints does not change the integral. "
                + "Each original positive-part layer vanishes at its own clock threshold; "
                + "noninteger clocks, empty shells and 1<A<2 are included.")),
            Paragraph(Text(
                "For 1<a<=A'<=A<=b, x>=1 and "
                + "K=log(b/a)+log(log(b)/log(a)), integrating the actual prefix "
                + "bound Q(t/x)<=(t/x)*log(t) gives "
                + "0<=W(A,x)-W(A',x)<=K/x. This quantitative range estimate "
                + "is consumed in the covariance theorem below; no W envelope "
                + "or covariance sign is assumed.")),
            Paragraph(Text(
                "Writing U(x)=W(A,x)-W(A',x), for 1<a<=A'<=A<=b and 1<=x<=y, put "
                + "C=(1+1/log(a))*(log(b/a)+1/2). The right derivative "
                + "of the relative kernel has the finite shell A'<=k*x<A. "
                + "Each active term is at most (1+1/log(a))/(x^2*k), and "
                + "the shell reciprocal sum is at most 1/2+log(A/A'). "
                + "Right-derivative FTC therefore gives "
                + "0<=U(x)-U(y)<=C*(1/x-1/y). The inclusive lower shell "
                + "endpoint is the correct right derivative at a kink; "
                + "empty shells, noninteger clocks and 1<A<2 are included. "
                + "No convexity of U is asserted.")),
            Paragraph(Text(
                "The ordinary analytic calculation is the finite-band supplement "
                + "in Library/Analytic/mantovanelli2026primeworkload.md at commit "
                + "cd554e98a13551899994b718e7cdbd35d81624ab, specifically "
                + "U-int, U-size, U-var, G-size, G-var and J. The kernel estimates proved here "
                + "have no correlation-supplier premise. The supplement's "
                + "further arithmetic consumers remain conditional, and "
                + "no primary-source or literature-priority claim is made.")),
            Describe.Lean(
                DescribeId.Create("activation-density-integrable"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualRobinClockCovariance.density_integrable"),
                H("Integrability of the activation density"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real endpoints s,t with 1<s and s<=t, activationDensity is "
                    + "interval integrable with respect to volume from s to t. "
                    + "Continuity on the compact interval proves the assertion, including s=t. "
                    + "Translation gives integrability of u -> activationDensity(x+u) "
                    + "on [0,a] whenever x>1 and a>=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-terms-integrable"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualRobinClockCovariance.price_terms_integrable"),
                H("Integrability of both logarithmic price terms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real endpoints a,b with 1<a and a<=b, both t -> 1/t and "
                    + "t -> t^(-1)/log(t) are interval integrable with respect to volume "
                    + "from a to b. The second integrand equals g(t). "
                    + "Translation therefore supplies the shifted g integrals, and "
                    + "singleton intervals are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-robin-clock-quantitative"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualRobinClockCovariance.actual_clock_quantitative"),
                H("Actual quantitative covariance, signs and support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be any finite sample of m clocks, with "
                        + "1<a<=A_i<=b and a<=b. For 1<=x<=y and z>=0, the "
                        + "unnormalized centered covariance Gamma(x,x+z) lies "
                        + "between zero and m*K^2/(4*x*(x+z)). It does not "
                        + "increase under the simultaneous advance to (y,y+z). "
                        + "Its decrease is at most m*K*C/4 times "
                        + "[1/(x*(x+z))-1/(y*(y+z))]. At y=x+1 the second "
                        + "denominator is exactly (x+1)*(x+z+1). "
                        + "If b<=2*y, the later covariance is exactly zero. "
                        + "For m=0 every sample sum and covariance is zero; "
                        + "repeated and unordered clocks are allowed.")),
                    Paragraph(Text(
                        "The proof consumes the actual activation integral "
                        + "and K/x range estimate, translates by W(a,x), and "
                        + "uses finite range variance and Cauchy--Schwarz to "
                        + "obtain m/4. The two covariance-difference terms "
                        + "consume the same shell-derived C variation and "
                        + "K ranges. The previously compiled common-clock "
                        + "sign, simultaneous-decrease and support calculation "
                        + "is retained as a consumed private helper. No "
                        + "convexity assertion, Corr supplier, CA optimizer "
                        + "identity or full Robin/RH conclusion is used."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The same actual quantitative covariance is consumed by "
                + "D5/S3/Arith/Robin/ActualRobinClockCoefficientMass.actual_clock_coefficient_mass. "
                + "That companion theorem proves the finite maximum coefficient "
                + "budget with its exact Abel top and lower anchor.")),
            Paragraph(Text(
                "The conditional Corr consumer remains unfinished. "
                + "For its positive integer rough shifts, define S_R(z) as "
                + "the sum of mu(w)*mu(w+z) for 1<=w<=R. "
                + "The ordinary supplier is uniform for a fixed Z and every "
                + "selector c(z) in [0,1], fixed before the inner Moebius sum. "
                + "The required bound is abs(sum_z c(z)*S_R(z)/z) "
                + "<=C22*R*B^(-1-epsilon), under the supplier's conditions, "
                + "at R=L-1 and every R=r in [L,T]. This result does not "
                + "certify that supplier. "
                + "The exact finite Abel formula retains the negative lower "
                + "anchor and the top sum of Gamma_z(T+1)*S_T(z). "
                + "That top vanishes only with actual support evidence, "
                + "for example b<=2*(T+1); the negative finite top in A_LT "
                + "is retained in the deterministic coefficient budget. "
                + "This result treats arbitrary actual clocks and does "
                + "not identify them with a selected equality-inclusive CA sample.")),
            Paragraph(Text(
                "The full Robin/5040/RH goal remains active and unproved. "
                + "Its complete quadratic consumer retains m*mean(R)^2, V_a "
                + "with actual reserve and defect, the signed cross term "
                + "2*sum(mu(d)*beta(d)), the squarefree diagonal, d=1, all "
                + "rows below L and every complementary shift. No one of "
                + "these unpaid terms is removed by this covariance estimate. "
                + "Four-slot registration of actual_clock_quantitative remains unfinished under "
                + "the source-owner issue https://github.com/the-omega-institute/trureturing/issues/5214#issuecomment-6101507121; no declared_validated state "
                + "or literature priority is claimed.")))));
}
