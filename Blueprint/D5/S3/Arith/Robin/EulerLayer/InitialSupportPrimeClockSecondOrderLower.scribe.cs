using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.EulerLayer;

internal sealed class InitialSupportPrimeClockSecondOrderLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform scalar transfer from the logarithmic integer clock to the actual largest-prime clock.",
        H("Initial-Support Prime-Clock Second-Order Lower Law"),
        Blocks(Describe.Lean(
            DescribeId.Create("initial-support-prime-clock-second-order-lower"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/EulerLayer/InitialSupportPrimeClockSecondOrderLower.initial_support_prime_clock_second_order_lower"),
            H("One P-threshold before every initial-support integer"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every real epsilon>0 there is one real P0>1 such that every positive "
                    + "natural m with P=largestPrime(m), m.primeFactors=Nat.primesLE(P), "
                    + "theta(P)>1 and P>=P0 satisfies "
                    + "log(P)*(sqrt(P)*log(P)*(tail(m)+log(log(log(m)))-log(log(theta(P)))) "
                    + "-2*sqrt(2))+sqrt(2)*(2+log(2))>-epsilon. The threshold precedes all m, "
                    + "including arbitrary exponents on their initial prime support.")),
                Paragraph(Text(
                    "Write X=log(m), L=log(P), c=log(2), A=2*sqrt(2), "
                    + "B=sqrt(2)*(2+c), and D(t)=sqrt(t)*log(t). The public "
                    + "EulerLayerInventoryGrowth.log_factorization_split gives theta(P)<=X. "
                    + "The public LogarithmicLayerRigidity.theta_error_eight supplies one "
                    + "threshold with L>=2 and P/2<=theta(P)<=P*(1+1/(2*L^3)). The complete "
                    + "uniform_min_tail_robin_second_order_lower supplies the X-clock inequality.")),
                Paragraph(Text(
                    "Near X<=P*(1+L^(-3)), put Y=L-c>0. Then log(X)>=Y. Dropping only the "
                    + "positive third-order term in the supplied lower bound gives D(X)*C>=H(L), "
                    + "where C=tail(m)+log(log(X))-log(log(theta(P))) and "
                    + "H(L)=A-B/Y-3200/Y^3. This H tends to A>0; hence C>=0. "
                    + "Monotonicity of D on t>1, sqrt(a)<=a and log(a)<=a-1 for "
                    + "a=1+L^(-3) give D(X)<=D(P)*a*(1+L^(-4)). Consequently "
                    + "D(P)*C>=r(L)*H(L), with r(L)=1/((1+L^(-3))*(1+L^(-4))).")),
                Paragraph(Text(
                    "The near error is an explicit scalar rational function. Set z=1/L, "
                    + "R(z)=1/((1+z^3)*(1+z^4)), and Q(z)=1/(1-c*z). Then "
                    + "L*(r(L)*H(L)-A)+B equals "
                    + "-A*(z^2+z^3+z^6)*R(z)-B*(R(z)*Q(z)-1) "
                    + "-3200*R(z)*z^2*Q(z)^3. Its denominators are nonzero near zero, "
                    + "and its value at zero is zero. This chooses a single scalar threshold "
                    + "before introducing any m; no moving-m limit is used.")),
                Paragraph(Text(
                    "Far X>P*a, use b=1+1/(2*L^3), theta(P)<=P*b, and tail(m)>=0 from "
                    + "OriginalEndpointPrimeTail.tail_robin_data. The public "
                    + "RestrictedDivisorStrictInventory.loglog_tangent at x=P*a and y=P*b "
                    + "gives C>(a-b)/(a*log(P*a)). The numerator before cancellation is "
                    + "(a-b)*P, so no factor P remains in the denominator. Since L>=2, "
                    + "a<=2 and log(P*a)<=2*L; therefore C>1/(8*L^4) and "
                    + "D(P)*C>sqrt(P)/(8*L^3). The public Mathlib supplier "
                    + "isLittleO_log_rpow_rpow_atTop with exponents 3 and 1/2, together "
                    + "with Real.sqrt_eq_rpow, makes this last expression tend to infinity. "
                    + "It eventually exceeds the same A and hence pays the same A,B endpoint.")),
                Paragraph(Text(
                    "Finally choose P0=max(max(Ttheta,max(Tnear,Tfar)),max(2,2*X0)). "
                    + "Then X0<=P/2<=theta(P)<=X, so the X-clock supplier applies to every m. "
                    + "The two branches exhaust X. No restriction on exponents, record or "
                    + "price premise, optimizer substitution, or assumption X/P tending to one "
                    + "is used.")),
                Paragraph(Text(
                    "This is UNCOMPILED/UNACCEPTED source. All three former proof blocks have "
                    + "explicit tactic proof bodies; neither Lean elaboration nor Scribe generation "
                    + "has been run. Source inspection and hashes do not establish acceptance."))),
            DescribeRole.Theorem))));
}
