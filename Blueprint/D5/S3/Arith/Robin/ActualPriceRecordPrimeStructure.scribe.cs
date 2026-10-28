using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualPriceRecordPrimeStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-integer prime structure, higher-layer confinement and qualitative localization for positive-price records.",
        H("Prime Structure of Actual Price Records"),
        Blocks(
            Paragraph(Text(
                "Write X=log(m), L=log(X), lambda0=1/(40*X*L), and "
                + "Q(m)=sum over prime factors p of Nat(v_p(m)-1)*log(p). "
                + "The largest prime P is OriginalEndpointPrimeTail.largestPrime(m). "
                + "A predecessor record at price lambda compares the literal "
                + "goldenResourceObjective(lambda,n) with goldenResourceObjective(lambda,m) "
                + "for every natural n with 0<n<m. In particular, one and two remain rivals.")),
            Describe.Lean(
                DescribeId.Create("price-record-divides-canonical-strict-integer"),
                DeclarationHandle.Create(Prefix + "price_record_divides_strictInteger"),
                H("Occupied layers embed into the canonical strict integer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural m and every real lambda>0, a strict "
                        + "predecessor record at lambda implies m divides strictInteger(lambda). "
                        + "For an occupied prime p, the predecessor m/p is positive and smaller. "
                        + "The public single-layer objective difference makes its last marginal "
                        + "strictly larger than lambda. Exact strict-layer membership bounds "
                        + "the valuation by that of the same canonical integer. Zero valuations "
                        + "and nonprime coordinates contribute zero.")),
                    Paragraph(Text(
                        "At any t>=2 with q_t=1/(t*log(t))<=lambda, canonical price "
                        + "divisibility gives m divides strictInteger(q_t). Only this full "
                        + "integer has the literal strictInteger_counts law. The full-inventory "
                        + "higher-layer estimate and active-power cutoff apply there; "
                        + "valuation and higher-mass monotonicity transfer them to m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-price-record-uniform-prime-confinement"),
                DeclarationHandle.Create(Prefix + "price_record_prime_confinement"),
                H("An absolute square-root envelope for the same record integer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is one K>0 such that every m>=3 with the full predecessor "
                        + "record at lambda0 has nonincreasing valuations along all primes, "
                        + "including zero valuations; primeFactors(m)=primesLE(P); and "
                        + "X=theta(P)+Q(m). Moreover "
                        + "0<=Q(m)<=2*theta(sqrt(80*X))+2*(psi(40*X)-theta(40*X))<=K*sqrt(X). "
                        + "Consequently X-K*sqrt(X)<=theta(P)<=X. The same m divides "
                        + "strictInteger(1/(40*X*log(40*X))), and every occupied positive "
                        + "layer k satisfies p^k<40*k*X.")),
                    Paragraph(Text(
                        "The strongest antitone normal-form theorem supplies a companion "
                        + "a<=m with at least the same normalized divisor sum. If a<m, "
                        + "log monotonicity and the strictly positive price make its score "
                        + "strictly better, contradicting the record. Thus a=m. Nonempty "
                        + "prime support and its existing finite supremum then include every "
                        + "prime at most P. The original finite logarithmic factorization "
                        + "split identifies the first-prime mass with theta(P).")),
                    Paragraph(Text(
                        "Take t=40*X. Since log(3)>1, its price is positive and strictly "
                        + "less than lambda0. Apply the complete higher-layer theorem to "
                        + "the full canonical inventory at this price, then use m dividing "
                        + "it to compare Q. If psi(t)-theta(t)<=c*sqrt(t), put C=abs(c). "
                        + "The bounds theta(y)<=log(4)*y and sqrt(2*t)<=2*sqrt(t) "
                        + "give K=sqrt(40)*(4*log(4)+2*C)>0. This argument imposes "
                        + "no full-count or global optimality condition on m, and does not "
                        + "identify m with its containing inventory."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-price-record-largest-prime-localization"),
                DeclarationHandle.Create(Prefix + "price_record_largest_prime_localization"),
                H("One log-size cutoff for each prime-localization tolerance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real epsilon>0 there is A>0 such that all natural "
                        + "m>=3 with A<=log(m) and the same full record at lambda0 satisfy "
                        + "abs(P/log(m)-1)<epsilon. The cutoff precedes all such integers.")),
                    Paragraph(Text(
                        "For X>=4*K^2 the finite mass envelope gives theta(P)>=X/2. "
                        + "Chebyshev's global upper bound then gives P>=X/(2*log(4)), "
                        + "so P passes any fixed qualitative PNT cutoff once X is large. "
                        + "Combine theta(P)/P tending to one with Q(m)/X bounded by "
                        + "K/sqrt(X) tending to zero, and use X=theta(P)+Q(m). Only "
                        + "Q(m)/X has the stated square-root rate; no such rate is claimed "
                        + "for the total P/X error.")),
                    Paragraph(Text(
                        "These are log-size statements conditional on actual price records. "
                        + "Converting a uniform least-crossing height into the required record "
                        + "and log-size hypotheses is a separate arithmetic-analytic bridge. "
                        + "No crossing existence, unbounded crossing family, Robin sign or "
                        + "Riemann hypothesis follows from this dependency alone."))),
                DescribeRole.Theorem))));
}
