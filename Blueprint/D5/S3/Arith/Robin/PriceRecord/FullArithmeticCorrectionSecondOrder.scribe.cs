using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

// Full arithmetic correction for the same integer at every positive-price strict predecessor record.
internal sealed class FullArithmeticCorrectionSecondOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-integer full arithmetic correction at every positive-price literal predecessor record.",
        H("Full arithmetic correction and the original integer clock"),
        Blocks(
            Paragraph(Text(
                "The full correction combines the original Euler tail with the change from the prime theta clock "
                + "to X=log(m), retaining the same integer and every positive-price strict predecessor record. "
                + "CompleteTailSecondOrder supplies its public price_record_complete_tail_second_order endpoint. "
                + "The additional clock term follows from the exact mass identity and finite remainder bound below.")),
            Describe.Lean(
                DescribeId.Create("price-record-existing-fixed-layer-filter-ratio"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.record_layer_ratio"),
                H("Original fixed-layer limit, exposed for a live consumer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unchanged original proof retains any index type and filter, m>=2, arbitrary positive prices and the full literal strict predecessor record at each index. With P->infinity it gives Qj^j/P->j for each fixed j>=2. The residual higher-envelope proof consumes j=3. This is visibility-only reuse, not new mathematics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-record-existing-mass-filter-rates"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.record_mass_limits"),
                H("Original same-integer relative clock rate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unchanged owner proof gives both same-integer E/sqrt(P) coefficients and X/P=1+o(1/log(P)), with X=log(m). The last conjunction uses the existing private reducible UnitRate; its calculus remains private. higher_layer_negligible consumes X/P->1. No bound X-P=O(sqrt(P)) follows."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-record-existing-finite-log-envelope"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.record_log_envelope"),
                H("Original finite envelope forces P escape"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unchanged finite proof gives X<=P*log(4P^2) for m>=2 at every positive original price with the full strict predecessor comparison. record_prime_escape consumes this exact bound to convert own-X escape into P escape uniformly over prices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-record-consumed-own-clock-q2-coefficient"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.record_second_own_clock_limit"),
                H("Only the needed Q2 coefficient in the existing owner context"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any filter of literal original record pairs with P->infinity, log(X)*(Q2/sqrt(X)-sqrt(2))->-log(2)/sqrt(2). Apply unit_sqrt(unit_inv(record_mass_limits.2.2)), multiply Q2/sqrt(P) with second_mul_unit, and transport the logarithmic ratio with relative_clocks. All four are the original private calculus. In the critical residual proof this limit places the second-layer coefficient in a fixed tube on the record's own clock, uniformly over the original prices."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The newly visible suppliers and consumed own-clock helper still require complete "
                + "source-bound four-slot audits; the exact remaining evidence is tracked in "
                + "https://github.com/the-omega-institute/trureturing/issues/28966.")),
            Describe.Lean(
                DescribeId.Create("price-record-same-integer-log-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.record_log_mass"),
                H("Exact factorization and the empty second layer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m>=2, lambda>0 and EVERY positive natural predecessor n<m, assume the strict inequality "
                    + "goldenResourceObjective(lambda,n)<goldenResourceObjective(lambda,m). Write P=largestPrime(m), "
                    + "X=log(m), Qj=layerPrime(m,j), and R=sum over occupied primes with valuation a>=3 of (a-2)*log(p). "
                    + "The public price_record_prime_structure supplies exact initial support and antitone valuations "
                    + "of this very m. The private layer_support proof identifies the primes with a>=j with primesLE(Qj) "
                    + "for every j>=1, including Qj=1. It uses valuation_below_layer_prime, the finite supremum defining "
                    + "layerPrime, and prime-factorization membership; a prime <=1 cannot occur. "
                    + "The existing public log_inventory_split proves the finite weighted factorization identity. "
                    + "Substituting initial support and the j=2 layer support gives EXACTLY "
                    + "X-theta(P)=theta(Q2)+R. Thus Q2=1 contributes theta(1)=0, with no deleted endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-record-third-mass-envelope"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.record_third_mass_bound"),
                H("A finite third-layer remainder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every summand of R is nonnegative. Each occupied prime with a>=3 lies below Q3 by the exact "
                    + "finite supremum. There are at most Q3 such primes, even without a prime-counting estimate. "
                    + "The public nonnegative-price prime_power_envelope applies because lambda>0: p^a<4P^2. "
                    + "Therefore (a-2)*log(p)<=a*log(p)=log(p^a)<log(4P^2), and "
                    + "0<=R<=Q3*log(4P^2). Fixed j=3 rigidity gives Q3^3/P->3, hence eventually "
                    + "Q3<=4^(1/3)*P^(1/3). Consequently "
                    + "0<=log(P)*R/sqrt(P)<=4^(1/3)*(log(4)*log(P)+2*log(P)^2)/P^(1/6)->0. "
                    + "This proves R=O(P^(1/3)*log(P)) and the stronger needed little-o mass estimate. "
                    + "It uses no maximum-exponent theorem or unproved uniformity in j."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Put Lp=log(P), H=log(Q2), c=log(2), k=sqrt(2). Logarithmic j=2 rigidity gives "
                + "Lp*(Q2^2/(2P)-1)->-c. First-order j=2 rigidity and the positive square root give "
                + "z=Q2/sqrt(P)->k. Rationalizing z-k through (z-k)*(z+k)=2*(Q2^2/(2P)-1) yields "
                + "Lp*(z-k)->-k*c/2. Also Q2->infinity and log(Q2)/Lp->1/2, using the exact identity "
                + "log(z)=log(Q2)-Lp/2. The public theta_error_eight gives "
                + "theta(t)/t=1+o(1/log(t)); it is obtained by multiplying the normalized eight-log error "
                + "by 1/log(t)^7. At Q2, multiply log(Q2)*(theta(Q2)/Q2-1) by "
                + "Lp/log(Q2) and Q2/sqrt(P). The result tends to zero. Together with the finite remainder, "
                + "E=X-theta(P)=Q2+o(sqrt(P)/Lp), E/sqrt(P)->k, and "
                + "Lp*(E/sqrt(P)-k)->-k*c/2. All are derived for the original arbitrary record.")),
            Paragraph(Text(
                "The nonlinear clock estimate is paid by a finite real inequality, not by an assumed Taylor bridge. "
                + "For a>1 and e>=0, the public loglog_tangent at a and at a+e gives "
                + "e/((a+e)*log(a+e))<=log(log(a+e))-log(log(a))<=e/(a*log(a)), including e=0. "
                + "Here a=theta(P), e=E, and a+e=X exactly. The PNT rate gives theta(P)/P=1+o(1/Lp); "
                + "E/P=(E/sqrt(P))/sqrt(P) gives X/P=1+o(1/Lp). Both clocks tend to infinity, so eventually "
                + "theta(P)>1 and X>1. For y equal to theta(P) or X, use the EXACT identity "
                + "log(y)-log(P)=log(y/P). It implies log(y)/Lp=1+o(1/Lp). Products and inverses then give "
                + "P*Lp/(y*log(y))=1+o(1/Lp). Multiplying the two finite tangent bounds by sqrt(P)*Lp "
                + "makes BOTH normalized endpoints equal (E/sqrt(P))*(1+o(1/Lp)). "
                + "Their second coefficients agree. Squeezing after multiplication by Lp proves "
                + "sqrt(P)*Lp*clock=k-k*c/(2Lp)+o(1/Lp), with every remainder derived. "
                + "Equivalently the nonlinear replacement error vanishes at sqrt(P)*Lp^2 scale.")),
            Describe.Lean(
                DescribeId.Create("price-record-complete-correction-both-second-orders"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.price_record_full_arithmetic_correction_second_order"),
                H("Both full second-order laws, uniformly in integer and price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C(m)=OriginalEndpointPrimeTail.tail(m)+log(log(X))-log(log(theta(P))), X=log(m). "
                        + "The fixed upstream tail endpoint gives sqrt(P)*Lp*tail=k-k*(2+c/2)/Lp+o(1/Lp). "
                        + "Adding the newly derived clock gives "
                        + "Lp*(sqrt(P)*Lp*C(m)-2*k)+k*(2+c)->0. "
                        + "The public theorem selects one T>1 BEFORE m AND lambda, then covers every m>=2, "
                        + "every lambda>0 and every literal strict full predecessor record with P>=T. "
                        + "Its conclusion includes theta(P)>1, X>1 and the epsilon bounds for BOTH displayed normalizations. "
                        + "No estimate or record premise is silently weakened, and no lower theorem is promoted to equality.")),
                    Paragraph(Text(
                        "For the X normalization, X/P=1+o(1/Lp) implies "
                        + "sqrt(X/P)=1+o(1/Lp), by rationalizing sqrt(X/P)-1. "
                        + "Also log(X)/Lp=1+o(1/Lp). Hence the exact multiplicative change from "
                        + "sqrt(P)*Lp*C to sqrt(X)*log(X)*C is "
                        + "sqrt(X/P)*log(X)/Lp=1+o(1/Lp). Multiplication preserves the second coefficient; "
                        + "the outer log(X)/Lp tends to one as well. Therefore "
                        + "log(X)*(sqrt(X)*log(X)*C(m)-2*k)+k*(2+c)->0. "
                        + "This uses only relative errors. No unconditional X-P=O(sqrt(P)) is asserted: "
                        + "the independent theta(P)-P term can dominate sqrt(P)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-record-complete-correction-in-original-clock"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.price_record_full_arithmetic_correction_second_order_X"),
                H("The threshold can also be chosen in X"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite prime-power envelope and log factorization give X<=P*log(4P^2): "
                    + "there are at most P occupied primes, and each a*log(p)<log(4P^2). "
                    + "Given the P threshold T, set B=max(T,2) and X0=B*log(4B^2)+2. If X>=X0 but P<T, "
                    + "monotonicity bounds X<=B*log(4B^2), a contradiction. This gives one X0>1 before m and lambda. "
                    + "The existing uniform_min_tail_robin_second_order_lower has the exact telescope "
                    + "m>0, initial prime support, theta(P)>1, X>=X0, X=log(m), L=log(X). It gives only "
                    + "sqrt(X)*L*C>=2*k-k*(2+c)/L+k*(8+4*c+3*c^2/4)/L^2-3200/L^3. "
                    + "It neither supplies nor is used to assume the two-sided law. The theorem establishes matching "
                    + "first and second coefficients, not attainment of that lower bound's third coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arbitrarily-large-literal-positive-price-records"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/FullArithmeticCorrectionSecondOrder.arbitrarily_large_price_records"),
                H("Actual records make the two coefficients attainable"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real T, take a prime p>T and lambda=goldenLayerMarginal(p,1)/2>0. "
                    + "The public optimal_layer_count_spec realizes all strict positive layers in a positive optimizer m "
                    + "that divides every other positive optimizer at that price. Its p layer is occupied, so P>=p>T. "
                    + "If any positive n<m had objective at least that of m, global maximality would force equality; "
                    + "then n would also be an optimizer and m would divide n, a contradiction. Thus m is a genuine "
                    + "literal strict predecessor record. This construction is confined to the nonvacuity proof; "
                    + "the universal theorem continues to quantify over all records, without replacing their m. "
                    + "Choosing such records beyond successive uniform thresholds realizes both first two coefficients."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The same private second_layer_limits and record_mass_limits also give the complete second-layer "
                + "application in the integer's own clock. Put Q=Q2, t=sqrt(2)*sqrt(X), and "
                + "H(m,t)=sum over ALL primes p<=t with v_p(m)<=1 of log(p). For every epsilon>0 there is "
                + "ONE X0>=2, chosen BEFORE every m>=2 and every lambda>0, such that the full strict predecessor "
                + "record premise and X=log(m)>=X0 imply all three conclusions: "
                + "|log(X)*(Q/sqrt(X)-sqrt(2))+log(2)/sqrt(2)|<epsilon; "
                + "every prime p>=t has v_p(m)<=1; and "
                + "|(log(X)/sqrt(X))*H(m,t)-log(2)/sqrt(2)|<epsilon. "
                + "The record premise compares goldenResourceObjective(lambda,n) strictly with "
                + "goldenResourceObjective(lambda,m) for EVERY natural n with 0<n<m. "
                + "There is no actualDefect, support cap, exponent cap, fixed-price, short-interval, "
                + "RH or P-X bound premise.")),
            Paragraph(Text(
                "To obtain this application, index by the subtype of all pairs (m,lambda) satisfying that entire "
                + "record premise, and use comap(X,atTop). The finite record_log_envelope forces P to infinity "
                + "as X tends to infinity: P<A would bound X by B*log(4B^2), B=max(A,2). "
                + "With w=log(P) and r=X/P, record_mass_limits gives r=1+o(1/w). "
                + "The existing unit_inv followed by unit_sqrt gives sqrt(P)/sqrt(X)=1+o(1/w). "
                + "Apply second_mul_unit to u=Q/sqrt(P), whose second coefficient is supplied by "
                + "second_layer_limits, and to this factor. The existing relative_clocks gives "
                + "log(X)/log(P)->1, so multiplication by that ratio yields exactly "
                + "log(X)*(Q/sqrt(X)-sqrt(2))->-log(2)/sqrt(2). Its strictly negative limit, together with "
                + "log(X)>0, gives the strict cutoff Q<t eventually. Thus even a prime equal to t is strictly "
                + "above Q; valuation_above_layer_prime at j=2 gives its ORIGINAL valuation <=1. "
                + "Intersect the two epsilon tails and this valuation tail before eventually_comap and "
                + "eventually_atTop extract X0. Neither extraction requires a NeBot premise.")),
            Paragraph(Text(
                "The finite hole identity is valid for every n>0 with antitone prime valuations and every real "
                + "t>=layerPrime(n,2): H(n,t)=theta(t)-theta(layerPrime(n,2)). "
                + "Indeed, valuation_below_layer_prime and valuation_above_layer_prime identify the filtered "
                + "primesLE(floor(t)) exactly with primesLE(floor(t)) minus primesLE(layerPrime(n,2)); "
                + "Finset.sum_sdiff and the finite theta sums then give the identity. "
                + "This includes n=1 and the empty second layer Q=1, where theta(1)=0. "
                + "The holes include ABSENT primes, with valuation zero, as well as primes of valuation one; "
                + "restricting the sum to occupied prime factors would change the conclusion.")),
            Paragraph(Text(
                "For the hole coefficient, apply QuantitativePrimeAbel.theta_error_log_power at N=1 "
                + "SEPARATELY at y=Q and at y=t. Both endpoints tend to infinity, y/sqrt(X)->sqrt(2), "
                + "and log(X)/log(y)->2. Multiplying each normalized theta error by these two ratios gives "
                + "(log(X)/sqrt(X))*(theta(y)-y)->0 at each endpoint, without assuming cancellation. "
                + "For Q the logarithmic ratio follows from second_layer_limits and relative_clocks; "
                + "for t it follows from log(t)=log(2)/2+log(X)/2. The exact decomposition is "
                + "(log(X)/sqrt(X))*H(m,t)=-log(X)*(Q/sqrt(X)-sqrt(2)) "
                + "+(log(X)/sqrt(X))*(theta(t)-t)-(log(X)/sqrt(X))*(theta(Q)-Q). "
                + "It gives the positive coefficient log(2)/sqrt(2) for the complete finite holes.")),
            Paragraph(Text(
                "The own-X record tail is nonempty arbitrarily far out. For any real R, "
                + "arbitrarily_large_price_records(exp(R)) supplies m>=2, an actual lambda>0, the full strict "
                + "predecessor record and exp(R)<P. Since every prime factor of m is <=m, the finite supremum "
                + "defining largestPrime gives P<=m; taking logarithms yields R<log(m)=X. "
                + "This constructs positive-price records and does not assert that least crossings exist.")),
            Paragraph(Text(
                "For literal least crossings, first choose the preceding X0, then choose "
                + "Tepsilon=max(Tpr,Tesc), where Tpr is supplied by "
                + "ActualLeastCrossingPriceRecord.uniform_actual_least_crossing_price_record and Tesc by "
                + "ActualLeastCrossing5040.uniform_actual_height_escape(X0). Both thresholds precede eta,T,m. "
                + "For every 0<eta<=1/2, T>=Tepsilon, and m>=3 with T<=actualHeight(eta,m) and "
                + "actualHeight(eta,n)<T for EVERY 3<=n<m, the escape theorem and "
                + "ActualIntegerHeightJump.divisor_log_le_log give X0<divisorLog(m)<=X. "
                + "The record theorem supplies lam0=1/(40*X*log(X))>0, the strict record against EVERY "
                + "positive predecessor at lam0, and 5040|m. Applying the own-X implication at this very "
                + "m and lam0 retains all three conclusions, including the complete holes and the weak "
                + "prime cutoff. This application includes eta=1/2. It remains conditional on the displayed "
                + "crossing premises: first_crossing_calibration has the separate requirements eta<1/2 "
                + "and unbounded actualHeight, which record nonvacuity does not supply.")),
            Paragraph(Text(
                "Applicability limits. The derivation uses classical prime-number estimates and finite factorization "
                + "identities, with no additional target estimate or Taylor premise. It establishes the first two "
                + "coefficients uniformly over all positive-price strict predecessor records; it does not establish "
                + "the third coefficient of the separate lower bound. Literature novelty is unassessed. "
                + "For Robin, margin(m)=C(m)-[M(P)-gamma-log(log(theta(P)))]. "
                + "The signed oscillatory Mertens/theta expression in brackets remains uncontrolled. "
                + "These correction asymptotics prove no Robin sign and no RH statement."))
        )));
}
