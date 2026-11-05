using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

// Candidate mirror. Native compiler and Scribe checks are pending for this module; no acceptance or literature novelty claim.
internal sealed class FullArithmeticCorrectionSecondOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-integer full arithmetic correction at every positive-price literal predecessor record; candidate source.",
        H("Full arithmetic correction and the original integer clock"),
        Blocks(
            Paragraph(Text(
                "CANDIDATE SOURCE, 2026-11-05. The Lean declaration and this Scribe mirror are under native compilation. "
                + "The upstream CompleteTailSecondOrder import is the delivered canonical compiled supplier, with SHA256 "
                + "4eeec2b602524c7f835c58bf8eca19530a001295aef305121602616187563dc0. "
                + "Only its public price_record_complete_tail_second_order endpoint is consumed; its frozen proof body is not reproduced here. "
                + "The supplier hash and theorem endpoint were checked in the linked canonical core. The exact read-file hashes are below. "
                + "Declaration handles describe intended canonical addresses, not successful integration or acceptance.")),
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
                        + "The public draft theorem selects one T>1 BEFORE m AND lambda, then covers every m>=2, "
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
                    + "It neither supplies nor is used to assume the new two-sided law. The draft establishes matching "
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
                    + "Choosing such records beyond successive uniform thresholds realizes both first two coefficients. "
                    + "The existence claim and its supplied Lean proof are also uncompiled."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Supplier/API limits. Full public telescopes were read, including the universal lower and its X clock. "
                + "Public canonical mathematical source hashes (SHA256): "
                + "ActualPriceRecordPrimeStructure ea2cf59fa72829204b34ff6db5c3bd85ec723271fa7709a7c83eb9a6b3ebba84; "
                + "FixedLayerRigidity 46f1366c378febe30bb61b3adf1083577821b7b4254803679136af0f27823d2a; "
                + "LogarithmicLayerRigidity 2c02eb17d94e3c38dd0969198dea30c36963cbe8fab780b405618d6e91607c32; "
                + "PrimePowerEnvelope 2e973897195d08c1e091a75d5cf28cab8b6309579df0c0bf5e471eb3d44a6722; "
                + "EulerLayerInventoryGrowth cacb751e51a8de86f4debf9a0c74d2f817087c0472c41e8e016499660d7d4521; "
                + "LogarithmBounds b7c99a12b0b7821f864568db16c14c9a402931ee9adce4bb51b2683c4e892875; "
                + "EulerLayer/PrimeMinCorrectionSecondOrderLower 53ef701c27706cb92a456a6982571aac768388f867eb575cb188c366ee0a1223. "
                + "Additional exact-source hashes, including EulerLayerRootCorrection and the nonvacuity supplier, "
                + "are retained in the runner result envelope. Source hashes identify read bytes; they are not compiler receipts.")),
            Paragraph(Text(
                "The mathematical derivation has no additional target estimate or unproved Taylor premise. "
                + "Formal completion remains OPEN: this module, the upstream complete-tail draft, their intended import "
                + "composition, Lean coercions/rpow/filter congruence APIs, tactics, Scribe handles and all axiom closures "
                + "have not been checked by a compiler. No accepted integration, registration, CI, PR or push is claimed. "
                + "No external literature search was authorized, so paper novelty is unassessed. "
                + "For Robin, margin(m)=C(m)-[M(P)-gamma-log(log(theta(P)))]. "
                + "The signed oscillatory Mertens/theta expression in brackets remains uncontrolled. "
                + "These correction asymptotics prove no Robin sign and no RH statement."))
        )));
}
