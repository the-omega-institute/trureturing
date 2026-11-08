using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CompleteTailSecondOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original Euler tail at every positive-price full predecessor record.",
        H("Complete Price-Record Euler Tail at Second Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("price-record-complete-original-tail-second-order"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/PriceRecord/CompleteTailSecondOrder.price_record_complete_tail_second_order"),
            H("One threshold for every integer and every positive price"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This result concerns the complete original finite Euler tail at literal "
                    + "positive-price predecessor records. It does not establish the sign of "
                    + "the Robin endpoint or the Riemann hypothesis, and no literature novelty "
                    + "is claimed.")),
                Paragraph(Text(
                    "For every epsilon>0 there exists a real T>1 such that for every natural "
                    + "m>=2 and every real lambda>0, if for every natural n with 0<n<m one has "
                    + "goldenResourceObjective(lambda,n)<goldenResourceObjective(lambda,m), "
                    + "and P=OriginalEndpointPrimeTail.largestPrime(m)>=T, then "
                    + "abs(log(P)*(sqrt(P)*log(P)*OriginalEndpointPrimeTail.tail(m)-sqrt(2)) "
                    + "+sqrt(2)*(2+log(2)/2))<epsilon. The tail is the original finite sum "
                    + "of -log(1-p^(-(v_p(m)+1))) over every prime divisor of m. "
                    + "There is no restriction on the price, no omission of small positive "
                    + "predecessors and no replacement of m by an optimizing inventory.")),
                Paragraph(Text(
                    "Repository reuse: ActualPriceRecordPrimeStructure.price_record_prime_structure "
                    + "already proves antitone valuations, including zero valuations, and "
                    + "m.primeFactors=Nat.primesLE(P) on precisely this record domain. "
                    + "FixedLayerRigidity.valuation_below_layer_prime and "
                    + "valuation_above_layer_prime identify the valuation-one primes exactly "
                    + "as Q<p<=P, where Q=FixedLayerRigidity.layerPrime(m,2). The max-one "
                    + "convention permits Q=1; Q<=P follows directly from the finite supremum. "
                    + "Every prime in the support has positive valuation. Splitting the "
                    + "support at valuation two therefore gives the exact identity tail(m)="
                    + "sum_(Q<p<=P)(-log(1-p^-2))+H(m), where H(m) is the complete "
                    + "repeated-prime contribution, including P whenever its valuation is at least two.")),
                Paragraph(Text(
                    "Put S=sum_(Q<p<=P)p^-2. For each prime p, x=p^-2 lies in [0,1/2]. "
                    + "The ordinary log tangent bound gives -log(1-x)>=x; the existing "
                    + "LogarithmBounds theorem D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le "
                    + "gives -log(1-x)<=x+x^2. Thus each replacement error lies in [0,p^-4]. "
                    + "There are at most P primes in the finite interval and p>Q>=1, so "
                    + "0<=tail(m)-S<=P/Q^4+6/P^(2/3), using the existing "
                    + "HigherValuationTail.higher_valuation_tail for H(m). This estimate "
                    + "is for the same complete original tail, not just its first stratum.")),
                Paragraph(Text(
                    "Write L=log(P), H=log(Q), c=log(2), k=sqrt(2), and R=Q^2/(2P). "
                    + "LogarithmicLayerRigidity.price_record_logarithmic_layer_rigidity at j=2 "
                    + "gives L*(R-1)->-c along every filter of the full records on which "
                    + "P tends to infinity. Dividing by L gives R->1; hence Q tends to "
                    + "infinity. Set s=Q/sqrt(P) and B=L/H. The exact identities "
                    + "s^2=2R and (s-k)*(s+k)=2*(R-1) give s->k and "
                    + "L*(s-k)->-c/k. The exact log identity 2H=L+c+log(R) gives "
                    + "H/L->1/2, B->2 and L*(B-2)=-B*(c+log(R))->-2c. "
                    + "Consequently L*(B/s-k)=(L*(B-2)-k*L*(s-k))/s tends to "
                    + "-c/k=-k*c/2. Also B^2/s tends to 2k.")),
                Paragraph(Text(
                    "Let A2(t)=1/(t*log(t))-1/(t*log(t)^2), and K=sqrt(P)*L^2. "
                    + "PrimeSquareTail.prime_square_tail_logarithmic_refinements supplies one "
                    + "Y>exp(1), preceding both endpoints, with "
                    + "abs(S-A2(Q)+A2(P))<=2/(Q*H^3)+5/(Q*H^9) whenever P>=Q>=Y. "
                    + "Floors of the actual natural endpoints reduce exactly; the lower endpoint "
                    + "remains strict and the upper endpoint inclusive. At scale K the two "
                    + "error terms become 2*(B^2/s)/H and 5*(B^2/s)/H^7, both tending "
                    + "to zero. The finite upper endpoint is explicitly retained: "
                    + "K*A2(P)=(L-1)/sqrt(P)->0. Mere divergence of P/Q is not used "
                    + "to discard it.")),
                Paragraph(Text(
                    "The arithmetic comparison also vanishes at scale K. Eventually R>1/2, "
                    + "so Q^2>=P and K*P/Q^4<=L^2/sqrt(P)->0. Exactly "
                    + "6*K/P^(2/3)=6*L^2/P^(1/6)->0. These limits use the standard "
                    + "Mathlib logarithmic-power little-o theorem. The lower endpoint gives "
                    + "L*(sqrt(P)*L*A2(Q)-k)=L*(B/s-k)-B^2/s "
                    + "tending to -k*(2+c/2). Adding the arithmetic error, the signed "
                    + "finite Abel error and the retained upper endpoint yields the stated "
                    + "complete-tail constant. No asymptotic estimate is assumed as a new premise.")),
                Paragraph(Text(
                    "Uniformity uses S={(m,lambda):m>=2,lambda>0,and the literal full "
                    + "predecessor record holds}, with the filter comap(P,atTop). The generic "
                    + "filter proof applies to this entire subtype. An eventual epsilon-ball "
                    + "is pulled back from atTop to produce T, and only then are arbitrary "
                    + "m and lambda introduced. No sequence is selected after lambda and "
                    + "no existence of unbounded records is needed to manufacture a limit.")),
                Paragraph(Text(
                    "The scope search did not find this exact all-record tail law in the "
                    + "canonical Robin and exponent-exchange sources inspected. The existing "
                    + "ActualLeastCrossingPriceRecord.uniform_actual_least_crossing_5040_tail_budget "
                    + "is a coarser upper budget and is not rewrapped here. "
                    + "PrimeMinCorrectionSecondOrderLower.uniform_min_tail_robin_second_order_lower "
                    + "is a different lower theorem for tail plus the log-log clock correction "
                    + "at initial-support integers; it is not duplicated or inferred from this "
                    + "tail law. Robin endpoint signs and RH remain outside this result. "
                    + "The exact Euler-tail law above supplies neither the log-log clock "
                    + "correction nor a sign estimate for the Robin endpoint."))),
            DescribeRole.Theorem))));
}
