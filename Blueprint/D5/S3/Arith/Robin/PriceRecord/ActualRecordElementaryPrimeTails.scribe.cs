using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordElementaryPrimeTailsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary eventual single extra layer uniformly over all primes of original records.",
        H("One own-clock threshold for every prime"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("elementary-eventual-original-record-single-prime-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordElementaryPrimeTails.eventual_actual_record_single_prime_tail"),
                H("Uniform all-prime bound for arbitrary positive-price original records"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There exists a natural M such that for every natural m>=M, every real mu>0 "
                    + "and every FullRecord(m,mu), every natural prime p satisfies "
                    + "valuation_p(m)<=optimalLayerCount(ownPrice(m),p)+1. FullRecord means strict "
                    + "comparison of the original goldenResourceObjective at the same mu against "
                    + "every positive smaller integer. The own-clock price is "
                    + "1/(log(m)*log(log(m))); optimalLayerCount is the existing strict profitable "
                    + "canonical count, with equality layers excluded. M precedes m, mu and p; "
                    + "there is no prime-dependent threshold or restriction to a finite prime set. "
                    + "No infinite record sequence, nonempty-tail premise, BHP supplier, global "
                    + "optimizer hypothesis or special choice of the original record price is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The new content is the uniform odd-prime exchange and its common eventual "
                + "window, combined with the existing elementary binary endpoint. Put "
                + "P=largestPrime(m), Q=layerPrime(m,2), X=log(P), H=log(Q), lambda=beta(1,P) "
                + "and E=abs(X*(beta(2,Q)/lambda-1))+512*X/H^3. The original record limits and "
                + "the existing weighted_boundary_limit give E->0. The existing window_fee and "
                + "window_log_mass estimates control two primes U in the shrinking upper window "
                + "above Q and below P, all of actual valuation one. The single eventual event "
                + "is formed before choosing the varying prime p and gives "
                + "3*log(2)/4+2*E<logMass(U)-log(P)<log(3). These three helpers are reused at "
                + "their original definitions in ActualRecordElementarySingleTwoTail.")),
            Paragraph(Text(
                "For any odd prime p with valuation at least two, the original layer cutoff "
                + "places p at or below Q. Deleting p and P and inserting U is therefore a "
                + "disjoint actual exchange. Its logarithmic deficit "
                + "eta=log(p)+log(P)-logMass(U) is positive uniformly, because p>=3. The existing "
                + "signed_exchange_certificate is applied at the original arbitrary mu, with "
                + "lambda only an auxiliary comparison price. Its strict comparison, the two "
                + "window fees and mu*eta>0 yield "
                + "3*lambda*log(2)/4<goldenLayerMarginal(p,valuation_p(m))*log(p).")),
            Paragraph(Text(
                "Write a=optimalLayerCount(ownPrice(m),p). The existing adjacent_layer_strict "
                + "gives p-fold contraction of successive actual marginals. If the valuation "
                + "were at least a+2, the canonical next-layer threshold and the uniform "
                + "own-clock estimate c<=5*lambda/4 would give "
                + "goldenLayerMarginal(p,valuation_p(m))*log(p)<(5*lambda/12)*log(3), since log(p)/p is decreasing "
                + "for p>=3. The strict gap 5*log(3)<9*log(2), equivalently 3^5<2^9, contradicts "
                + "the exchange lower bound. Valuations at most one need no exchange.")),
            Paragraph(Text(
                "The proof takes a comap-atTop filter on all original record pairs. It obtains "
                + "a common largest-prime threshold for all odd primes, then reuses the existing "
                + "record_prime_escape from ActualRecordCriticalResidual to pass from m tending "
                + "to infinity to P tending to infinity. Combining this with the existing "
                + "eventual_actual_record_single_two_tail gives the single natural threshold M. "
                + "No NeBot assumption is used. Genuine records at arbitrarily large largest "
                + "prime are already supplied separately by "
                + "FullArithmeticCorrectionSecondOrder.arbitrarily_large_price_records.")),
            Paragraph(Text(
                "This is a repository-derived extension of the binary bound to all prime "
                + "indices at once. The higher-layer critical residual and the original-record "
                + "RH lower-bound criterion are existing canonical results, not new conclusions "
                + "of this module. The full prescribed bank, Robin beyond 5040 and RH remain "
                + "outside this conclusion.")))));
}
