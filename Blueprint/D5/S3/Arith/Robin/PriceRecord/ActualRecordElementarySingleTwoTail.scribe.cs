using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordElementarySingleTwoTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary eventual single extra binary layer of original records.",
        H("Original arbitrary-price records at their own clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("elementary-eventual-original-record-single-two-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordElementarySingleTwoTail.eventual_actual_record_single_two_tail"),
                H("One natural threshold for all original records"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There exists a natural M such that for every natural m>=M and every real mu>0, "
                    + "FullRecord(m,mu) implies valuation_2(m)<=optimalLayerCount(ownPrice(m),2)+1. "
                    + "Here FullRecord compares m strictly with every positive smaller integer at the "
                    + "same original mu, ownPrice(m)=1/(log(m)*log(log(m))), and optimalLayerCount is "
                    + "the existing strict profitable canonical count. No infinite record sequence, "
                    + "nonempty tail, special record price, globality or boundary supplier is assumed."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Put P=largestPrime(m), Q=layerPrime(m,2), x=log(P), H=log(Q), lambda=beta(1,P), "
                + "and r=Q^2/(2P). Original record limits give x*(r-1)+log(2)->0 and "
                + "x*(Q^2*H/(P*x)-1)->0. Elementary normalized gain bounds then give the essential "
                + "weighted estimate x*(beta(2,Q)/lambda-1)->0. Its exact algebraic numerator is "
                + "x*(A2-1)-x*(A1-1)-A1*x*(B-1), with denominator A1*B, where "
                + "A1=gain(1,P)*P, A2=gain(2,Q)*Q^2 and B=Q^2*H/(P*x).")),
            Paragraph(Text(
                "A shrinking upper prime window supplies two distinct primes U with "
                + "Q<p<=Q*(1+1/H^3). Eventually p<P. Prefix support and the original layer cutoff "
                + "give valuation one at both these primes and at P. Delete P and the highest binary "
                + "layer, and insert the two U layers. The P fee at lambda is exactly zero. The mass "
                + "eta=log(2)+x-logMass(U) is positive: it lies between -log(r)-2/H^3 and -log(r), "
                + "and the second-order limit controls the strict lower endpoint. The derivative "
                + "bound controls the entire upper window; its normalized total fee tends to zero.")),
            Paragraph(Text(
                "The existing actual finite predecessor gives the signed deficit comparison "
                + "lambda*log(2)-beta_v(2)*log(2)<(lambda-mu)*eta-auxiliaryGain. "
                + "Retaining the lambda*log(2) term yields beta_v(2)>=3lambda/4. The uniform own-clock "
                + "bound c<=5lambda/4 and strict binary layer halving exclude v>=a+2, where "
                + "a=optimalLayerCount(c,2). The proof takes the comap-atTop filter on all original "
                + "record pairs, so no NeBot hypothesis is needed. The original record logarithmic "
                + "envelope converts the uniform P threshold into a natural m threshold.")),
            Paragraph(Text(
                "This is an elementary consequence of the existing original record asymptotics "
                + "and actual finite prime exchanges. It removes the two BHP premises for this "
                + "binary layer bound. The complete prescribed bank, Robin beyond 5040 and RH "
                + "remain open.")))));
}
