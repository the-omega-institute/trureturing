using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordSingleTwoTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional single-two-tail reduction for original records.",
        H("Conditional original-record single-two-tail reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualrecordsingletwotail-bhp-actual-record-single-two-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordSingleTwoTail.bhp_actual_record_single_two_tail"),
                H("One uniform threshold for every original record and price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume BHPMaximumGap and BHPShortIntervalCount separately. There is one real T0>0 before every integer m>=2 and every real mu>0 with FullRecord(m,mu). FullRecord compares the original m strictly with every positive smaller integer at that same mu. Whenever T0<=P, where P=largestPrime(m), set c=1/(log(m)*log(log(m))), a=optimalLayerCount(c,2), and v=valuation_2(m). Then v<=a+1."))),
                DescribeRole.Theorem),
            Paragraph(Text("For every natural k with 1<=k<=v and goldenLayerMarginal(2,k)<c, the same conclusion gives v=a+1 and k=v. The entire original tail Icc(a+1,v) is exactly {v}; its full logarithmic volume is (v-a)*log(2)=log(2), with v-a taken in the natural numbers. Its complete loss is sum over j in Icc(a+1,v) of (c-goldenLayerMarginal(2,j))*log(2)=(c-goldenLayerMarginal(2,v))*log(2). These conclusions apply simultaneously to every occupied bad index, rather than to one chosen index or a selected subset of the tail.")),
            Paragraph(Text("The profitable prefix is strict: its positive indices satisfy c<goldenLayerMarginal(2,j). Equality layers are excluded from that prefix and included in the original tail with zero loss. The implication about a bad index uses the opposite strict inequality goldenLayerMarginal(2,k)<c. The theorem does not assert that a bad index exists.")),
            Paragraph(Text("The proof retains the literal comparison price lambda=beta(1,P). Along arbitrary families of original positive-price records, including varying mu, the exact factorization c/lambda=((log(m)/P)*(log(log(m))/log(P))*(gain(1,P)*P))^(-1) tends to one. The same record clock makes log(log(m)) tend to infinity and log(log(m))^2*P^(-19/640) tend to zero. Applying these limits on the space of all such records yields one threshold uniform in both m and mu.")),
            Paragraph(Text("The actual five-mode predecessor estimate then bounds the highest occupied 2-layer marginal below by 3*lambda/4, while c<=5*lambda/4. Consecutive positive 2-layer marginals satisfy 2*goldenLayerMarginal(2,j+1)<goldenLayerMarginal(2,j). The first excluded layer of a canonical optimizer at c has marginal at most c. If v>=a+2, these facts instead force the highest occupied marginal below c/2, contradicting the preceding bounds. The optimizer is an auxiliary integer whose optimality is proved; no global optimality of the original m is assumed.")),
            Paragraph(Text("This is a repository-derived conditional consequence of the original-record arithmetic and the two explicit analytic suppliers. It introduces no fixed-mu, own-price-localization, original-globality or single-tail hypothesis. The prescribed full bank and its b and delta, all required modes and both signs with every fee and full payment, Robin beyond 5040, and the Riemann hypothesis remain open.")))));
}
