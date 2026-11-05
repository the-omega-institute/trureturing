using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualRobinIntervalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualRobinInterval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Robin margins transfer across actual optimizer intervals; all-price endpoint estimates remain explicit.",
        H("Original Robin interval transfer"),
        Blocks(
            Paragraph(Text("Write W(n)=log(sigma(n)/n) and Phi(A)=gamma+log(log(A)). The original margin is Phi(log(n))-W(n). The same objective, sigma and original integers are retained.")),
            Describe.Lean(
                DescribeId.Create("actual-optimizer-interval-transfer"),
                DeclarationHandle.Create(Prefix + "optimizer_interval_transfer"),
                H("Transfer between actual same-price optimizers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q and original optimizers B,U at q with 3<=B<=n<=U, the margin at n is at least the convex combination of the endpoint margins, and strictly greater in the genuine interior. The weight t is (log(n)-log(B))/(log(U)-log(B)), with the source's zero convention at coincident endpoints. Objective optimality proves the W chord bound. Strict log-log concavity is proved rather than supplied as a final hypothesis; endpoint signs are not assumed in this transfer theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-upper-price-integer-range"),
                DeclarationHandle.Create(Prefix + "original_robin_through_maximal"),
                H("Every integer through an actual maximal endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix any positive q0. Assume positive original Robin margins for every actual strict or maximal endpoint above 5040 at every price q>=q0. Then every natural integer 5040<n<=maximalInteger(q0) satisfies sigma(n)<exp(gamma)*n*log(log(n)). Natural-order coverage constructs the interval. If its price is below q0, actual prime-layer divisibility forces maximalInteger(q0)<=strictInteger(q)<=n<=maximalInteger(q0), so n equals the checked upper endpoint. Otherwise the two supplied margins and interval concavity apply. The remaining finite boundary is computed as 55440 inside the proof, using the same q11 identification as the full global reduction. The upper-price margins remain explicit hypotheses of this general theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-global-margin-endpoint-equivalence"),
                DeclarationHandle.Create(Prefix + "global_margin_iff_unpaid_estimates"),
                H("The exact unpaid all-price obligation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive original margins for every natural n>5040 are equivalent to EndpointRobinEstimates: for every positive real q with strictInteger(q)>5040, both strictInteger(q) and maximalInteger(q) have positive original margin. The constructed coverage supplies the reverse implication. Its finite branch identifies the chosen boundary price as the first layer at prime 11, with strict product 5040 and maximal product 55440, and invokes the existing finite Robin theorem there. No separate finite-boundary premise remains. This equivalence does not prove EndpointRobinEstimates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-global-original-robin-reduction"),
                DeclarationHandle.Create(Prefix + "global_original_robin_reduction"),
                H("Consume endpoint estimates in the original inequality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assuming EndpointRobinEstimates, every natural n>5040 satisfies sigma(n)<exp(gamma)*n*log(log(n)). The final logarithm/exponential transport pays its positivity conditions and retains the original sigma, integer factor and iterated logarithm. This conditional reduction proves neither the all-price endpoint estimates nor RH."))),
                DescribeRole.Theorem))));
}
