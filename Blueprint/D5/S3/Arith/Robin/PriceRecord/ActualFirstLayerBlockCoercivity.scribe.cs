using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualFirstLayerBlockCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite theta-mass lower bounds for the complete first-layer loss.",
        H("Missing and occupied prime blocks"),
        Blocks(
            Paragraph(Text(
                "The loss is the existing ActualRecordHigherLayerResidual.completeFirstLayerLoss, "
                + "summed over the union of the strict optimizer's prime support and the original "
                + "integer's prime support. No selected tail, squarefree replacement, record error "
                + "bound, prime number theorem, or RH assumption is used. Let X>4, m>=2, "
                + "m.primeFactors=primesLE(Q), and 1<a<b. Write M=theta(b)-theta(a).")),
            Describe.Lean(
                DescribeId.Create("actual-first-layer-missing-block-theta"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.missing_block_theta_lower_bound"),
                H("Missing positive block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If Q<=a and b+1/2<X, then (X-b-1/2)*M/(X*(b+1/2)*log(b)) "
                    + "is at most the complete first-layer loss. Every block prime a<p<=b is absent "
                    + "from m. Mathlib's 2u/(u+2)<log(1+u), at u=1/p, gives raw margin "
                    + ">=1/(p+1/2)-1/X>=1/(b+1/2)-1/X>0. The library's exact positive-layer "
                    + "count interval and strictInteger_counts place that prime in the actual "
                    + "optimizer support. Its missing loss is therefore its raw margin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-first-layer-occupied-block-theta"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity.occupied_block_theta_lower_bound"),
                H("Occupied negative block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If b<=Q and X<a, then (a-X)*M/(X*a*log(b)) is at most the same "
                    + "complete first-layer loss. Every a<p<=b divides m and has positive valuation. "
                    + "The tangent bound log(1+1/p)<=1/p and log(p)>=log(X) give negative raw "
                    + "margin at least 1/X-1/p>=1/X-1/a>0. Occupied loss dominates that quantity."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For both clauses the exact block is primesLE(floor(b)) minus primesLE(floor(a)), "
                + "including b and excluding a even when an endpoint is prime. Its log sum is "
                + "exactly M, and each log(p)<=log(b), hence M<=card(block)*log(b). Summing the "
                + "strictly positive uniform margin and extending by nonnegative loss terms proves "
                + "the result. The proof never divides by M or card(block), so empty blocks and "
                + "zero theta mass remain covered. These are finite estimates only: they assert "
                + "no global coercivity equivalence, first-layer asymptotic bound, or RH criterion. "
                + "No literature novelty is claimed."))
        )));
}
