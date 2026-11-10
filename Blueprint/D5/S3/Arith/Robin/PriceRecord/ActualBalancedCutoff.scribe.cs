using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualBalancedCutoffDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/ActualBalancedCutoff.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same attained Robin minimum determines a unique real cutoff and exact prime support.",
        H("The real cutoff at the attained minimum's own price"),
        Blocks(
            Paragraph(Text("Set F(t)=log(1+1/t)/log(t) for real t>1. The definition firstLayerPrice extends the prime marginal via the existing golden_layer_marginal_one_eq_log_one_add_inv. The integer objective and Robin margin retain their original definitions.")),
            Describe.Lean(
                DescribeId.Create("actual-failure-unique-half-shift-cutoff"),
                DeclarationHandle.Create(Prefix + "failure_has_unique_half_shift_cutoff"),
                H("An original nonpositive failure constructs the same minimum's cutoff and support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The sole hypothesis is an actual natural n>5040 with robinLogMargin(n)<=0, including equality. Reuse failure_has_unique_internal_optimizer unchanged. Preserve its attained SAME N global margin minimum, N>55440, positive internal price lambda=1/(log N log log N), strict advantage over every distinct positive integer, strictInteger/maximalInteger equalities and all-prime/layer no-tie conclusion. No attainment, cutoff, root, support or optimizer premise is added.")),
                    Paragraph(Text("FewDistinctPrimes.robin_lt_223092870 and the original margin/ratio bridge force this failing N>=223092870. Since exp(1)<3 and 3^12<223092870, L=log N>12. For a=L-1/2 the pinned Real.lt_log_one_add_of_pos at x=1/a gives log(1+1/a)>1/L. Together with log a<log L this gives F(a)>lambda. The standard strict log upper bound gives F(L)<lambda. Continuity and the intermediate value theorem construct a<z<L, hence z>11 and 0<L-z<1/2.")),
                    Paragraph(Text("For 1<x<y the positive numerator log(1+1/t) strictly decreases while the positive denominator log t strictly increases. Thus F is strictly antitone on the full real domain t>1, proving uniqueness among all t>1, including outside its construction interval.")),
                    Paragraph(Text("The existing weak_layer_iff at layer 1 and N=maximalInteger(lambda) identify p in N.primeFactors with lambda<=F(p). Real antitonicity and F(z)=lambda make this equivalent to p<=z, hence exactly p<=floorNat(z). Therefore N.primeFactors=Nat.primesLE floorNat(z), with inclusive finite endpoints retained. The inherited no-tie conclusion also excludes a prime equaling z; no strict endpoint is silently substituted.")),
                    Paragraph(Text("This cutoff/support construction is repo-derived from the existing optimizer and pinned Mathlib logarithm/continuity results. The classical minimum-to-CA mechanism overlaps Caveney--Nicolas--Sondow, On SA, CA, and GA numbers, arXiv:1112.6010v2, section 2, as recorded by the optimizer supplier; no novelty claim is made for that mechanism. The full finite Mangoldt-to-Euler equality, SAME N signed margin ledger and strict necessary CompleteMertensPeak.I negativity remain subsequent obligations. This theorem asserts neither a signed integral estimate nor RH."))),
                DescribeRole.Theorem))));
}
