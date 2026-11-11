using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualFirstLayerPrefixCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite complete first-layer cancellation and actual-record budget comparison.",
        H("D5 source compiled; RegUNVALIDATED"),
        Blocks(
            Paragraph(Text(
                "These anchors describe a D5 source target with a current scoped Lean build. Its Reg mirror remains unvalidated for kernel checking, "
                + "source binding, variation and official acceptance "
                + "remains incomplete. The loss, raw margin, optimizer layer count and "
                + "unrestricted actual defect are reused from the canonical library. The companion "
                + "patch only exposes original consumed helpers. No second loss, margin, optimizer "
                + "or root definition is introduced. The mathematical mechanism is elementary; "
                + "no literature novelty is claimed.")),
            Describe.Lean(
                DescribeId.Create("actual-complete-first-layer-prefix-cancellation"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.complete_first_layer_prefix_cancellation"),
                H("Cancel the optimizer term on the complete common support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Statement: X>4, arbitrary natural m,k with m.primeFactors=primesLE(P), "
                    + "k.primeFactors=primesLE(Q), and the real casts of P,Q,r lie in [X/2,2X]. "
                    + "The root equation is the existing firstLayerPrice(r)=referencePrice(X), "
                    + "equivalently log(1+1/r)-log(r)/(X log(X))=0 on this interval. Then "
                    + "|C1(X,k)-C1(X,m)| <= "
                    + "6 max(|P-r|,|Q-r|) |theta(P)-theta(Q)| / (X^2 log(X/2)). "
                    + "Here C1 is exactly ActualRecordHigherLayerResidual.completeFirstLayerLoss.")),
                    Paragraph(Text(
                    "Each complete sum extends to lossPrimes(X,m) union lossPrimes(X,k). "
                    + "An original helper puts every positive first margin in optimizer support, "
                    + "so every added coordinate has exactly zero loss. Exact prime-factor prefixes "
                    + "turn first occupancy into p<=P or p<=Q. The identical max(rawMargin,0) terms "
                    + "cancel coordinate by coordinate. If P<=Q, the oriented difference is exactly "
                    + "minus the raw-margin sum over the existing block(P,Q)=(P,Q] primes. "
                    + "The reverse ordering swaps the two original integers.")),
                    Paragraph(Text(
                    "The candidate differentiates the literal real function g(t)=log(1+1/t) "
                    + "-log(t)/(X log(X)), obtaining g'(t)=-1/(t(t+1))-1/(X log(X)t). "
                    + "For every t in [X/2,2X], X>4 gives log(X)>1, the two positive derivative "
                    + "magnitudes are <=4/X^2 and <=2/X^2, and therefore |g'(t)|<=6/X^2. "
                    + "Mathlib's convex-set mean value inequality, applied to the actual root, "
                    + "bounds each discrepancy margin by (6/X^2) max(|P-r|,|Q-r|). "
                    + "The exact block log sum is theta(Q)-theta(P). Since every block prime "
                    + "has log(p)>=log(X/2)>0, its cardinality is at most this mass/log(X/2). "
                    + "No division by the mass or cardinality occurs. Equal prefixes, zero theta "
                    + "mass, inclusive upper endpoints and a prime root with zero margin are covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-record-prefix-budget-higher-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.actual_record_prefix_budget_residual"),
                H("Consume cancellation for the same original record"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Candidate statement: retain all preceding prefix/root/tube hypotheses. "
                    + "The ORIGINAL m is a strict record of goldenResourceObjective(mu,.) against "
                    + "every positive predecessor, for an arbitrary mu>0; X=log(m)>4. "
                    + "The integer k>=2 satisfies the concrete budget log(k)+delta=X with delta>=0. "
                    + "For every prime p and j>=2, j<=v_p(k) iff "
                    + "j<=optimalLayerCount(referencePrice(X),p). Then the actual residual "
                    + "R=actualDefect(X,m)-C1(X,m) satisfies 0<=R and "
                    + "R<=6 max(|P-r|,|Q-r|)|theta(P)-theta(Q)|/(X^2 log(X/2)) "
                    + "+delta/(X log(X)). The conclusion concerns m itself.")),
                    Paragraph(Text(
                    "The budget proves k<=m by strict monotonicity of log. If k<m the original "
                    + "record comparison applies; if k=m reflexivity applies. Expanding the actual "
                    + "objective and using mu*delta>=0 gives D(X,m)<=D(X,k)+delta/(X log(X)). "
                    + "The higher-occupancy equivalence is a premise about the existing canonical "
                    + "optimizer counts, not a defect or loss bound. The original margin_active_iff "
                    + "makes every j>=2 loss of k exactly zero, including ties. The exposed original "
                    + "actual_defect_decomposition therefore gives D(X,k)=C1(X,k). For m the same "
                    + "decomposition and nonnegative coordinate losses give R>=0. Subtract C1(X,m), "
                    + "bound the oriented first-layer difference by its absolute value, and consume "
                    + "the first theorem. This is a finite result only. Comparator construction, "
                    + "global theta estimates, RH implications and any A2-scale limit are absent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-ordered-prefix-difference"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.ordered_prefix_difference"),
                H("ordered_prefix_difference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem ordered_prefix_difference {X : ℝ} (hX : 1 < X)     {m k P Q : ℕ} (hmprefix : m.primeFactors = Nat.primesLE P)     (hkprefix : k.primeFactors = Nat.primesLE Q) (hPQ : P ≤ Q) :     completeFirstLayerLoss X k - completeFirstLayerLoss X m =       -(∑ p ∈ block (P : ℝ) Q, rawLayerMargin X p 1)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-raw-first-bound-at-root"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.raw_first_bound_at_root"),
                H("raw_first_bound_at_root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem raw_first_bound_at_root {X r t : ℝ} (hX : 4 < X)     (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     (ht : t ∈ Set.Icc (X / 2) (2 * X)) :     |log (1 + 1 / t) - log t / (X * log X)| ≤ (6 / X ^ 2) * |t - r|"))),
                DescribeRole.Theorem)

,
            Describe.Lean(
                DescribeId.Create("paid-prefix-consumed-defect-eq-first-of-optimizer-higher-layers"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation.defect_eq_first_of_optimizer_higher_layers"),
                H("defect_eq_first_of_optimizer_higher_layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete statement: theorem defect_eq_first_of_optimizer_higher_layers {X : ℝ} (hX : 1 < X) {k : ℕ} (hk : 1 ≤ k) (hhigher : ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j → (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p)) : actualDefect X k = completeFirstLayerLoss X k"))),
                DescribeRole.Theorem)
        )));
}
