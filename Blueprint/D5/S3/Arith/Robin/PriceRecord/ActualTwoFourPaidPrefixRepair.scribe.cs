using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;
internal sealed class ActualTwoFourPaidPrefixRepairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ActualTwoFourPaidPrefixRepair", H("D5 source compiled; RegUNVALIDATED"),
        Blocks(Paragraph(Text("The D5 source target and its exact mathematical candidate bodies compile under the scoped Lean check. RegUNVALIDATED remains for lawful registration, source binding, variation, official acceptance and axiom-bound audit; no RH conclusion is asserted. Ordinary Pro input is fallible. The exact original-record/arbitrary-original-price/energy endgoals belong to other owners.")),
            Describe.Lean(
                DescribeId.Create("actual-two-four-actual-two-four-paid-prefix-repair"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourPaidPrefixRepair.actual_two_four_paid_prefix_repair"),
                H("actual_two_four_paid_prefix_repair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem actual_two_four_paid_prefix_repair :     ∃ X0 : ℝ, 1 < X0 ∧ ∀ X : ℝ, X0 ≤ X →       ∀ b : Budget, b.spec X → ∃ k Qprime : ℕ,         2 ≤ k ∧ Qprime.Prime ∧ X / 2 < (Qprime : ℝ) ∧ (Qprime : ℝ) ≤ 2 * X ∧         k.primeFactors = Nat.primesLE Qprime ∧ log (k : ℝ) < X ∧         |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| +           (actualDefect X k - completeFirstLayerLoss X k) +           referencePrice X * (X - log (k : ℝ)) ≤ 10 / (X * log X ^ 3)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-canonical-paid-prefix-budget-eventually"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualTwoFourPaidPrefixRepair.canonical_paid_prefix_budget_eventually"),
                H("canonical_paid_prefix_budget_eventually"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem canonical_paid_prefix_budget_eventually :     ∃ b : ℝ → Budget, ∀ᶠ X : ℝ in atTop, (b X).spec X ∧       ∃ k Qprime : ℕ, 2 ≤ k ∧ Qprime.Prime ∧ X / 2 < (Qprime : ℝ) ∧         (Qprime : ℝ) ≤ 2 * X ∧ k.primeFactors = Nat.primesLE Qprime ∧         log (k : ℝ) < X ∧         |completeFirstLayerLoss X k - completeFirstLayerLoss X (b X).k| +           (actualDefect X k - completeFirstLayerLoss X k) +           referencePrice X * (X - log (k : ℝ)) ≤ 10 / (X * log X ^ 3)"))),
                DescribeRole.Theorem)
        )));
}
