using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualRecordAllLogBudgetRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual prefix-budget candidate for every fixed real logarithmic weight.",
        H("D5 source compiled; Reg audit incomplete"),
        Blocks(
            Paragraph(Text(
                "This document anchors a D5 source target with a current scoped Lean build. The attempted Reg mirror was not retained after its source_bridge mismatch and sorryAx report; "
                + "the exact candidate is preserved in the runner packet under issue 28966. "
                + "Its finite prefix-cancellation dependency retains its original "
                + "source attribution. "
                + "The completed source has been reconciled with current canonical source under Lean 4.35 "
                + "and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. The critical file retains "
                + "namespace ActualRecordHigherLayerResidual; its exact prime-escape proof is exposed "
                + "by an unapplied patch and imported here. Only actual cross-module budget helpers "
                + "are made public. All mathematical statements and proof bodies are unchanged. "
                + "No new registration or validated status is asserted.")),
            Describe.Lean(
                DescribeId.Create("source-exposure-original-record-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.original_record_bounds"),
                H("Existing consumed helper: original_record_bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled; Reg audit incomplete. Exposure of an existing consumed full proof, with unchanged mathematical type and body. Complete candidate Lean statement: theorem original_record_bounds {α : Type*} {l : Filter α}     (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x) (hmu : ∀ x, 0 < mu x)     (hrecord : ∀ x k, 0 < k → k < m x →       goldenResourceObjective (mu x) k < goldenResourceObjective (mu x) (m x))     (hX : Tendsto (fun x => log (m x : ℝ)) l atTop) : ∀ᶠ x in l,     let X := log (m x : ℝ)     let P := largestPrime (m x)     (P : ℝ) ∈ Set.Icc (X / 2) (2 * X) ∧       0 ≤ X - Chebyshev.theta (P : ℝ) ∧       X - Chebyshev.theta (P : ℝ) ≤ 4 * sqrt X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-exposure-canonical-budget-eventually"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.canonical_budget_eventually"),
                H("Existing consumed helper: canonical_budget_eventually"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled; Reg audit incomplete. Exposure of an existing consumed full proof, with unchanged mathematical type and body. Complete candidate Lean statement: theorem canonical_budget_eventually : ∀ᶠ X : ℝ in atTop,     ∃ b : Budget, b.spec X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-exposure-log-shell"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.log_shell"),
                H("Existing consumed helper: log_shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled; Reg audit incomplete. Exposure of an existing consumed full proof, with unchanged mathematical type and body. Complete candidate Lean statement: theorem log_shell {X : ℝ} (hX : 4 < X) :     0 < log (X / 2) ∧ log X / 2 ≤ log (X / 2) ∧ log (2 * X) ≤ 2 * log X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-exposure-prefix-integer-log"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.prefix_integer_log"),
                H("Existing consumed helper: prefix_integer_log"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled; Reg audit incomplete. Exposure of an existing consumed full proof, with unchanged mathematical type and body. Complete candidate Lean statement: theorem prefix_integer_log (Q : ℕ) :     log (prefixInteger Q : ℝ) = Chebyshev.theta (Q : ℝ)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-exposure-higher-core-log"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.higher_core_log"),
                H("Existing consumed helper: higher_core_log"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled; Reg audit incomplete. Exposure of an existing consumed full proof, with unchanged mathematical type and body. Complete candidate Lean statement: theorem higher_core_log {n P : ℕ} (hn : 0 < n)     (hprefix : n.primeFactors = Nat.primesLE P) :     log (higherCore n : ℝ) = log (n : ℝ) - Chebyshev.theta (P : ℝ)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-exposure-prefix-integer-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.prefix_integer_pos"),
                H("Existing consumed helper: prefix_integer_pos"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled; Reg audit incomplete. Exposure of an existing consumed full proof, with unchanged mathematical type and body. Complete candidate Lean statement: theorem prefix_integer_pos (Q : ℕ) : 0 < prefixInteger Q"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-exposure-higher-core-pos"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.higher_core_pos"),
                H("Existing consumed helper: higher_core_pos"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled; Reg audit incomplete. Exposure of an existing consumed full proof, with unchanged mathematical type and body. Complete candidate Lean statement: theorem higher_core_pos (n : ℕ) : 0 < higherCore n"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-record-every-fixed-real-log-budget-remainder"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.actual_record_all_real_log_residual"),
                H("Uniform nonfirst loss at every fixed real logarithmic weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Candidate statement: for every fixed real a and epsilon>0 there exists "
                        + "X0>1 before every m>=2 and every original mu>0. If m is a literal strict "
                        + "goldenResourceObjective(mu,.) record against all positive predecessors "
                        + "and X=log(m)>=X0, then 0<=sqrt(X)*Real.rpow(log(X),a)*R<epsilon, "
                        + "where R=actualDefect(X,m)-completeFirstLayerLoss(X,m). All losses use "
                        + "the unrestricted actual pressure, complete union supports, and this "
                        + "same original X. The threshold may depend on a and epsilon.")),
                    Paragraph(Text(
                        "At lambda_X=1/(X log(X)), take the library's actual strictInteger N. "
                        + "The canonical strictInteger_spec supplies "
                        + "minimal divisibility. A tied smaller positive optimizer would be "
                        + "divisible by N, so N is a literal strict predecessor record. The "
                        + "unconditional half_shift_cutoff and strict first-layer membership give "
                        + "largestPrime(N)<X. As lambda_X tends to zero, each fixed prime eventually "
                        + "divides N, giving largestPrime(N) tending to infinity. Applying the "
                        + "existing record_mass_limits and record_layer_ratio at j=2 gives, "
                        + "eventually, h=log(L)<=2 sqrt(X) and every higher occupied prime "
                        + "p<=2 sqrt(X). Here L is the finite product of p^(v_p(N)-1). "
                        + "The external reference X is never replaced by log(N).")),
                    Paragraph(Text(
                        "For Y=X-h, take n0 to be the least natural index with theta(n0)>Y, "
                        + "and Q=n0-1. Coarse existing PNT supplies existence. Minimality gives "
                        + "theta(Q)<=Y<theta(Q+1); the finite prime-sum jump is at most log(Q+1). "
                        + "A coarse shell comparison at X/2+1 and 3X/2 yields Q in [X/2,2X], "
                        + "Q+1<=2X, and 0<=delta=Y-theta(Q)<log(2X)<=sqrt(X). This contains "
                        + "the full higher support of L. Construct the literal natural integer "
                        + "k=L*product_{p<=Q}p. primeBlock_factorization gives its exact prefix "
                        + "support and every j>=2 occupancy equal to N; the finite log identity "
                        + "gives log(k)+delta=X. Q need not be prime. No inference P=Q from "
                        + "equality of theta or of prime prefixes is used.")),
                    Paragraph(Text(
                        "For arbitrary original record families, the original record_prime_escape "
                        + "and record_log_envelope turn escape of X=log(m) into escape of P. "
                        + "The existing record_mass_limits gives P in [X/2,2X] and "
                        + "0<=H=X-theta(P)<=4 sqrt(X). The same-X finite prefix-budget theorem "
                        + "is then applied to the constructed k and the unconditional real root r. "
                        + "With E=abs(theta(P)-P)+abs(theta(Q)-Q), the candidate derives "
                        + "0<=R<=300/(X log(X))+60E/(X sqrt(X) log(X))+2/X. "
                        + "These deliberately generous constants suffice; the remainder estimate "
                        + "is a conclusion of the constructed comparison, never a hypothesis.")),
                    Paragraph(Text(
                        "For each natural n, directly compose public theta_error_log_power(n) "
                        + "with the two escaping endpoints. Shell comparability gives "
                        + "abs(theta(t)-t)*log(X)^n/X tending to zero for t=P,Q, with finite "
                        + "factor 2^(n+1). Multiplying the derived bound by sqrt(X)*log(X)^(n+1) "
                        + "leaves 300 log(X)^n/sqrt(X), the two endpoint errors times 60, and "
                        + "2 log(X)^(n+1)/sqrt(X), all tending to zero. Given real a choose n "
                        + "with n+1>=a. For log(X)>=1, Real.rpow monotonicity dominates the "
                        + "a-weight by the (n+1)-weight. The subtype of all original record pairs "
                        + "and comap of their own log clocks yield one threshold before m and mu. "
                        + "This proof consumes no old A1 residual theorem, no RH hypothesis, "
                        + "no first-layer-loss bound, and proves no unconditional A2=X/log(X)^3 "
                        + "statement, full-defect estimate, Robin sign or RH conclusion. "
                        + "The Pro calculation and same-family independent ordinary audit are "
                        + "mathematical guidance, not kernel evidence or model-diverse consensus."))),
                DescribeRole.Theorem)
,
            Describe.Lean(
                DescribeId.Create("paid-prefix-consumed-prefix-budget-integer"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.prefix_budget_integer"),
                H("prefix_budget_integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete statement: theorem prefix_budget_integer {n Q : ℕ} (hQ : 2 ≤ Q) (hsupport : ∀ p : ℕ, p.Prime → 2 ≤ n.factorization p → p ≤ Q) : let k := higherCore n * prefixInteger Q 2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧ log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) ∧ ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j → (j ≤ k.factorization p ↔ j ≤ n.factorization p)"))),
                DescribeRole.Theorem)
        )));
}
