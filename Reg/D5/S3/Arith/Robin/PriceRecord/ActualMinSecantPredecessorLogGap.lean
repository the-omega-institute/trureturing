import D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/- Exact full-source laws and equivalence bridges only. Four-slot registration
remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29429:
compiler occurrence/source binding, whole-family intervention and variation,
fixed-other-readout sensitivity and actual observational dependence are absent.
No Contract.Registration or declared_validated result is asserted. -/

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap

open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace secant_support

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t n => goldenResourceObjective t n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∀ {m q : ℕ} (hq : 0 < q) (hqm : q < m)
    {mu : ℝ}
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      W.readout () mu n < W.readout () mu m)
    (hmin : ∀ r : ℕ, 0 < r → r < m →
      (W.readout () 0 m - W.readout () 0 q) /
          Real.log ((m : ℝ) / q) ≤
        (W.readout () 0 m - W.readout () 0 r) /
          Real.log ((m : ℝ) / r)),
    let nu := (W.readout () 0 m - W.readout () 0 q) /
      Real.log ((m : ℝ) / q)
    mu < nu ∧ W.readout () nu q = W.readout () nu m ∧
      ∀ r : ℕ, 0 < r → r ≤ m →
        W.readout () nu r ≤ W.readout () nu m

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap.secant_support

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap.secant_support)) ↔
      arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end secant_support

namespace occupied_top_price

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ × ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role t x => if role = 0 then
    goldenResourceObjective t x.1 else goldenLayerMarginal x.1 x.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∀ {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    {nu : ℝ}
    (hmax : ∀ r : ℕ, 0 < r → r ≤ m →
      W.readout 0 nu (r, 0) ≤ W.readout 0 nu (m, 0))
    (ha : 1 ≤ m.factorization p),
    nu ≤ W.readout 1 nu (p, m.factorization p)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap.occupied_top_price

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap.occupied_top_price)) ↔
      arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end occupied_top_price

namespace actual_min_secant_predecessor_eventual_log_gap

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t n => goldenResourceObjective t n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law W := ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      (∀ n : ℕ, 0 < n → n < m →
        W.readout () mu n < W.readout () mu m) →
      ∀ q : ℕ, 0 < q → q < m →
      (∀ r : ℕ, 0 < r → r < m →
        (Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) -
          Real.log ((ArithmeticFunction.sigma 1 q : ℝ) / q)) /
            Real.log ((m : ℝ) / q) ≤
        (Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) -
          Real.log ((ArithmeticFunction.sigma 1 r : ℝ) / r)) /
            Real.log ((m : ℝ) / r)) →
      T ≤ (largestPrime m : ℝ) →
      0 < Real.log ((m : ℝ) / q) ∧
        Real.log ((m : ℝ) / q) ≤
          C * Real.log (largestPrime m : ℝ) *
            Real.log (Real.log (largestPrime m : ℝ))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap.actual_min_secant_predecessor_eventual_log_gap

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap.actual_min_secant_predecessor_eventual_log_gap)) ↔
      arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge

end actual_min_secant_predecessor_eventual_log_gap

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualMinSecantPredecessorLogGap
