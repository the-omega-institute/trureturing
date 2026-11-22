import D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Register the higher inventory readout in the upper bound at the original record clock. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog

open Real Finset
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenLocalThreshold
open _root_.D5.S3.Arith.GoldenLayerMarginalDecay
open _root_.D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.PriceRecord.CompleteHigherInventoryDuality
open _root_.D5.S3.Arith.Robin.PriceRecord.CanonicalRecordPowerDefect (higherInventoryMismatch)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- No free data coordinates are needed by M(log m,m); m is the original late
state. Real weights and tolerances remain binders in the complete Law. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => higherInventoryMismatch (log (m : ℝ)) m)
    (fun e => nomatch e)

/-- Replace only the selected raw upper-bound observation, retaining the
original lower clause, all logical binders and the original local clock let. -/
abbrev arena : Arena where
  signature := signature
  Law W :=
    ∀ a : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 1 < X0 ∧
        ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
          (∀ k : ℕ, 0 < k → k < m →
            goldenResourceObjective mu k < goldenResourceObjective mu m) →
          X0 ≤ log (m : ℝ) →
          let X := log (m : ℝ)
          0 ≤ Real.rpow (log X) a * higherInventoryMismatch X m / sqrt X ∧
          Real.rpow (log X) a * W.readout () () m / sqrt X < ε

private theorem source_bridge :
    (type_of% (@actual_record_all_real_log_higher_inventory)) ↔ arena.Law actual :=
  Iff.rfl

private theorem actual_law : arena.Law actual :=
  source_bridge.mp actual_record_all_real_log_higher_inventory

/-- Cofinality is proved from the existing all-layer strict optimizer. It is
not an assumption about enrollment or an assumed instance of the conclusion. -/
private theorem original_records_cofinal (B : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ mu : ℝ, 0 < mu ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective mu k < goldenResourceObjective mu m) ∧
      B ≤ log (m : ℝ) := by
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes ⌈exp B⌉₊
  have hg : 0 < goldenLayerMarginal p 1 := by
    rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact div_pos (log_pos (by have := one_div_pos.mpr hp0; linarith)) hp.log_pos
  let mu := goldenLayerMarginal p 1 / 2
  have hmu : 0 < mu := half_pos hg
  let m := strictInteger mu
  have hspec := strictInteger_spec hmu
  have hm0 : 0 < m := by have := hspec.1; change 1 ≤ m at this; omega
  have hv : 1 ≤ m.factorization p :=
    (strict_layer_iff hmu hp le_rfl).mpr (by dsimp [mu]; linarith)
  have hpdvd : p ∣ m := (hp.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mpr hv
  have hpm : p ≤ m := Nat.le_of_dvd hm0 hpdvd
  have hrecord : ∀ k : ℕ, 0 < k → k < m →
      goldenResourceObjective mu k < goldenResourceObjective mu m := by
    intro k hk hkm
    have hle := hspec.2.2.1 k (by omega)
    by_contra! hnot
    have heq := le_antisymm hle hnot
    have hkopt : IsGoldenResourceOptimal mu k := by
      intro n hn
      rw [heq]
      exact hspec.2.2.1 n hn
    exact (Nat.le_of_dvd hk (hspec.2.2.2 k (by omega) hkopt)).not_gt hkm
  have hlarge : B ≤ log (m : ℝ) := by
    apply (le_log_iff_exp_le (by exact_mod_cast hm0 : (0 : ℝ) < m)).mpr
    exact (Nat.le_ceil (exp B)).trans
      ((by exact_mod_cast hpB : (⌈exp B⌉₊ : ℝ) ≤ p).trans
        (by exact_mod_cast hpm))
  exact ⟨m, hp.two_le.trans hpm, mu, hmu, hrecord, hlarge⟩

/-- This whole-family intervention makes the normalized upper readout equal
one at a=0 on every sufficiently late original record. -/
private def rejected : Realization signature :=
  realize signature (fun _ _ m => sqrt (log (m : ℝ))) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hbad
  obtain ⟨X0, hX0, htail⟩ := hbad 0 1 (by norm_num)
  obtain ⟨m, hm, mu, hmu, hrecord, hlarge⟩ := original_records_cofinal X0
  have h := (htail m hm mu hmu hrecord hlarge).2
  have hX : 0 < log (m : ℝ) := lt_of_lt_of_le (by linarith : (0 : ℝ) < X0) hlarge
  change Real.rpow (log (log (m : ℝ))) 0 * sqrt (log (m : ℝ)) /
    sqrt (log (m : ℝ)) < 1 at h
  simpa only [Real.rpow_eq_pow, Real.rpow_zero, one_mul,
    div_self (sqrt_pos.mpr hX).ne', lt_self_iff_false] using h

private theorem mismatch_weight_nonnegative (X : ℝ) (n : ℕ) (c : ℕ × ℕ)
    (hc : c ∈ (coordinates n \ coordinates (strictInteger (referencePrice X))) ∪
      (coordinates (strictInteger (referencePrice X)) \ coordinates n)) :
    0 ≤ coordinateWeight c := by
  rcases mem_union.mp hc with hc | hc <;>
    exact (mem_coordinates.mp (mem_sdiff.mp hc).1).1.log_pos.le

/-- The actual own-clock observation is not a constant family. The witnesses
are actual natural states 2 and 4, while the realization retains every state. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hlog2lo : (1 / 2 : ℝ) < log 2 := by
    have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at h ⊢
    linarith
  have hlog2hi : log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    linarith
  have hq2 : ¬ 0 < referencePrice (log 2) := by
    have hll : log (log (2 : ℝ)) < 0 := log_neg (by linarith) hlog2hi
    have hden : log (2 : ℝ) * log (log 2) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hll
    exact not_lt.mpr (by simpa only [referencePrice] using (one_div_neg.mpr hden).le)
  have htwo : higherInventoryMismatch (log 2) 2 = 0 := by
    norm_num [higherInventoryMismatch, strictInteger, hq2, coordinates,
      Nat.prime_two.factorization]
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, log_pow]
    norm_num
  have hX1 : 1 < log (4 : ℝ) := by rw [hlog4]; linarith
  have hX2 : log (4 : ℝ) < 2 := by rw [hlog4]; linarith
  have hL0 : 0 < log (log (4 : ℝ)) := log_pos hX1
  have hL1 : log (log (4 : ℝ)) < 1 :=
    (log_lt_log (by linarith : 0 < log (4 : ℝ)) hX2).trans hlog2hi
  have hden0 : 0 < log (4 : ℝ) * log (log 4) := mul_pos (by linarith) hL0
  have hden2 : log (4 : ℝ) * log (log 4) < 2 := by
    calc
      _ < log (4 : ℝ) * 1 := mul_lt_mul_of_pos_left hL1 (by linarith)
      _ < 2 := by simpa only [mul_one] using hX2
  have hq4 : (1 / 2 : ℝ) < referencePrice (log 4) := by
    dsimp only [referencePrice]
    exact (lt_div_iff₀ hden0).mpr (by nlinarith)
  have hmarg : goldenLayerMarginal 2 2 < (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 : ℝ)⁻¹ ^ 2 / log 2 :=
        golden_layer_marginal_le_inv_pow Nat.prime_two (by norm_num)
      _ < 1 / 2 := by
        norm_num
        exact (div_lt_iff₀ (by linarith : (0 : ℝ) < log 2)).mpr (by linarith)
  have hin : (2, 2) ∈ coordinates 4 := by
    apply mem_coordinates.mpr
    refine ⟨Nat.prime_two, le_rfl, ?_⟩
    change 2 ≤ (2 ^ 2).factorization 2
    rw [Nat.factorization_pow_self Nat.prime_two]
  have hout : (2, 2) ∉ coordinates (strictInteger (referencePrice (log 4))) := by
    intro hc
    have hh := ((canonical_mem (by linarith : 0 < referencePrice (log 4))).mp hc).2.2
    linarith
  have hmem : (2, 2) ∈
      (coordinates 4 \ coordinates (strictInteger (referencePrice (log 4)))) ∪
      (coordinates (strictInteger (referencePrice (log 4))) \ coordinates 4) :=
    mem_union_left _ (mem_sdiff.mpr ⟨hin, hout⟩)
  have hsingle : coordinateWeight (2, 2) ≤ higherInventoryMismatch (log 4) 4 := by
    unfold higherInventoryMismatch
    exact single_le_sum (fun c hc => mismatch_weight_nonnegative (log 4) 4 c hc) hmem
  have hfour : 0 < higherInventoryMismatch (log 4) 4 := by
    have hw : 0 < coordinateWeight (2, 2) := by
      change 0 < log (2 : ℝ)
      linarith
    exact hw.trans_le hsingle
  refine ⟨(), 2, 4, ?_⟩
  change higherInventoryMismatch (log 2) 2 ≠ higherInventoryMismatch (log 4) 4
  rw [htwo]
  exact ne_of_lt hfour

def family : Registration arena (type_of% (@actual_record_all_real_log_higher_inventory)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_record_all_real_log_higher_inventory) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog.actual_record_all_real_log_higher_inventory.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ m => higherInventoryMismatch (log (m : ℝ)) m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog
    definition := none
    coordinates := #[]
    readouts := #[{
      -- Source-inferred path, NOT extracted from a compiler artifact:
      -- Pi a/epsilon/h-epsilon; Exists predicate body X0; And right;
      -- Pi m/h-m/mu/h-mu/record/large; let X body; And right;
      -- LT left; division numerator; multiplication right.
      -- Scope ordinals: a=0, epsilon=1, h-epsilon=2, X0=3, m=4,
      -- h-m=5, mu=6, h-mu=7, record=8, large=9, local X=10.
      -- Let X is transported through log m; it is never a coordinate.
      path := #["body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherInventoryAllLog
