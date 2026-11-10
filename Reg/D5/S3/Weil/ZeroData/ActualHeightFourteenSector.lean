import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZeroData.ActualHeightFourteenSector
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenSector
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open LeanInformationAudit
open scoped BigOperators ComplexConjugate

abbrev Input := Σ N : ℕ, Σ c : Fin N → ℝ, ℝ × ℝ
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ s =>
    0 < H14Sector.weight s.2.1 s.2.2.1 s.2.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {c : Fin N → ℝ} {u p : ℝ},
    (∀ j, 0 ≤ c j) → 0 < u → p ∈ Set.Icc 0 (1 / 4) →
      ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2 →
      R.readout () () ⟨N, c, (u, p)⟩

private theorem source_reconstruction :
    (type_of% (@H14Sector.weight_pos)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsqrt : (10 : ℝ) < Real.sqrt 101 := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 10)).2
    norm_num
  have hsector : (2 : ℝ) / Real.sqrt 101 < Real.pi / 2 := by
    have hrat0 : (2 : ℝ) / Real.sqrt 101 < 2 / 10 :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 10) hsqrt
    have hrat : (2 : ℝ) / Real.sqrt 101 < 1 / 5 := by norm_num at hrat0 ⊢; exact hrat0
    linarith [Real.pi_gt_three]
  have hbad := h (N := 1) (c := ![0]) (u := 101) (p := 0)
    (by intro j; fin_cases j <;> norm_num)
    (by norm_num) (by norm_num) (by norm_num at hsector ⊢; exact hsector)
  simpa [rejected, realize] using hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ⟨1, ![0], (101, 0)⟩, ⟨1, ![0], (-2, 0)⟩, ?_⟩
  change (0 < H14Sector.weight ![0] 101 0) ≠ (0 < H14Sector.weight ![0] (-2) 0)
  have hsector : ((1 : ℝ) + 1) / Real.sqrt 101 < Real.pi / 2 := by
    norm_num at *
    have hsqrt : (10 : ℝ) < Real.sqrt 101 := by
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 10)).2
      norm_num
    have hrat0 : (2 : ℝ) / Real.sqrt 101 < 2 / 10 :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 10) hsqrt
    have hrat : (2 : ℝ) / Real.sqrt 101 < 1 / 5 := by norm_num at hrat0 ⊢; exact hrat0
    linarith [Real.pi_gt_three]
  have hp : 0 < H14Sector.weight ![0] 101 0 := by
    exact H14Sector.weight_pos (by intro j; fin_cases j <;> norm_num)
      (by norm_num) (by norm_num) (by norm_num at hsector ⊢; exact hsector)
  have hn : ¬ 0 < H14Sector.weight ![0] (-2) 0 := by
    norm_num [H14Sector.weight, H14Sector.reciprocalProduct, H14Sector.factor,
      H14Sector.stripImaginary, Fin.prod_univ_succ, Complex.inv_re, Complex.inv_im,
      Complex.normSq, Complex.mul_re, Complex.mul_im]
  intro he
  exact hn (he ▸ hp)

def family : Registration arena (type_of% (@H14Sector.weight_pos)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@H14Sector.weight_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@H14Sector.weight_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.H14Sector.weight_pos.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenSector.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s =>
    0 < H14Sector.weight s.2.1 s.2.2.1 s.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
namespace StrictAnti
abbrev Input := Σ N : ℕ, Σ c : Fin N → ℝ, ℝ
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ s =>
    StrictAntiOn (fun u : ℝ => H14Sector.weight s.2.1 u s.2.2)
      (Set.Ioi (H14Sector.threshold s.1)) ∧ 0 < s.1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {c : Fin N → ℝ} {p : ℝ}, 0 < N →
    (∀ j, 0 ≤ c j) → p ∈ Set.Icc 0 (1 / 4) →
      R.readout () () ⟨N, c, p⟩
private theorem source_reconstruction :
    (type_of% (@H14Sector.strictAntiOn_weight_u)) ↔ arena.Law actual := by
  constructor
  · intro h N c p hN hc hp
    exact ⟨h hN hc hp, hN⟩
  · intro h N c p hN hc hp
    exact (h hN hc hp).1
private theorem actual_law : arena.Law actual := by
  intro N c p hN hc hp
  exact ⟨H14Sector.strictAntiOn_weight_u hN hc hp, hN⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : ((1 : ℝ) + 1) / Real.sqrt 101 < Real.pi / 2 := by
    have hsqrt : (10 : ℝ) < Real.sqrt 101 := by
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 10)).2
      norm_num
    have hr0 : (2 : ℝ) / Real.sqrt 101 < 2 / 10 :=
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 10) hsqrt
    have hr : (2 : ℝ) / Real.sqrt 101 < 1 / 5 := by norm_num at hr0 ⊢; exact hr0
    linarith [Real.pi_gt_three]
  have hbad := h (N := 1) (c := ![0]) (p := 0)
    (by norm_num) (by intro j; fin_cases j <;> norm_num) (by norm_num)
  simpa [rejected, realize] using hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ⟨1, ![0], 0⟩, ⟨0, ![], 0⟩, ?_⟩
  have htrue : StrictAntiOn (fun u : ℝ => H14Sector.weight ![0] u 0)
      (Set.Ioi (H14Sector.threshold 1)) ∧ 0 < (1 : ℕ) := by
    refine ⟨H14Sector.strictAntiOn_weight_u (by norm_num)
      (by intro j; fin_cases j <;> norm_num) (by norm_num), by norm_num⟩
  change (StrictAntiOn (fun u : ℝ => H14Sector.weight ![0] u 0)
      (Set.Ioi (H14Sector.threshold 1)) ∧ 0 < (1 : ℕ)) ≠ _
  intro he
  have hbad := he ▸ htrue
  exact (Nat.not_lt_zero 0) hbad.2

def family : Registration arena (type_of% (@H14Sector.strictAntiOn_weight_u)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@H14Sector.strictAntiOn_weight_u) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.H14Sector.strictAntiOn_weight_u.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenSector.StrictAnti.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s =>
    StrictAntiOn (fun u : ℝ => H14Sector.weight s.2.1 u s.2.2)
      (Set.Ioi (H14Sector.threshold s.1)) ∧ 0 < s.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end StrictAnti

namespace StrictMono
abbrev Input := Σ N : ℕ, Σ c : Fin N → ℝ, ℝ
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ s =>
    StrictMonoOn (H14Sector.weight s.2.1 s.2.2)
      (Set.Icc 0 (1 / 4)) ∧ ∃ j₀, s.2.1 j₀ = 0) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {c : Fin N → ℝ} {u : ℝ},
    (∀ j, 0 ≤ c j) → (∃ j₀, c j₀ = 0) → 0 < u →
      ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2 →
      R.readout () () ⟨N, c, u⟩
private theorem source_reconstruction :
    (type_of% (@H14Sector.strictMonoOn_weight_p)) ↔ arena.Law actual := by
  constructor
  · intro h N c u hc hz hu hs
    exact ⟨h hc hz hu hs, hz⟩
  · intro h N c u hc hz hu hs
    exact (h hc hz hu hs).1
private theorem actual_law : arena.Law actual := by
  intro N c u hc hz hu hs
  exact ⟨H14Sector.strictMonoOn_weight_p hc hz hu hs, hz⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (N := 1) (c := ![0]) (u := 196)
    (by intro j; fin_cases j <;> norm_num) ⟨0, by norm_num⟩ (by norm_num)
    (by nlinarith [Real.pi_gt_three])
  simpa [rejected, realize] using hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ⟨1, ![0], 196⟩, ⟨1, ![1], 196⟩, ?_⟩
  have hs : (((1 : ℕ) : ℝ) + 1) / Real.sqrt 196 < Real.pi / 2 := by
    norm_num
    nlinarith [Real.pi_gt_three]
  have htrue : StrictMonoOn (H14Sector.weight ![0] 196) (Set.Icc 0 (1 / 4)) ∧
      ∃ j₀ : Fin 1, (![0] : Fin 1 → ℝ) j₀ = 0 := by
    refine ⟨H14Sector.strictMonoOn_weight_p (by intro j; fin_cases j <;> norm_num)
      ⟨0, by norm_num⟩ (by norm_num) hs, ⟨0, by norm_num⟩⟩
  change (StrictMonoOn (H14Sector.weight ![0] 196) (Set.Icc 0 (1 / 4)) ∧
      ∃ j₀ : Fin 1, (![0] : Fin 1 → ℝ) j₀ = 0) ≠
    (StrictMonoOn (H14Sector.weight ![1] 196) (Set.Icc 0 (1 / 4)) ∧
      ∃ j₀ : Fin 1, (![1] : Fin 1 → ℝ) j₀ = 0)
  intro he
  rw [he] at htrue
  obtain ⟨j₀, hj₀⟩ := htrue.2
  fin_cases j₀ <;> norm_num at hj₀

def family : Registration arena (type_of% (@H14Sector.strictMonoOn_weight_p)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@H14Sector.strictMonoOn_weight_p) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.H14Sector.strictMonoOn_weight_p.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenSector.StrictMono.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s =>
    StrictMonoOn (H14Sector.weight s.2.1 s.2.2) (Set.Icc 0 (1 / 4)) ∧
      ∃ j₀, s.2.1 j₀ = 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end StrictMono

structure SignedInput where
  N : ℕ
  c : Fin N → ℝ
  u : ℝ
  p : ℝ
  b : ℝ

namespace SignedReduction
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => SignedInput) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ s =>
    (∏ j : Fin s.N, (((s.u + s.p + s.c j : ℝ) : ℂ) +
      (s.b : ℂ) * Complex.I)⁻¹).re = H14Sector.weight s.c s.u s.p ∧
      s.b ^ 2 = s.u * (1 - 4 * s.p)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : SignedInput),
    s.b ^ 2 = s.u * (1 - 4 * s.p) → R.readout () () s
private theorem source_reconstruction :
    (type_of% (@H14Sector.real_product_signed_reduction)) ↔ arena.Law actual := by
  constructor
  · intro h s hb
    exact ⟨h s.c s.u s.p s.b hb, hb⟩
  · intro h N c u p b hb
    exact (h ⟨N, c, u, p, b⟩ hb).1
private theorem actual_law : arena.Law actual := by
  intro s hb
  exact ⟨H14Sector.real_product_signed_reduction s.c s.u s.p s.b hb, hb⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h ⟨1, ![0], 1, 0, 1⟩ (by norm_num)
  simpa [rejected, realize] using hbad
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ⟨1, ![0], 1, 0, 1⟩, ⟨1, ![0], 1, 0, 0⟩, ?_⟩
  have htrue :
      (∏ j : Fin 1, (((1 + 0 + ![0] j : ℝ) : ℂ) + (1 : ℂ) * Complex.I)⁻¹).re =
        H14Sector.weight ![0] 1 0 ∧ (1 : ℝ) ^ 2 = 1 * (1 - 4 * 0) := by
    exact ⟨H14Sector.real_product_signed_reduction ![0] 1 0 1 (by norm_num), by norm_num⟩
  change ((∏ j : Fin 1, (((1 + 0 + ![0] j : ℝ) : ℂ) + (1 : ℂ) * Complex.I)⁻¹).re =
      H14Sector.weight ![0] 1 0 ∧ (1 : ℝ) ^ 2 = 1 * (1 - 4 * 0)) ≠
    ((∏ j : Fin 1, (((1 + 0 + ![0] j : ℝ) : ℂ) + (0 : ℂ) * Complex.I)⁻¹).re =
      H14Sector.weight ![0] 1 0 ∧ (0 : ℝ) ^ 2 = 1 * (1 - 4 * 0))
  intro he
  have hbad := he ▸ htrue
  exact (by norm_num at hbad)

def family : Registration arena (type_of% (@H14Sector.real_product_signed_reduction)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@H14Sector.real_product_signed_reduction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.H14Sector.real_product_signed_reduction.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenSector.SignedReduction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s =>
    (∏ j : Fin s.N, (((s.u + s.p + s.c j : ℝ) : ℂ) +
      (s.b : ℂ) * Complex.I)⁻¹).re = H14Sector.weight s.c s.u s.p ∧
      s.b ^ 2 = s.u * (1 - 4 * s.p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end SignedReduction

end Reg.D5.S3.Weil.ZeroData.ActualHeightFourteenSector
