import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling
import Reg.Support.DependentFamily

/-! Source registration for the determinant coefficient of a periodic sublevel. -/

namespace Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.PlanarWindowSampling
open _root_.D5.S3.Fourier.Asymptotics.PlanarFourierTail
open _root_.D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling
open Omega.Analysis.PeriodicSublevelSandwich (closedCell openCell latticeVector)
open Filter Finset WithLp
open scoped Topology RealInnerProductSpace Pointwise

noncomputable section

universe uι uα uβ

private def gridPhase (N : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (((m : ℂ) / (N : ℂ)) * (2 * Real.pi * Complex.I))

private theorem phase_sum_zero (N : ℕ) (hN : 0 < N) (m : ℤ)
    (hm : m ≠ 0) (hmN : m.natAbs < N) :
    ∑ j ∈ range N, gridPhase N m ^ j = 0 := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hphase : gridPhase N m ≠ 1 := by
    intro hz
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hz
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hcommon : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero
    have hk' : ((m : ℂ) / N) = (k : ℂ) := mul_right_cancel₀ hcommon hk
    have hm' : (m : ℂ) = (k : ℂ) * N := (div_eq_iff hNC).mp hk'
    have he : m = k * (N : ℤ) := by exact_mod_cast hm'
    have habs : m.natAbs = k.natAbs * N := by rw [he, Int.natAbs_mul, Int.natAbs_natCast]
    have hk₀ : k ≠ 0 := by
      intro hk₀
      exact hm (by simp [he, hk₀])
    have hka : 0 < k.natAbs := Int.natAbs_pos.mpr hk₀
    have hle : N ≤ k.natAbs * N := by
      simpa using Nat.mul_le_mul_right N hka
    rw [habs] at hmN
    exact (not_lt_of_ge hle) hmN
  have hpow : gridPhase N m ^ N = 1 := by
    rw [gridPhase, ← Complex.exp_nat_mul]
    convert Complex.exp_int_mul_two_pi_mul_I m using 2
    field_simp [hNC]
  rw [geom_sum_eq hphase, hpow, sub_self, zero_div]

private def gridPoint (N : ℕ) (j : ℕ × ℕ) : Plane :=
  toLp 2 ![(j.1 : ℝ) / N, (j.2 : ℝ) / N]

private theorem grid_character (N : ℕ) (m : ℤ × ℤ) (j : ℕ × ℕ) :
    character m (gridPoint N j) = gridPhase N m.1 ^ j.1 * gridPhase N m.2 ^ j.2 := by
  rw [character, Real.fourierChar_apply, gridPhase, gridPhase, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, ← Complex.exp_add, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [RCLike.star_def, conj_trivial, Pi.star_apply, dotProduct, gridPoint,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  congr 1
  ring

private theorem grid_sum_zero (N : ℕ) (hN : 0 < N) (m : ℤ × ℤ)
    (hm : m ≠ (0, 0)) (hcut : modeRadius m < N) :
    ∑ j ∈ (range N ×ˢ range N), character m (gridPoint N j) = 0 := by
  have h1 : m.1.natAbs < N := lt_of_le_of_lt (le_max_left _ _) hcut
  have h2 : m.2.natAbs < N := lt_of_le_of_lt (le_max_right _ _) hcut
  rw [Finset.sum_product (range N) (range N) (fun j => character m (gridPoint N j))]
  simp_rw [grid_character]
  calc
    _ = (∑ j ∈ range N, gridPhase N m.1 ^ j) * (∑ j ∈ range N, gridPhase N m.2 ^ j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = 0 := by
      by_cases hz : m.1 = 0
      · have hz₂ : m.2 ≠ 0 := fun he => hm (Prod.ext hz he)
        rw [phase_sum_zero N hN m.2 hz₂ h2, mul_zero]
      · rw [phase_sum_zero N hN m.1 hz h1, zero_mul]

private def cutoff (n : ℕ) := (n + 2) ^ 2
private def side (n : ℕ) := cutoff n + 1
private def radius (n : ℕ) : ℝ := ((n : ℝ) + 2)⁻¹
private def grid (n : ℕ) := (range (side n) ×ˢ range (side n))
private def gridWeight (n : ℕ) (_ : ℕ × ℕ) : ℝ := ((side n : ℝ) ^ 2)⁻¹

private theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by
  unfold cutoff
  positivity

private theorem grid_weight_sum (n : ℕ) : ∑ j ∈ grid n, gridWeight n j = 1 := by
  have hside : (side n : ℝ) ≠ 0 := by
    have h : side n ≠ 0 := by unfold side; omega
    exact_mod_cast h
  simp only [grid, gridWeight, sum_const, card_product, card_range, nsmul_eq_mul, ← pow_two,
    Nat.cast_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ hside)

private theorem grid_fourier (n : ℕ) (m : ℤ × ℤ) (hm : m ≠ (0, 0))
    (hcut : modeRadius m ≤ cutoff n) :
    ‖∑ j ∈ grid n, (gridWeight n j : ℂ) * character m (gridPoint (side n) j)‖ ≤
      (0 : ℝ) + 0 * (modeRadius m : ℝ) ^ 2 := by
  have hside : 0 < side n := by unfold side; omega
  have hm' : modeRadius m < side n := Nat.lt_succ_of_le hcut
  simp only [grid, gridWeight, ← Finset.mul_sum, grid_sum_zero (side n) hside m hm hm',
    mul_zero, norm_zero, add_zero, zero_mul, le_refl]

private theorem radius_tendsto : Tendsto radius atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

private theorem grid_tail_tendsto :
    Tendsto (fun n => 1 / (radius n ^ 6 * (cutoff n : ℝ) ^ 4)) atTop (𝓝 0) := by
  have h := radius_tendsto.pow 2
  convert h using 1
  · ext n
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    simp only [radius, cutoff, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    field_simp [hn]
  · simp

abbrev signature : Signature.{uι + 1, 0, 0, 0, 0} where
  Params := Σ I : Type uι, Fintype I
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => Real.pi * v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ {ι : Type uι} {α : Type uα} {β : Type uβ} [fintype : Fintype ι]
    (l : Filter α) (q : Plane) {F : Plane → Plane} (_hF : Continuous F)
    (_hperiod : ∀ (a : Fin 2 → ℤ) (x : Plane), F (latticeVector a + x) = F x)
    (z : ι → Plane) (_hz : Function.Injective z)
    (_hcell : ∀ i, z i ∈ openCell q)
    (_hzero : ∀ x ∈ closedCell q, F x = 0 ↔ ∃ i, x = z i)
    (A : ι → Plane ≃L[ℝ] Plane)
    (_hA : ∀ i, HasFDerivAt F (A i : Plane →L[ℝ] Plane) (z i))
    (s : α → Finset β) (p : α → β → Plane) (w : α → β → ℝ)
    (_hw : ∀ n, ∀ j ∈ s n, 0 ≤ w n j) (_hw₁ : ∀ n, ∑ j ∈ s n, w n j = 1)
    (ε : α → ℝ) (_hεpos : ∀ n, 0 < ε n) (_hε : Tendsto ε l (𝓝 0))
    (J : α → ℕ) (_hJ : ∀ n, 0 < J n) (c d : α → ℝ)
    (_hc : ∀ n, 0 ≤ c n) (_hd : ∀ n, 0 ≤ d n)
    (_hmode : ∀ n m, m ≠ (0, 0) → modeRadius m ≤ J n →
      ‖∑ j ∈ s n, (w n j : ℂ) * character m (p n j)‖ ≤
        c n + d n * (modeRadius m : ℝ) ^ 2)
    (_hc₀ : Tendsto (fun n => c n / (ε n) ^ 2) l (𝓝 0))
    (_hd₀ : Tendsto (fun n => d n / (ε n) ^ 4) l (𝓝 0))
    (_htail : Tendsto (fun n => 1 / ((ε n) ^ 6 * (J n : ℝ) ^ 4)) l (𝓝 0)),
    Tendsto (fun n =>
      (∑ j ∈ s n, w n j * (if ‖F (p n j)‖ < ε n then 1 else 0)) / (ε n) ^ 2)
      l (𝓝 (R.readout () ⟨ι, fintype⟩
        (∑ i, |LinearMap.det ((A i).toLinearEquiv : Plane →ₗ[ℝ] Plane)|⁻¹)))

theorem rejected_law : ¬ arena.{uι, uα, uβ}.Law rejected := by
  intro failure
  let constant : Plane := toLp 2 ![1, 0]
  have hconstant : constant ≠ 0 := by
    intro hz
    have hcoord := congrArg (fun x : Plane => x (0 : Fin 2)) hz
    exact one_ne_zero (show (1 : ℝ) = 0 from hcoord)
  let z : ULift.{uι} (Fin 0) → Plane := fun i => i.down.elim0
  let A : ULift.{uι} (Fin 0) → Plane ≃L[ℝ] Plane := fun i => i.down.elim0
  have hzero : ∀ x ∈ closedCell 0, (fun _ : Plane => constant) x = 0 ↔ ∃ i, x = z i := by
    intro x _
    constructor
    · intro h
      exact (hconstant h).elim
    · rintro ⟨i, _⟩
      exact i.down.elim0
  let up : ℕ → ULift.{uα} ℕ := ULift.up
  let liftPoint : ℕ × ℕ ↪ ULift.{uβ} (ℕ × ℕ) := Equiv.ulift.symm.toEmbedding
  let samples (n : ULift.{uα} ℕ) := (grid n.down).map liftPoint
  let points (n : ULift.{uα} ℕ) (j : ULift.{uβ} (ℕ × ℕ)) := gridPoint (side n.down) j.down
  let weights (n : ULift.{uα} ℕ) (j : ULift.{uβ} (ℕ × ℕ)) := gridWeight n.down j.down
  have hmass (n : ULift.{uα} ℕ) : ∑ j ∈ samples n, weights n j = 1 := by
    rw [Finset.sum_map]
    exact grid_weight_sum n.down
  have hmode (n : ULift.{uα} ℕ) (m : ℤ × ℤ) (hm : m ≠ (0, 0))
      (hcut : modeRadius m ≤ cutoff n.down) :
      ‖∑ j ∈ samples n, (weights n j : ℂ) * character m (points n j)‖ ≤
        (0 : ℝ) + 0 * (modeRadius m : ℝ) ^ 2 := by
    rw [Finset.sum_map]
    exact grid_fourier n.down m hm hcut
  have hbad := failure (Filter.map up atTop) 0
    (F := fun _ => constant) continuous_const (fun _ _ => rfl)
    z (fun {i} => i.down.elim0) (fun i => i.down.elim0) hzero A (fun i => i.down.elim0)
    samples points weights (fun _ _ _ => by unfold weights gridWeight; positivity) hmass
    (fun n => radius n.down) (fun n => by unfold radius; positivity)
    (tendsto_map'_iff.mpr radius_tendsto) (fun n => cutoff n.down) (fun n => cutoff_pos n.down)
    (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl) hmode
    (by simp only [zero_div]; exact tendsto_const_nhds)
    (by simp only [zero_div]; exact tendsto_const_nhds)
    (tendsto_map'_iff.mpr grid_tail_tendsto)
  have hbad' : Tendsto (fun n => (∑ j ∈ grid n, gridWeight n j *
      (if ‖constant‖ < radius n then 1 else 0)) / radius n ^ 2) atTop (𝓝 1) := by
    simpa only [Function.comp_def, samples, weights, up, ULift.down_up, Finset.sum_map,
      liftPoint, Equiv.toEmbedding_apply, Equiv.ulift_symm_apply, rejected, realize] using
      tendsto_map'_iff.mp hbad
  have hp : ∀ᶠ n in atTop, radius n < ‖constant‖ :=
    (tendsto_order.1 radius_tendsto).2 _ (norm_pos_iff.mpr hconstant)
  have hgood : Tendsto (fun n => (∑ j ∈ grid n, gridWeight n j *
      (if ‖constant‖ < radius n then 1 else 0)) / radius n ^ 2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hp] with n hn
    simp [not_lt_of_ge hn.le]
  have heq : (0 : ℝ) = 1 := tendsto_nhds_unique hgood hbad'
  exact zero_ne_one heq

theorem dependence : ObservationalDependence signature.{uι} actual := by
  intro _
  refine ⟨⟨ULift.{uι} (Fin 0), inferInstance⟩, 0, 1, ?_⟩
  change Real.pi * 0 ≠ Real.pi * 1
  simpa only [mul_zero, mul_one] using Real.pi_ne_zero.symm

def source_registration : Registration arena.{uι, uα, uβ}
    (type_of% @tendsto_weighted_sublevel_of_fourier.{uι, uα, uβ}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tendsto_weighted_sublevel_of_fourier, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro other h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tendsto_weighted_sublevel_of_fourier.{uι, uα, uβ})
      (Realization signature.{uι}) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => Real.pi * v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Fourier.Asymptotics.PeriodicSublevelSampling
