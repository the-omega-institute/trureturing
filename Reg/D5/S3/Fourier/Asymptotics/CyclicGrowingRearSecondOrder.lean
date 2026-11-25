import Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearFirstOrder
import D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder

/-! Source dependence in the second-order rear value and support law. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder

open Filter Matrix Finset
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open _root_.D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open _root_.D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open _root_.Reg.Support

noncomputable section

namespace SecondOrder

abbrev signature := CyclicGrowingEdgeLimits.RearEdge.signature
abbrev actual := CyclicGrowingEdgeLimits.RearEdge.actual
abbrev rejected := CyclicGrowingEdgeLimits.RearEdge.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {h : ℕ → ℝ} {K L H : ℝ},
    Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K) →
    Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20))
      atTop (𝓝 L) →
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20)-L))
      atTop (𝓝 H) → ∀ S : Finset ℝ, S.Nonempty → ∀ r : ℝ,
    let readout := R.readout () ()
    let D := (S.card:ℝ)*r^2-∑ s∈S,s^2
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*((S.card:ℝ)*(n:ℝ)^3*readout (((S,n),h n),r)
        -(3*K/20-3*D/4))-(L+3*K/20+9*D/8))) atTop (𝓝 (H+L-15*D/8))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Tendsto (fun n : ℕ => (n:ℝ)^5*(0:ℝ)^2) atTop (𝓝 0) := by simp
  have hl : Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(0:ℝ)^2)/20-3*0/20))
      atTop (𝓝 0) := by simp
  have hh : Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3*((n:ℝ)^5*(0:ℝ)^2)/20-3*0/20)-0))
      atTop (𝓝 0) := by simp
  have ht := h hs hl hh {0} (by simp) 1
  have ht' : Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3/4)-9/8)) atTop (𝓝 (-15/8)) := by
    convert ht using 1 <;> norm_num [rejected, CyclicGrowingEdgeLimits.RearEdge.rejected, realize]
  have hsmall := ht'.eventually_lt_const (by norm_num : (-15/8:ℝ)<0)
  obtain ⟨n,hn,h'n⟩ := (eventually_ge_atTop (3:ℕ)).and hsmall |>.exists
  have hnR : (3:ℝ)≤n := by exact_mod_cast hn
  exact h'n.not_ge (mul_nonneg (by positivity) (by linarith))

def evidence : Registration arena (type_of% @scaled_rear_second_order) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_rear_second_order, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := CyclicGrowingEdgeLimits.RearEdge.evidence.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@scaled_rear_second_order) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder.SecondOrder.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder.SecondOrder.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SecondOrder


namespace Support

abbrev signature := CyclicGrowingEdgeLimits.Coefficients.signature
abbrev actual := CyclicGrowingEdgeLimits.Coefficients.actual
abbrev rejected := CyclicGrowingEdgeLimits.Coefficients.rejected

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e l : ℕ)
    (_hpar : ∀ᶠ n in atTop, q n % 2 = e) {K L H : ℝ},
    Tendsto (fun n : ℕ => (n:ℝ)^5*(mesh (q n))^2) atTop (𝓝 K) →
    Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(mesh (q n))^2)/20-3*K/20))
      atTop (𝓝 L) →
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3*((n:ℝ)^5*(mesh (q n))^2)/20-3*K/20)-L))
      atTop (𝓝 H) →
    3*K/20=rearThreshold e (l+1) → L+3*K/8=0 → H-3*K/4≠0 →
    let readout := R.readout () ()
    let k := if 0<H-3*K/4 then l+1 else l
    ∀ᶠ n : ℕ in atTop,
      letI : NeZero (q n) := ⟨hq n⟩
      let v : ZMod (q n) → ℝ := windowLaw n k (readout ((rearRealOffsets e k,n),mesh (q n)))
      let threshold := 1-2*budget n*(mesh (q n))^2
      cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
      v ∈ feasible (q n) threshold ∧
        (∀ w ∈ feasible (q n) threshold, w ≠ v → energy v < energy w) ∧
        (∀ w ∈ feasible (q n) threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
        ∀ w ∈ feasible (q n) threshold, IsMinOn energy (feasible (q n) threshold) w →
          ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites (q n) n ∪ rearSites (q n) k

private def ideal (n : ℕ) : ℝ := (Real.pi/Real.sqrt 5)*(n:ℝ)^2*Real.sqrt (n:ℝ)
private def shifted (n : ℕ) : ℝ := ideal n*(1+5/(4*(n:ℝ)))
private def cycles (n : ℕ) : ℕ := if n=0 then 2 else 2*Nat.ceil (shifted n)
private def ratio (n : ℕ) : ℝ := (Nat.ceil (shifted n):ℝ)/ideal n

private theorem ideal_pos {n : ℕ} (hn : 0 < n) : 0 < ideal n := by
  unfold ideal
  exact mul_pos (mul_pos (div_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num)))
    (pow_pos (by exact_mod_cast hn) _)) (Real.sqrt_pos.mpr (by exact_mod_cast hn))

private theorem shifted_pos {n : ℕ} (hn : 0 < n) : 0 < shifted n := by
  unfold shifted
  apply mul_pos (ideal_pos hn)
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  positivity

private theorem cycles_nonzero (n : ℕ) : cycles n≠0 := by
  by_cases hn : n=0
  · simp [cycles,hn]
  · have hc := Nat.ceil_pos.mpr (shifted_pos (Nat.pos_of_ne_zero hn))
    simp [cycles,hn,hc.ne']

private theorem ratio_quadratic_drift :
    Tendsto (fun n : ℕ => (n:ℝ)^2*(ratio n-(1+5/(4*(n:ℝ))))) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hbound : Tendsto (fun n : ℕ => (Real.sqrt 5/Real.pi)*(Real.sqrt (n:ℝ))⁻¹)
      atTop (𝓝 0) := by simpa using hs.const_mul (Real.sqrt 5/Real.pi)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hy := ideal_pos hn
    have hc := Nat.le_ceil (shifted n)
    apply mul_nonneg (sq_nonneg _)
    apply sub_nonneg.mpr
    unfold ratio
    apply (le_div_iff₀ hy).mpr
    simpa [shifted,mul_comm] using hc
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have hy := ideal_pos hn
    have hc : (Nat.ceil (shifted n):ℝ) < shifted n+1 := Nat.ceil_lt_add_one (shifted_pos hn).le
    have hle : ratio n-(1+5/(4*(n:ℝ)))≤(ideal n)⁻¹ := by
      apply sub_le_iff_le_add.mpr
      calc
        ratio n ≤ (shifted n+1)/ideal n := (div_le_div_iff_of_pos_right hy).mpr hc.le
        _ = _ := by
          unfold shifted
          field_simp [hy.ne',hnR.ne']
          ring
    calc
      _ ≤ (n:ℝ)^2*(ideal n)⁻¹ := mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = _ := by
        unfold ideal
        field_simp [hnR.ne',Real.pi_ne_zero,Real.sqrt_ne_zero'.mpr hnR,
          Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<5)]
        <;> ring

private theorem ratio_drift :
    Tendsto (fun n : ℕ => (n:ℝ)*(ratio n-1)) atTop (𝓝 (5/4)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := (ratio_quadratic_drift.mul hi).const_add (5/4:ℝ)
  apply (show Tendsto (fun n : ℕ =>
      5/4+((n:ℝ)^2*(ratio n-(1+5/(4*(n:ℝ)))))*(n:ℝ)⁻¹)
      atTop (𝓝 (5/4)) by simpa using ht).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
  field_simp [hn0]
  ring

private theorem ratio_limit : Tendsto ratio atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := (ratio_drift.mul hi).const_add (1:ℝ)
  apply (show Tendsto (fun n : ℕ => 1+((n:ℝ)*(ratio n-1))*(n:ℝ)⁻¹)
      atTop (𝓝 1) by simpa using ht).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
  field_simp [hn0]
  ring

private theorem scale_eq {n : ℕ} (hn : 0 < n) :
    (n:ℝ)^5*(mesh (cycles n))^2=5/(ratio n)^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hc : (Nat.ceil (shifted n):ℝ)≠0 := by
    exact_mod_cast (Nat.ceil_pos.mpr (shifted_pos hn)).ne'
  have hy := ideal_pos hn
  have hy2 : (ideal n)^2=Real.pi^2*(n:ℝ)^5/5 := by
    unfold ideal
    rw [mul_pow,mul_pow,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤5),Real.sq_sqrt hnR.le]
    ring
  rw [cycles,ite_eq_right hn.ne',mesh,ratio]
  push_cast
  rw [div_pow,div_pow]
  field_simp [hc,hy.ne']
  rw [hy2]
  ring

private theorem cycles_scale :
    Tendsto (fun n : ℕ => (n:ℝ)^5*(mesh (cycles n))^2) atTop (𝓝 5) := by
  have ht := (tendsto_const_nhds (x:=(5:ℝ))).div (ratio_limit.pow 2) (by norm_num)
  apply (show Tendsto (fun n : ℕ => 5/(ratio n)^2) atTop (𝓝 5) by
      change Tendsto (fun n : ℕ => 5/(ratio n)^2) atTop (𝓝 (5/1^2)) at ht
      simpa using ht).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact (scale_eq hn).symm

private theorem cycles_drift :
    Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(mesh (cycles n))^2)/20-3*5/20))
      atTop (𝓝 (-15/8)) := by
  have ht0 := ratio_drift.mul (ratio_limit.add (tendsto_const_nhds (x:=(1:ℝ))))
  have ht := (ht0.const_mul (-3/4:ℝ)).div (ratio_limit.pow 2) (by norm_num)
  apply (show Tendsto (fun n : ℕ => (-3/4)*((n:ℝ)*(ratio n-1)*(ratio n+1))/(ratio n)^2)
      atTop (𝓝 (-15/8)) by
        change Tendsto (fun n : ℕ => (-3/4)*((n:ℝ)*(ratio n-1)*(ratio n+1))/(ratio n)^2)
          atTop (𝓝 ((-3/4)*((5/4)*(1+1))/(1:ℝ)^2)) at ht
        convert ht using 1 <;> norm_num).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),ratio_limit.eventually_ne (by norm_num : (1:ℝ)≠0)]
    with n hn hr
  rw [scale_eq hn]
  field_simp [hr]
  ring

private theorem cycles_second_drift :
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3*((n:ℝ)^5*(mesh (cycles n))^2)/20-3*5/20)-(-15/8)))
      atTop (𝓝 (225/64)) := by
  have h1 := ratio_quadratic_drift.const_mul (-2:ℝ)
  have h2 := (ratio_drift.mul (ratio_limit.add (tendsto_const_nhds (x:=(1:ℝ))))).const_mul (5/2:ℝ)
  have h3 := ratio_drift.pow 2
  have ht := (((h1.add h2).sub h3).const_mul (3/4:ℝ)).div (ratio_limit.pow 2) (by norm_num)
  apply (show Tendsto (fun n : ℕ =>
    (3/4)*(-2*((n:ℝ)^2*(ratio n-(1+5/(4*(n:ℝ)))))+
      (5/2)*((n:ℝ)*(ratio n-1)*(ratio n+1))-((n:ℝ)*(ratio n-1))^2)/(ratio n)^2)
    atTop (𝓝 (225/64)) by
      change Tendsto (fun n : ℕ =>
        (3/4)*(-2*((n:ℝ)^2*(ratio n-(1+5/(4*(n:ℝ)))))+
          (5/2)*((n:ℝ)*(ratio n-1)*(ratio n+1))-((n:ℝ)*(ratio n-1))^2)/(ratio n)^2)
        atTop (𝓝 ((3/4)*(-2*0+(5/2)*((5/4)*(1+1))-(5/4)^2)/(1:ℝ)^2)) at ht
      convert ht using 1 <;> norm_num).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),ratio_limit.eventually_ne (by norm_num : (1:ℝ)≠0)]
    with n hn hr
  rw [scale_eq hn]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
  field_simp [hr,hn0]
  ring

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht := h cycles cycles_nonzero 0 0
    (Eventually.of_forall fun n => by by_cases hn : n=0 <;> simp [cycles,hn])
    cycles_scale cycles_drift cycles_second_drift
    (by norm_num [rearThreshold]) (by norm_num) (by norm_num)
  obtain ⟨n,hn⟩ := ht.exists
  letI : NeZero (cycles n) := ⟨cycles_nonzero n⟩
  have hf := hn.2.2.1
  norm_num only [zero_add,Nat.zero_add,show ¬ (0:ℝ)<225/64-3*5/4 by norm_num,ite_false] at hf
  change windowLaw n 0 0 ∈ feasible (cycles n) _ at hf
  have hz : windowLaw (q := cycles n) n 0 0 = 0 := by
    funext i
    simp only [windowLaw]
    split
    · change _ ⬝ᵥ (0 : Fin 3 → ℝ) = _
      simp
    · rfl
  rw [hz] at hf
  have hm := hf.2.1
  simp at hm

def evidence : Registration arena (type_of% @eventual_support_at_second_order_threshold) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventual_support_at_second_order_threshold, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := CyclicGrowingEdgeLimits.Coefficients.evidence.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@eventual_support_at_second_order_threshold) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder.Support.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder.Support.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body","value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder
