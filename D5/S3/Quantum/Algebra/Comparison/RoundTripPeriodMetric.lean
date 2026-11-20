/- GID: D5/S3/Quantum/Algebra/Comparison/RoundTripPeriodMetric
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/RoundTripPeriodMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential return periods determine the comparison metric. -/
import D5.S3.Analytic.Dilation.DuplicationCircleRigidity
import D5.S3.Quantum.Algebra.Comparison.RoundTripClassification
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! Periods of the exponential comparison curves and their common metric. -/

namespace D5.S3.Quantum.Algebra.Comparison.RoundTripPeriodMetric

open Set Filter RoundTripComparison
open D5.S3.Analytic.Dilation.DuplicationCircleRigidity
open scoped Topology

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A

/-- Comparison data with continuity along the exponential curves. -/
structure ContinuousData (L : LieSubalgebra ℝ A) (G : Subgroup Aˣ) where
  exp_mem : ∀ X : L, expUnit (X : A) ∈ G
  conj_mem : ∀ (g : G) (X : L), (g : Aˣ) * (X : A) * ↑((g : Aˣ)⁻¹) ∈ L
  phi : G → ℝ
  bounded : ∀ g, 0 ≤ phi g ∧ phi g ≤ 1
  faithful : ∀ g, phi g = 1 ↔ g = 1
  duplication : ∀ g, phi (g * g) = (2 * phi g - 1)^2
  conjugation : ∀ g k, phi (k * g * k⁻¹) = phi g
  continuous_ray : ∀ X : L, Continuous fun t : ℝ =>
    phi ⟨expUnit ((t • X : L) : A), exp_mem (t • X)⟩

variable {L : LieSubalgebra ℝ A} {G : Subgroup Aˣ}

def ContinuousData.exp (D : ContinuousData L G) (X : L) : G :=
  ⟨expUnit (X : A), D.exp_mem X⟩

private theorem exp_zero (D : ContinuousData L G) : D.exp 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact NormedSpace.exp_zero

private theorem exp_add (D : ContinuousData L G) (X Y : L)
    (hXY : Commute (X : A) (Y : A)) : D.exp (X + Y) = D.exp X * D.exp Y := by
  apply Subtype.ext
  apply Units.ext
  exact NormedSpace.exp_add_of_commute hXY

private theorem ray_add (D : ContinuousData L G) (X : L) (s t : ℝ) :
    D.exp ((s + t) • X) = D.exp (s • X) * D.exp (t • X) := by
  rw [add_smul]
  exact exp_add D _ _ (((Commute.refl (X : A)).smul_left s).smul_right t)

private theorem exp_kernel_isolated :
    ∃ ε > 0, ∀ X : A, ‖X‖ < ε → NormedSpace.exp X = 1 → X = 0 := by
  let e : A ≃L[ℝ] A := ContinuousLinearEquiv.refl ℝ A
  have hd : HasStrictFDerivAt (NormedSpace.exp : A → A) (e : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hd.eventually_left_inverse
  refine ⟨ε, hε, fun X hX hx => ?_⟩
  have hXe := hball (show X ∈ Metric.ball (0 : A) ε by simpa [Metric.mem_ball, dist_zero_right])
  have h0e := hball (Metric.mem_ball_self hε)
  change hd.localInverse (NormedSpace.exp : A → A) e 0 (NormedSpace.exp X) = X at hXe
  change hd.localInverse (NormedSpace.exp : A → A) e 0 (NormedSpace.exp (0 : A)) = 0 at h0e
  rw [hx] at hXe
  rw [NormedSpace.exp_zero] at h0e
  exact hXe.symm.trans h0e

private theorem even_of_period_lattice {p : ℝ → ℝ}
    (hcont : Continuous p) (hbound : ∀ t, |p t| ≤ 1)
    (hdup : ∀ t, p (2 * t) = 2 * (p t) ^ 2 - 1)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic p T)
    (hlat : ∀ t, p t = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ)) :
    ∀ t, p (-t) = p t := by
  have hzero : p 0 = 1 := (hlat 0).2 ⟨0, by simp⟩
  have hhalf (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) : p (σ * (T / 2)) = -1 := by
    have hone : p (2 * (σ * (T / 2))) = 1 := by
      apply (hlat _).2
      rcases hσ with rfl | rfl
      · exact ⟨1, by push_cast; ring⟩
      · exact ⟨-1, by push_cast; ring⟩
    have hnot : p (σ * (T / 2)) ≠ 1 := by
      intro he
      obtain ⟨k, hk⟩ := (hlat _).1 he
      have hk' : (-1 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 1 := by
        constructor <;> rcases hσ with rfl | rfl <;>
          nlinarith [mul_lt_mul_of_pos_left (show ((1 : ℝ) / 2) < 1 by norm_num) hT]
      have hk0 : k = 0 := by
        have hlo : (-1 : ℤ) < k := by exact_mod_cast hk'.1
        have hhi : k < 1 := by exact_mod_cast hk'.2
        omega
      rw [hk0] at hk
      rcases hσ with rfl | rfl <;> norm_num at hk <;> linarith
    rw [hdup] at hone
    have hfactor : (p (σ * (T / 2)) - 1) * (p (σ * (T / 2)) + 1) = 0 := by
      nlinarith
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hnot))
  have hunique (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (t : ℝ)
      (ht : t ∈ Icc 0 (T / 2)) (hz : p (σ * t) = 0) : t = T / 4 := by
    have h4 : p (4 * (σ * t)) = 1 := by
      rw [show 4 * (σ * t) = 2 * (2 * (σ * t)) by ring, hdup, hdup, hz]
      norm_num
    obtain ⟨k, hk⟩ := (hlat _).1 h4
    have ht0 : 0 < t := by
      refine lt_of_le_of_ne ht.1 ?_
      intro he
      rw [← he, mul_zero, hzero] at hz
      norm_num at hz
    have ht1 : t < T / 2 := by
      refine lt_of_le_of_ne ht.2 ?_
      intro he
      rw [he, hhalf σ hσ] at hz
      norm_num at hz
    rcases hσ with rfl | rfl
    · have hpos : (0 : ℝ) < (k : ℝ) :=
        pos_of_mul_pos_right (by rw [← hk]; positivity) hT.le
      have hlt : (k : ℝ) < 2 := by
        apply lt_of_mul_lt_mul_left _ hT.le
        rw [← hk]
        linarith
      have hk1 : k = 1 := by
        have hlow : (0 : ℤ) < k := by exact_mod_cast hpos
        have hhigh : k < 2 := by exact_mod_cast hlt
        omega
      rw [hk1] at hk
      push_cast at hk
      linarith
    · have hneg : (k : ℝ) < 0 := by
        apply lt_of_mul_lt_mul_left _ hT.le
        rw [mul_zero, ← hk]
        linarith
      have hgt : (-2 : ℝ) < (k : ℝ) := by
        apply lt_of_mul_lt_mul_left _ hT.le
        rw [← hk]
        linarith
      have hk1 : k = -1 := by
        have hlow : (-2 : ℤ) < k := by exact_mod_cast hgt
        have hhigh : k < 0 := by exact_mod_cast hneg
        omega
      rw [hk1] at hk
      push_cast at hk
      linarith
  have hsign (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (t : ℝ) (ht : t ∈ Icc 0 (T / 2)) :
      (t ≤ T / 4 → 0 ≤ p (σ * t)) ∧ (T / 4 ≤ t → p (σ * t) ≤ 0) := by
    have hc : Continuous (fun u : ℝ => p (σ * u)) := by fun_prop
    constructor
    · intro htl
      by_contra! hneg
      obtain ⟨u, hu, hp⟩ := intermediate_value_Icc' ht.1 hc.continuousOn
        (show (0 : ℝ) ∈ Icc (p (σ * t)) (p (σ * 0)) by simp [hneg.le, hzero])
      have hu' := hunique σ hσ u ⟨hu.1, hu.2.trans ht.2⟩ hp
      have hut : u = t := le_antisymm hu.2 (htl.trans_eq hu'.symm)
      exact hneg.ne (hut ▸ hp)
    · intro htr
      by_contra! hpos
      obtain ⟨u, hu, hp⟩ := intermediate_value_Icc' ht.2 hc.continuousOn
        (show (0 : ℝ) ∈ Icc (p (σ * (T / 2))) (p (σ * t)) by simp [hhalf σ hσ, hpos.le])
      have hu' := hunique σ hσ u ⟨ht.1.trans hu.1, hu.2⟩ hp
      have hut : t = u := le_antisymm hu.1 (hu'.trans_le htr)
      exact hpos.ne' (hut.symm ▸ hp)
  have hpair (t : ℝ) (ht : t ∈ Icc 0 T) :
      (0 ≤ p t ∧ 0 ≤ p (-t)) ∨ (p t ≤ 0 ∧ p (-t) ≤ 0) := by
    have hside (u : ℝ) (hu : u ∈ Icc 0 (T / 2)) :
        (0 ≤ p u ∧ 0 ≤ p (-u)) ∨ (p u ≤ 0 ∧ p (-u) ≤ 0) := by
      have hplus := hsign 1 (.inl rfl) u hu
      have hminus := hsign (-1) (.inr rfl) u hu
      rcases le_total u (T / 4) with h | h
      · exact .inl ⟨by simpa using hplus.1 h, by simpa using hminus.1 h⟩
      · exact .inr ⟨by simpa using hplus.2 h, by simpa using hminus.2 h⟩
    by_cases h : t ≤ T / 2
    · exact hside t ⟨ht.1, h⟩
    · have hv := hside (T - t) ⟨by linarith [ht.2], by linarith⟩
      have hp₁ : p (T - t) = p (-t) := by simpa [sub_eq_add_neg, add_comm] using hper (-t)
      have hp₂ : p (-(T - t)) = p t := by
        rw [show -(T - t) = t - T by ring, hper.sub_eq]
      rw [hp₁, hp₂] at hv
      exact hv.elim (fun hh => .inl ⟨hh.2, hh.1⟩) (fun hh => .inr ⟨hh.2, hh.1⟩)
  have hsigns (t : ℝ) : (0 ≤ p t ∧ 0 ≤ p (-t)) ∨ (p t ≤ 0 ∧ p (-t) ≤ 0) := by
    let u := toIcoMod hT 0 t
    have hu : u ∈ Ico 0 T := toIcoMod_mem_Ico' hT t
    have he : u = t - (toIcoDiv hT 0 t : ℝ) * T := by
      rw [← zsmul_eq_mul]
      exact (self_sub_toIcoDiv_zsmul hT 0 t).symm
    have hup : p u = p t := by
      rw [he, ← zsmul_eq_mul, (hper.zsmul _).sub_eq]
    have hdown : p (-u) = p (-t) := by
      rw [he, show -(t - (toIcoDiv hT 0 t : ℝ) * T) =
        -t + (toIcoDiv hT 0 t : ℝ) * T by ring, ← zsmul_eq_mul, hper.zsmul]
    rw [← hup, ← hdown]
    exact hpair u ⟨hu.1, hu.2.le⟩
  let a (t : ℝ) := Real.arccos (p t)
  have ha (t : ℝ) : 0 ≤ a t ∧ a t ≤ Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos (t : ℝ) : Real.cos (a t) = p t :=
    Real.cos_arccos (abs_le.mp (hbound t)).1 (abs_le.mp (hbound t)).2
  have hdouble (t : ℝ) : Real.cos (a (2 * t)) = Real.cos (2 * a t) := by
    rw [hcos, Real.cos_two_mul, hcos, hdup]
  have hpos (t : ℝ) (ht : 0 ≤ p t) : a (2 * t) = 2 * a t := by
    have hle : a t ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr ht
    exact Real.strictAntiOn_cos.injOn (ha _) ⟨by linarith [(ha t).1], by linarith⟩
      (hdouble t)
  have hneg (t : ℝ) (ht : p t ≤ 0) : a (2 * t) = 2 * Real.pi - 2 * a t := by
    have hle : Real.pi / 2 ≤ a t := Real.pi_div_two_le_arccos.mpr ht
    apply Real.strictAntiOn_cos.injOn (ha _) ⟨by linarith [(ha t).2], by linarith⟩
    rw [Real.cos_two_pi_sub]
    exact hdouble t
  let f (t : ℝ) := |a t - a (-t)|
  have hd (t : ℝ) : f (2 * t) = 2 * f t := by
    dsimp [f]
    rw [show -(2 * t) = 2 * (-t) by ring]
    rcases hsigns t with hh | hh
    · rw [hpos t hh.1, hpos (-t) hh.2, ← mul_sub, abs_mul]
      norm_num
    · rw [hneg t hh.1, hneg (-t) hh.2, show
        2 * Real.pi - 2 * a t - (2 * Real.pi - 2 * a (-t)) =
          -(2 * (a t - a (-t))) by ring, abs_neg, abs_mul]
      norm_num
  intro t
  have hvanish := le_zero_of_bounded_doubling (s := univ) f (C := Real.pi)
    (fun u _ => abs_le.mpr ⟨by linarith [(ha u).1, (ha (-u)).2],
      by linarith [(ha u).2, (ha (-u)).1]⟩)
    (fun u _ => ⟨2 * u, mem_univ _, (hd u).ge⟩) (mem_univ t)
  have he : a t = a (-t) := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hvanish (abs_nonneg _)))
  rw [← hcos (-t), ← hcos t, he]

private theorem ray_period_cosine (D : ContinuousData L G) (X : L) (hX : X ≠ 0) :
    ∃ T > 0, (∀ t : ℝ, D.exp (t • X) = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ)) ∧
      ∀ t : ℝ, 2 * D.phi (D.exp (t • X)) - 1 = Real.cos (2 * Real.pi * t / T) := by
  let p (t : ℝ) := 2 * D.phi (D.exp (t • X)) - 1
  have hcont : Continuous p := (continuous_const.mul (D.continuous_ray X)).sub continuous_const
  have hone (t : ℝ) : p t = 1 ↔ D.exp (t • X) = 1 := by
    rw [← D.faithful]
    dsimp [p]
    constructor <;> intro h <;> linarith
  have hzero : p 0 = 1 := (hone 0).2 (by rw [zero_smul, exp_zero D])
  have hbound (t : ℝ) : |p t| ≤ 1 := by
    obtain ⟨hl, hu⟩ := D.bounded (D.exp (t • X))
    exact abs_le.mpr ⟨by dsimp [p]; linarith, by dsimp [p]; linarith⟩
  have hdup (t : ℝ) : p (2 * t) = 2 * (p t)^2 - 1 := by
    dsimp only [p]
    rw [show (2 : ℝ) * t = t + t by ring, ray_add, D.duplication]
  have hperiod (s : ℝ) (hs : p s = 1) : Function.Periodic p s := by
    intro t
    dsimp only [p]
    rw [ray_add, (hone s).1 hs, mul_one]
  have hneg (s : ℝ) (hs : p s = 1) : p (-s) = 1 := by
    have h := hperiod s hs (-s)
    rwa [neg_add_cancel, hzero, eq_comm] at h
  have hisolated : ∃ ε > 0, ∀ t ∈ Ioo (-ε) ε, p t = 1 → t = 0 := by
    obtain ⟨δ, hδ, hlocal⟩ := exp_kernel_isolated (A := A)
    have hnorm : 0 < ‖(X : A)‖ := norm_pos_iff.mpr (fun h => hX (Subtype.ext h))
    refine ⟨δ / ‖(X : A)‖, div_pos hδ hnorm, fun t ht hp => ?_⟩
    have hsmall : ‖t • (X : A)‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (lt_div_iff₀ hnorm).mp (abs_lt.mpr ht)
    have hexp : NormedSpace.exp (t • (X : A)) = 1 :=
      congrArg (fun g : G => (g : Aˣ).val) ((hone t).1 hp)
    exact (smul_eq_zero.mp (hlocal _ hsmall hexp)).resolve_right (norm_pos_iff.mp hnorm)
  let K : AddSubgroup ℝ :=
    { carrier := {t | p t = 1}
      zero_mem' := hzero
      add_mem' := fun {x y} hx hy => (hperiod y hy x).trans hx
      neg_mem' := fun {s} => hneg s }
  have hnotdense : ¬ Dense (K : Set ℝ) := by
    intro hd
    obtain ⟨ε, hε, hlocal⟩ := hisolated
    obtain ⟨t, ht, htK⟩ := hd.inter_open_nonempty (Ioo 0 ε) isOpen_Ioo
      (nonempty_Ioo.mpr hε)
    exact ht.1.ne' (hlocal t ⟨by linarith [ht.1], ht.2⟩ htK)
  have hreturn : ∃ t > 0, p t = 1 := by
    by_contra! h
    exact no_faithful_duplication_on_line ⟨p, hcont, hzero, hbound, hdup,
      fun t ht => lt_of_le_of_ne (abs_le.mp (hbound t)).2 (h t ht)⟩
  obtain ⟨a, ha⟩ := K.isAddCyclic_iff_exists_zmultiples_eq_top.mp
    (K.dense_or_isCyclic.resolve_left hnotdense)
  have hlattice (t : ℝ) : p t = 1 ↔ ∃ k : ℤ, t = (a : ℝ) * (k : ℝ) := by
    change t ∈ K ↔ _
    rw [← ha, AddSubgroup.mem_zmultiples_iff]
    exact exists_congr fun k => by rw [zsmul_eq_mul, mul_comm (k : ℝ), eq_comm]
  have habs : 0 < |(a : ℝ)| := by
    obtain ⟨t, ht, hp⟩ := hreturn
    obtain ⟨k, hk⟩ := (hlattice t).1 hp
    refine abs_pos.mpr (fun h => ht.ne' ?_)
    simpa [h] using hk
  have hlattice_abs (t : ℝ) : p t = 1 ↔ ∃ k : ℤ, t = |(a : ℝ)| * (k : ℝ) := by
    rw [hlattice]
    by_cases ha0 : (0 : ℝ) ≤ a
    · rw [abs_of_nonneg ha0]
    · rw [abs_of_neg (lt_of_not_ge ha0)]
      constructor <;> rintro ⟨k, hk⟩ <;> refine ⟨-k, ?_⟩ <;> push_cast <;> linarith
  have habs_mem : p |(a : ℝ)| = 1 := (hlattice_abs _).2 ⟨1, by simp⟩
  have heven := even_of_period_lattice hcont hbound hdup habs (hperiod _ habs_mem) hlattice_abs
  obtain ⟨T, hT, hlat, hcos⟩ := eq_scaled_cos_of_discrete_fibre hcont hbound hzero heven hdup
    hisolated hperiod
  exact ⟨T, hT, fun t => (hone t).symm.trans (hlat t), hcos⟩

end
end D5.S3.Quantum.Algebra.Comparison.RoundTripPeriodMetric
