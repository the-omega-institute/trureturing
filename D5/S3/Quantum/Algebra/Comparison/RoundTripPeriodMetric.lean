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
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

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

section ComplexOperators

open Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

private theorem exp_apply_of_sq_zero (f : V →L[ℂ] V) (x : V) (hx : f (f x) = 0) :
    NormedSpace.exp f x = x + f x := by
  have hp (n : ℕ) : (f ^ (n + 2)) x = 0 := by
    rw [pow_add, mul_apply_eq_comp, pow_two, mul_apply_eq_comp, hx, map_zero]
  have hs := (ContinuousLinearMap.apply ℂ V x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) f)
  simp only [ContinuousLinearMap.apply_apply] at hs
  rw [← hs.tsum_eq, tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro n hn
    have h : 2 ≤ n := Nat.le_of_not_gt (fun hh => hn (Finset.mem_range.mpr hh))
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm 2 k, ← algebraMap_smul ℂ]
    change (algebraMap ℚ ℂ ((↑(k + 2).factorial : ℚ)⁻¹)) • ((f ^ (k + 2)) x) = 0
    rw [hp k, smul_zero]

private theorem exp_apply_of_shift_sq_zero (f : V →L[ℂ] V) (z : ℂ)
    (x : V) (hx : (f - algebraMap ℂ (V →L[ℂ] V) z)
      ((f - algebraMap ℂ (V →L[ℂ] V) z) x) = 0) :
    NormedSpace.exp f x = Complex.exp z • (x + (f - algebraMap ℂ (V →L[ℂ] V) z) x) := by
  let r := algebraMap ℂ (V →L[ℂ] V) z
  have hc : Commute r (f - r) := (Algebra.commute_algebraMap_left z f).sub_right (Commute.refl r)
  have he : NormedSpace.exp f = NormedSpace.exp r * NormedSpace.exp (f - r) := by
    simpa only [add_sub_cancel, add_comm r f] using NormedSpace.exp_add_of_commute hc
  rw [he, mul_apply_eq_comp, exp_apply_of_sq_zero _ _ hx]
  change NormedSpace.exp (algebraMap ℂ (V →L[ℂ] V) z) _ = _
  rw [← NormedSpace.map_exp (algebraMap ℂ (V →L[ℂ] V)) (continuous_algebraMap _ _),
    ← Complex.exp_eq_exp_ℂ]
  rfl

private theorem exp_apply_of_eigen (f : V →L[ℂ] V) (z : ℂ) (x : V)
    (hx : f x = z • x) : NormedSpace.exp f x = Complex.exp z • x := by
  have h0 : (f - algebraMap ℂ (V →L[ℂ] V) z) x = 0 := by
    change f x - z • x = 0
    rw [hx, sub_self]
  rw [exp_apply_of_shift_sq_zero f z x (by rw [h0, map_zero]), h0, add_zero]

private theorem kernels_of_shift_pow (f : V →L[ℂ] V) (hf : NormedSpace.exp f = 1)
    (z : ℂ) (n : ℕ) (x : V)
    (hx : ((f - algebraMap ℂ (V →L[ℂ] V) z) ^ n) x = 0) :
    f x = z • x := by
  let N := f - algebraMap ℂ (V →L[ℂ] V) z
  have hstep (v : V) (hv : N (N v) = 0) : N v = 0 := by
    by_contra hw
    have hEig : f (N v) = z • N v := sub_eq_zero.mp hv
    have he := exp_apply_of_eigen f z (N v) hEig
    rw [hf, one_apply_eq_self] at he
    have hscalar : Complex.exp z = 1 := by
      have hc : (1 - Complex.exp z) • N v = 0 := by
        rw [sub_smul, one_smul, ← he, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp hc).resolve_right hw)).symm
    have hv' := exp_apply_of_shift_sq_zero f z v hv
    rw [hf, one_apply_eq_self, hscalar, one_smul] at hv'
    apply hw
    exact add_left_cancel (hv'.symm.trans (add_zero v).symm)
  suffices h : N x = 0 from sub_eq_zero.mp h
  change (N ^ n) x = 0 at hx
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    rw [hx0, map_zero]
  | succ n ih =>
    apply hstep
    apply ih
    simpa [pow_succ, mul_apply_eq_comp] using hx

variable [FiniteDimensional ℂ V]

private theorem periodic_operator_basis (f : V →L[ℂ] V) (hf : NormedSpace.exp f = 1) :
    ∃ (b : Basis (Fin (finrank ℂ V)) ℂ V) (k : Fin (finrank ℂ V) → ℤ),
      ∀ i, f (b i) = ((k i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) • b i := by
  classical
  let F : Module.End ℂ V := f
  let S := {x : V | ∃ z : ℂ, F x = z • x}
  have htop : ⊤ ≤ Submodule.span ℂ S := by
    rw [← F.iSup_maxGenEigenspace_eq_top]
    apply iSup_le
    intro z x hx
    obtain ⟨n, hn⟩ := (F.mem_maxGenEigenspace z x).mp hx
    have hnx : ((f - algebraMap ℂ (V →L[ℂ] V) z) ^ n) x = 0 := by
      change (↑((f - algebraMap ℂ (V →L[ℂ] V) z) ^ n) : Module.End ℂ V) x = 0
      simpa only [ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.toLinearMap_sub,
        Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.toLinearMap_one] using hn
    exact Submodule.subset_span ⟨z, kernels_of_shift_pow f hf z n x hnx⟩
  let s := (linearIndepOn_empty ℂ (@id V)).extend (empty_subset S)
  let c : Basis s ℂ V := Basis.ofSpan htop
  let : Fintype s := c.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℂ V)
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm
  let b : Basis (Fin (finrank ℂ V)) ℂ V := c.reindex e
  have hb (i : Fin (finrank ℂ V)) : ∃ z : ℂ, f (b i) = z • b i := by
    apply Basis.ofSpan_subset htop
    exact ⟨e.symm i, by change c (e.symm i) = b i; simp only [b, Basis.reindex_apply]⟩
  choose z hz using hb
  have hk (i : Fin (finrank ℂ V)) :
      ∃ k : ℤ, z i = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have he := exp_apply_of_eigen f (z i) (b i) (hz i)
    rw [hf, one_apply_eq_self] at he
    have hz1 : Complex.exp (z i) = 1 := by
      have h0 : (1 - Complex.exp (z i)) • b i = 0 := by
        rw [sub_smul, one_smul, ← he, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right (b.ne_zero i))).symm
    exact Complex.exp_eq_one_iff.mp hz1
  choose k hk using hk
  exact ⟨b, k, fun i => by simpa only [← hk i] using hz i⟩

private theorem scaled_periodic_operator_basis (f : V →L[ℂ] V) (T : ℝ) (hT : T ≠ 0)
    (hf : NormedSpace.exp (T • f) = 1) :
    ∃ (b : Basis (Fin (finrank ℂ V)) ℂ V) (k : Fin (finrank ℂ V) → ℤ),
      ∀ i, f (b i) =
        (((2 * Real.pi / T * (k i : ℝ) : ℝ) : ℂ) * Complex.I) • b i := by
  obtain ⟨b, k, hk⟩ := periodic_operator_basis (T • f) hf
  refine ⟨b, k, fun i => ?_⟩
  have hki := hk i
  change (T : ℂ) • f (b i) = _ at hki
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  apply (smul_right_injective V hT')
  dsimp only
  rw [hki, smul_smul]
  congr 1
  push_cast
  field_simp

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
private theorem det_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (F : Module.End ℂ V) (z : ι → ℂ) (hz : ∀ i, F (b i) = z i • b i) :
    F.det = ∏ i, z i := by
  classical
  have hM : LinearMap.toMatrix b b F = Matrix.diagonal z := by
    ext i j
    by_cases h : i = j
    · subst i; simp [LinearMap.toMatrix_apply, hz]
    · simp [LinearMap.toMatrix_apply, hz, Matrix.diagonal_apply_ne _ h, Ne.symm h]
  rw [← LinearMap.det_toMatrix b, hM, Matrix.det_diagonal]

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
private theorem trace_sq_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (F : Module.End ℂ V) (z : ι → ℂ) (hz : ∀ i, F (b i) = z i • b i) :
    LinearMap.trace ℂ V (F * F) = ∑ i, (z i)^2 := by
  classical
  have hM : LinearMap.toMatrix b b F = Matrix.diagonal z := by
    ext i j
    by_cases h : i = j
    · subst i; simp [LinearMap.toMatrix_apply, hz]
    · simp [LinearMap.toMatrix_apply, hz, Matrix.diagonal_apply_ne _ h, Ne.symm h]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_mul, hM,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [pow_two]

private theorem operator_return_iff (f : V →L[ℂ] V) (T : ℝ) (hT : T ≠ 0)
    (hf : NormedSpace.exp (T • f) = 1) (t : ℝ) :
    NormedSpace.exp (t • f) = 1 ↔ ∀ z : ℂ, Module.End.HasEigenvalue (f : Module.End ℂ V) z →
      Complex.exp ((t : ℂ) * z) = 1 := by
  constructor
  · intro he z hz
    obtain ⟨v, hmem, hv⟩ := hz.exists_hasEigenvector
    have heig := Module.End.mem_eigenspace_iff.mp hmem
    have ht : (t • f) v = ((t : ℂ) * z) • v := by
      change (t : ℂ) • f v = _
      rw [show f v = z • v from heig, mul_smul]
    have hh := exp_apply_of_eigen (t • f) ((t : ℂ) * z) v ht
    rw [he, one_apply_eq_self] at hh
    have h0 : (1 - Complex.exp ((t : ℂ) * z)) • v = 0 := by
      rw [sub_smul, one_smul, ← hh, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hv)).symm
  · intro h
    obtain ⟨b, k, hk⟩ := scaled_periodic_operator_basis f T hT hf
    suffices hLin : ((NormedSpace.exp (t • f) : V →L[ℂ] V) : Module.End ℂ V) = 1 by
      exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun hLin x
    apply b.ext
    intro i
    let z : ℂ := ((2 * Real.pi / T * (k i : ℝ) : ℝ) : ℂ) * Complex.I
    have hz : Module.End.HasEigenvalue (f : Module.End ℂ V) z :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (hk i), b.ne_zero i⟩
    change (NormedSpace.exp (t • f)) (b i) = b i
    have ht : (t • f) (b i) = ((t : ℂ) * z) • b i := by
      change (t : ℂ) • f (b i) = _
      exact (congrArg (fun w : V => (t : ℂ) • w) (show f (b i) = z • b i from hk i)).trans
        (mul_smul (t : ℂ) z (b i)).symm
    rw [exp_apply_of_eigen (t • f) ((t : ℂ) * z) (b i) ht, h z hz, one_smul]

end ComplexOperators

section TraceForm

open Module
open scoped BigOperators

variable [FiniteDimensional ℝ A]

private abbrev RegularSpace (A : Type*) [AddCommGroup A] [Module ℝ A] :=
  Fin (finrank ℝ A) → ℂ

private def regularOperator : A →ₐ[ℝ] (RegularSpace A →L[ℂ] RegularSpace A) := by
  let V := RegularSpace A
  let c : Module.End ℂ V →ₐ[ℂ] (V →L[ℂ] V) :=
    { toFun := fun f => LinearMap.toContinuousLinearMap f
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let b := Module.finBasis ℝ A
  exact (c.restrictScalars ℝ).comp
    ((Matrix.toLinAlgEquiv'.toAlgHom.restrictScalars ℝ).comp
      (((RCLike.ofRealAm : ℝ →ₐ[ℝ] ℂ).mapMatrix).comp
        ((LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul ℝ A))))

omit [CompleteSpace A] in
private theorem regularOperator_injective :
    Function.Injective (regularOperator (A := A)) := by
  intro x y h
  apply Algebra.lmul_injective (R := ℝ)
  apply (LinearMap.toMatrixAlgEquiv (Module.finBasis ℝ A)).injective
  apply Matrix.map_injective Complex.ofReal_injective
  apply Matrix.toLinAlgEquiv'.injective
  exact congrArg ContinuousLinearMap.toLinearMap h

omit [CompleteSpace A] in
private theorem regularOperator_continuous :
    Continuous (regularOperator (A := A) : A → (RegularSpace A →L[ℂ] RegularSpace A)) := by
  exact (regularOperator (A := A)).toLinearMap.continuous_of_finiteDimensional

private theorem regularOperator_exp (x : A) :
    NormedSpace.exp (regularOperator x) = regularOperator (NormedSpace.exp x) :=
  (NormedSpace.map_exp regularOperator regularOperator_continuous x).symm

private def traceForm : LinearMap.BilinForm ℝ L :=
  LinearMap.mk₂ ℝ (fun x y =>
    -(LinearMap.trace ℂ (RegularSpace A)
      ((regularOperator (x : A) : Module.End ℂ (RegularSpace A)) *
        (regularOperator (y : A) : Module.End ℂ (RegularSpace A)))).re)
    (by intro x x' y; simp [add_mul, Complex.add_re, add_comm])
    (by intro r x y; simp [Complex.mul_re])
    (by intro x y y'; simp [mul_add, Complex.add_re, add_comm])
    (by intro r x y; simp [Complex.mul_re])

omit [CompleteSpace A] in
private theorem traceForm_symm : (traceForm (L := L)).IsSymm := by
  constructor
  intro x y
  change -(LinearMap.trace ℂ _
    ((regularOperator (x : A) : Module.End ℂ (RegularSpace A)) *
      (regularOperator (y : A) : Module.End ℂ (RegularSpace A)))).re = _
  rw [LinearMap.trace_mul_comm]
  rfl

private theorem operator_period_iff (D : ContinuousData L G) (X : L) (t : ℝ) :
    NormedSpace.exp (t • regularOperator (X : A)) = 1 ↔ D.exp (t • X) = 1 := by
  rw [← map_smul, regularOperator_exp, ← map_one regularOperator,
    regularOperator_injective.eq_iff]
  constructor
  · intro h
    apply Subtype.ext
    apply Units.ext
    exact h
  · intro h
    exact congrArg (fun g : G => (g : Aˣ).val) h

private theorem regularOperator_eigenbasis (D : ContinuousData L G) (X : L) (hX : X ≠ 0) :
    ∃ (T : ℝ) (b : Basis (Fin (finrank ℂ (RegularSpace A))) ℂ (RegularSpace A))
        (k : Fin (finrank ℂ (RegularSpace A)) → ℤ),
      0 < T ∧ ∀ i, regularOperator (X : A) (b i) =
        (((2 * Real.pi / T * (k i : ℝ) : ℝ) : ℂ) * Complex.I) • b i := by
  obtain ⟨T, hT, hlat, _⟩ := ray_period_cosine D X hX
  have hreturn : D.exp (T • X) = 1 := (hlat T).2 ⟨1, by simp⟩
  obtain ⟨b, k, he⟩ := scaled_periodic_operator_basis _ T hT.ne'
    ((operator_period_iff D X T).2 hreturn)
  exact ⟨T, b, k, hT, he⟩

omit [CompleteSpace A] in
private theorem traceForm_eigenvalues (X : L) (T : ℝ)
    (b : Basis (Fin (finrank ℂ (RegularSpace A))) ℂ (RegularSpace A))
    (k : Fin (finrank ℂ (RegularSpace A)) → ℤ)
    (he : ∀ i, regularOperator (X : A) (b i) =
      (((2 * Real.pi / T * (k i : ℝ) : ℝ) : ℂ) * Complex.I) • b i) :
    traceForm X X = (2 * Real.pi / T)^2 * (∑ i, ((k i : ℝ)^2)) := by
  let F : Module.End ℂ (RegularSpace A) := regularOperator (X : A)
  change -(LinearMap.trace ℂ (RegularSpace A) (F * F)).re = _
  rw [trace_sq_of_eigenbasis b F _ he]
  change -Complex.reLm (∑ i, ((↑(2 * Real.pi / T * (k i : ℝ) : ℝ) : ℂ) * Complex.I)^2) = _
  rw [map_sum, ← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change -(((↑(2 * Real.pi / T * (k i : ℝ) : ℝ) : ℂ) * Complex.I)^2).re = _
  simp [pow_two, Complex.mul_re, Complex.mul_im]
  ring

private theorem traceForm_pos (D : ContinuousData L G) (X : L) (hX : X ≠ 0) :
    0 < traceForm X X := by
  obtain ⟨T, b, k, hT, he⟩ := regularOperator_eigenbasis D X hX
  have hk : ∃ i, k i ≠ 0 := by
    by_contra! h
    apply hX
    apply Subtype.ext
    apply regularOperator_injective
    change regularOperator (X : A) = regularOperator (0 : A)
    rw [map_zero]
    suffices hF : (regularOperator (X : A) : Module.End ℂ (RegularSpace A)) = 0 by
      exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun hF x
    apply b.ext
    intro i
    simpa [h i] using he i
  rw [traceForm_eigenvalues X T b k he]
  apply mul_pos (sq_pos_of_pos (by positivity))
  obtain ⟨i, hi⟩ := hk
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i,
    sq_pos_of_ne_zero (by exact_mod_cast hi)⟩

private def normalizedDirection (X : L) : L := (Real.sqrt (traceForm X X))⁻¹ • X

private theorem normalizedDirection_ne_zero (D : ContinuousData L G) {X : L} (hX : X ≠ 0) :
    normalizedDirection X ≠ 0 := by
  have hp := Real.sqrt_pos.2 (traceForm_pos D X hX)
  exact smul_ne_zero (inv_ne_zero hp.ne') hX

private def normalizedOperator (X : L) : RegularSpace A →L[ℂ] RegularSpace A :=
  regularOperator (normalizedDirection X : A)

private theorem normalizedOperator_has_period (D : ContinuousData L G) {X : L} (hX : X ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ NormedSpace.exp (T • normalizedOperator X) = 1 := by
  obtain ⟨T, hT, hlat, _⟩ := ray_period_cosine D _ (normalizedDirection_ne_zero D hX)
  exact ⟨T, hT, (operator_period_iff D _ _).2 ((hlat T).2 ⟨1, by simp⟩)⟩

private def normalizedDet (z : ℂ) (X : L) : ℂ :=
  (algebraMap ℂ _ z - normalizedOperator X).det

private theorem normalizedDet_continuous (D : ContinuousData L G) (z : ℂ) :
    ContinuousOn (normalizedDet (L := L) z) ({0}ᶜ : Set L) := by
  have hB : Continuous fun X : L => traceForm X X := by
    change Continuous fun X : L => traceForm.toContinuousBilinearMap X X
    fun_prop
  have hn : ContinuousOn (normalizedDirection (L := L)) ({0}ᶜ : Set L) := by
    apply (Real.continuous_sqrt.comp hB).continuousOn.inv₀
      (fun X hX => (Real.sqrt_pos.2 (traceForm_pos D X hX)).ne') |>.smul continuousOn_id
  exact ContinuousLinearMap.continuous_det.comp_continuousOn
    (continuousOn_const.sub (regularOperator_continuous.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hn)))

private theorem normalizedDet_countable (D : ContinuousData L G) (z : ℂ) :
    (normalizedDet z '' ({0}ᶜ : Set L)).Countable := by
  let n := finrank ℂ (RegularSpace A)
  let C (k : Fin n → ℤ) : ℂ := ∏ i,
    (z - ((↑((k i : ℝ) / Real.sqrt (∑ j, ((k j : ℝ)^2)) : ℝ) : ℂ) * Complex.I))
  apply (countable_range C).mono
  rintro w ⟨X, hX, rfl⟩
  obtain ⟨T, b, k, hT, hEig⟩ := regularOperator_eigenbasis D X hX
  refine ⟨k, ?_⟩
  have ha : 0 < 2 * Real.pi / T := by positivity
  have hscale : Real.sqrt (traceForm X X) =
      (2 * Real.pi / T) * Real.sqrt (∑ i, ((k i : ℝ)^2)) := by
    rw [traceForm_eigenvalues X T b k hEig, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]
  have hd : ∀ i, normalizedOperator X (b i) =
      ((↑((k i : ℝ) / Real.sqrt (∑ j, ((k j : ℝ)^2)) : ℝ) : ℂ) * Complex.I) • b i := by
    intro i
    dsimp only [normalizedOperator, normalizedDirection]
    rw [show ((Real.sqrt (traceForm X X))⁻¹ • X : L).val =
      (Real.sqrt (traceForm X X))⁻¹ • (X : A) from rfl, map_smul]
    change (↑((Real.sqrt (traceForm X X))⁻¹) : ℂ) • regularOperator (X : A) (b i) = _
    have hr : (Real.sqrt (traceForm X X))⁻¹ * (2 * Real.pi / T * (k i : ℝ)) =
        (k i : ℝ) / Real.sqrt (∑ j, ((k j : ℝ)^2)) := by
      rw [hscale, mul_inv_rev]
      calc
        _ = ((∑ j, ((k j : ℝ)^2)).sqrt)⁻¹ * ((2 * Real.pi / T)⁻¹ *
            (2 * Real.pi / T)) * (k i : ℝ) := by ring
        _ = _ := by rw [inv_mul_cancel₀ ha.ne']; ring
    rw [hEig, smul_smul, ← mul_assoc, ← Complex.ofReal_mul, hr]
  change _ = ((algebraMap ℂ _ z - normalizedOperator X : _ →L[ℂ] _).toLinearMap).det
  rw [det_of_eigenbasis b _ _ (fun i => by
    change z • b i - normalizedOperator X (b i) = _
    rw [hd, sub_smul])]

private theorem normalizedDet_constant (D : ContinuousData L G) (hd : 1 < finrank ℝ L)
    (z : ℂ) {X Y : L} (hX : X ≠ 0) (hY : Y ≠ 0) :
    normalizedDet z X = normalizedDet z Y := by
  have hr : (1 : Cardinal) < Module.rank ℝ L := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hd
  let S := normalizedDet z '' ({0}ᶜ : Set L)
  have hS : IsPreconnected S :=
    (isConnected_compl_singleton_of_one_lt_rank hr (0 : L)).isPreconnected.image _
      (normalizedDet_continuous D z)
  let f : ℂ → ℝ := fun w => dist w (normalizedDet z X)
  have hf : Continuous f := continuous_id.dist continuous_const
  have hc : (f '' S).Countable := (normalizedDet_countable D z).image f
  have hconn := (hS.image f hf.continuousOn).ordConnected
  have h0 : (0 : ℝ) ∈ f '' S := by
    exact ⟨normalizedDet z X, ⟨X, hX, rfl⟩, dist_self _⟩
  have h1 : f (normalizedDet z Y) ∈ f '' S :=
    ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
  have hI : Ioo 0 (f (normalizedDet z Y)) ⊆ f '' S := fun _ ht =>
    hconn.out h0 h1 ⟨ht.1.le, ht.2.le⟩
  have hz := Cardinal.Real.Ioo_countable_iff.mp (hc.mono hI)
  exact (dist_eq_zero.mp (le_antisymm hz dist_nonneg)).symm

private theorem normalized_period_eq_of_dim (D : ContinuousData L G) (hd : 1 < finrank ℝ L)
    {X Y : L} (hX : X ≠ 0) (hY : Y ≠ 0) (t : ℝ) :
    D.exp (t • normalizedDirection X) = 1 ↔ D.exp (t • normalizedDirection Y) = 1 := by
  obtain ⟨s, hs, hs1⟩ := normalizedOperator_has_period D hX
  obtain ⟨u, hu, hu1⟩ := normalizedOperator_has_period D hY
  rw [← operator_period_iff, ← operator_period_iff]
  change NormedSpace.exp (t • normalizedOperator X) = 1 ↔
    NormedSpace.exp (t • normalizedOperator Y) = 1
  rw [operator_return_iff _ s hs.ne' hs1, operator_return_iff _ u hu.ne' hu1]
  have he (z : ℂ) :
      Module.End.HasEigenvalue (normalizedOperator X : Module.End ℂ (RegularSpace A)) z ↔
        Module.End.HasEigenvalue (normalizedOperator Y : Module.End ℂ (RegularSpace A)) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly]
    change (normalizedOperator X : Module.End ℂ (RegularSpace A)).charpoly.eval z = 0 ↔
      (normalizedOperator Y : Module.End ℂ (RegularSpace A)).charpoly.eval z = 0
    rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly]
    change normalizedDet z X = 0 ↔ normalizedDet z Y = 0
    rw [normalizedDet_constant D hd z hX hY]
  exact forall_congr' fun z => by rw [he z]

private theorem trace_normalized (D : ContinuousData L G) {X : L} (hX : X ≠ 0) :
    traceForm (normalizedDirection X) (normalizedDirection X) = 1 := by
  have h := traceForm_pos D X hX
  have hs := Real.sqrt_pos.2 h
  simp only [normalizedDirection, map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp [hs.ne']
  nlinarith [Real.sq_sqrt h.le]

private theorem normalized_period_eq (D : ContinuousData L G)
    {X Y : L} (hX : X ≠ 0) (hY : Y ≠ 0) (t : ℝ) :
    D.exp (t • normalizedDirection X) = 1 ↔ D.exp (t • normalizedDirection Y) = 1 := by
  by_cases hd : 1 < finrank ℝ L
  · exact normalized_period_eq_of_dim D hd hX hY t
  · have hp : 0 < finrank ℝ L := finrank_pos_iff_exists_ne_zero.mpr ⟨X, hX⟩
    have hdim : finrank ℝ L = 1 := by omega
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim
      (normalizedDirection_ne_zero D hX) (normalizedDirection Y)
    have hn := trace_normalized D hY
    rw [← hc] at hn
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, trace_normalized D hX,
      mul_one] at hn
    have he : c = 1 ∨ c = -1 := by
      exact (mul_eq_zero.mp (show (c - 1) * (c + 1) = 0 by nlinarith)).imp
        sub_eq_zero.mp eq_neg_of_add_eq_zero_left
    rcases he with rfl | rfl
    · simp only [one_smul] at hc
      rw [hc]
    · have hneg : normalizedDirection Y = -normalizedDirection X := by simpa using hc.symm
      rw [hneg, smul_neg, ← neg_smul]
      have h := (ray_add D (normalizedDirection X) (-t) t).symm
      rw [neg_add_cancel, zero_smul, exp_zero D] at h
      constructor
      · intro hh
        rwa [hh, mul_one] at h
      · intro hh
        rwa [hh, one_mul] at h

private theorem lattice_generator_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ t : ℝ, (∃ n : ℤ, t = a * (n : ℝ)) ↔ ∃ n : ℤ, t = b * (n : ℝ)) :
    a = b := by
  have hle (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
      (hmem : ∃ n : ℤ, v = u * (n : ℝ)) : u ≤ v := by
    obtain ⟨n, hn⟩ := hmem
    have hn0 : (0 : ℝ) < (n : ℝ) := pos_of_mul_pos_right (hn ▸ hv) hu.le
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn0
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    simpa [hn] using mul_le_mul_of_nonneg_left h1 hu.le
  exact le_antisymm (hle a b ha hb ((h b).mpr ⟨1, by simp⟩))
    (hle b a hb ha ((h a).mp ⟨1, by simp⟩))

private theorem exists_period_metric (D : ContinuousData L G) :
    ∃ H : LinearMap.BilinForm ℝ L, H.IsSymm ∧
      (∀ X : L, 0 ≤ H X X) ∧
      (∀ X : L, X ≠ 0 → ∃ T > 0,
        (∀ t : ℝ, D.exp (t • X) = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ)) ∧
        H X X = 2 * Real.pi^2 / T^2) ∧
      (∀ (t : ℝ) (X : L), D.phi (D.exp (t • X)) = Real.cos (t * Real.sqrt (H X X / 2))^2) := by
  by_cases hL : ∃ X : L, X ≠ 0
  · obtain ⟨X₀, hX₀⟩ := hL
    obtain ⟨T₀, hT₀, hlat₀, _⟩ := ray_period_cosine D (normalizedDirection X₀)
      (normalizedDirection_ne_zero D hX₀)
    let H : LinearMap.BilinForm ℝ L := (2 * (Real.pi / T₀)^2) • traceForm
    have hsym : H.IsSymm := by
      constructor
      intro x y
      simp only [H, LinearMap.smul_apply, traceForm_symm.eq]
    have hnonneg (X : L) : 0 ≤ H X X := by
      by_cases hx : X = 0
      · simp [hx]
      · exact mul_nonneg (by positivity) (traceForm_pos D X hx).le
    have hlaws (X : L) (hx : X ≠ 0) : ∃ T > 0,
        (∀ t : ℝ, D.exp (t • X) = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ)) ∧
        H X X = 2 * Real.pi^2 / T^2 ∧
        ∀ t : ℝ, 2 * D.phi (D.exp (t • X)) - 1 = Real.cos (2 * Real.pi * t / T) := by
      let q := Real.sqrt (traceForm X X)
      have hq : 0 < q := Real.sqrt_pos.2 (traceForm_pos D X hx)
      let T := T₀ / q
      have hT : 0 < T := div_pos hT₀ hq
      have hlat (t : ℝ) : D.exp (t • X) = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ) := by
        have hsmul : (t * q) • normalizedDirection X = t • X := by
          rw [normalizedDirection, smul_smul, mul_assoc, mul_inv_cancel₀ hq.ne', mul_one]
        rw [← hsmul, normalized_period_eq D hx hX₀, hlat₀]
        exact exists_congr fun k => by
          dsimp [T]
          rw [div_mul_eq_mul_div, eq_div_iff hq.ne']
      have hDiag : H X X = 2 * Real.pi^2 / T^2 := by
        dsimp [H, T]
        change 2 * (Real.pi / T₀)^2 * traceForm X X = 2 * Real.pi^2 / (T₀ / q)^2
        have hq2 : q^2 = traceForm X X := Real.sq_sqrt (traceForm_pos D X hx).le
        rw [← hq2]
        field_simp [hq.ne', hT₀.ne']
      obtain ⟨S, hS, hlatS, hcos⟩ := ray_period_cosine D X hx
      have he : S = T := lattice_generator_unique hS hT
        (fun t => (hlatS t).symm.trans (hlat t))
      rw [he] at hcos
      exact ⟨T, hT, hlat, hDiag, hcos⟩
    refine ⟨H, hsym, hnonneg, fun X hx => ?_, fun t X => ?_⟩
    · obtain ⟨T, hT, hlat, hDiag, _⟩ := hlaws X hx
      exact ⟨T, hT, hlat, hDiag⟩
    · by_cases hx : X = 0
      · simp [hx, exp_zero D, (D.faithful 1).mpr rfl]
      · obtain ⟨T, hT, _, hDiag, hcos⟩ := hlaws X hx
        have hs : Real.sqrt (H X X / 2) = Real.pi / T := by
          rw [hDiag, show 2 * Real.pi^2 / T^2 / 2 = (Real.pi / T)^2 by ring,
            Real.sqrt_sq (by positivity)]
        rw [hs]
        have hf := hcos t
        rw [show 2 * Real.pi * t / T = 2 * (t * (Real.pi / T)) by ring,
          Real.cos_two_mul] at hf
        linarith
  · push Not at hL
    refine ⟨0, ⟨fun _ _ => rfl⟩, by simp, ?_, ?_⟩
    · intro X hX
      exact (hX (hL X)).elim
    · intro t X
      simp [hL X, exp_zero D, (D.faithful 1).mpr rfl]

open Asymptotics

private theorem comparison_expansion (D : ContinuousData L G)
    (H : LinearMap.BilinForm ℝ L) (hH : ∀ X, 0 ≤ H X X)
    (hcos : ∀ (t : ℝ) (X : L),
      D.phi (D.exp (t • X)) = Real.cos (t * Real.sqrt (H X X / 2))^2) :
    (fun X : L => D.phi (D.exp X) - (1 - H X X / 2))
      =o[𝓝 0] (fun X : L => ‖X‖^2) := by
  let u (X : L) := Real.sqrt (H X X / 2)
  have hu2 (X : L) : u X ^ 2 = H X X / 2 := Real.sq_sqrt (div_nonneg (hH X) (by norm_num))
  have hcont : Continuous u := by
    change Continuous fun X : L => Real.sqrt (H.toContinuousBilinearMap X X / 2)
    fun_prop
  have ht : Tendsto u (𝓝 0) (𝓝 0) := by
    have hz : u 0 = 0 := by simp [u]
    exact hz ▸ hcont.continuousAt (x := (0 : L))
  have hb : (fun X : L => u X ^ 2) =O[𝓝 0] (fun X : L => ‖X‖^2) := by
    apply IsBigO.of_bound (‖H.toContinuousBilinearMap‖ / 2)
    filter_upwards with X
    have hle := H.toContinuousBilinearMap.le_opNorm₂ X X
    rw [LinearMap.toContinuousBilinearMap_apply, Real.norm_eq_abs, abs_of_nonneg (hH X)] at hle
    rw [hu2, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hH X) (by norm_num)),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hg₀ := D5.S3.Analytic.Dilation.DuplicationQuadraticGerm.cosine_quadratic_germ 2
  have hg := ((hg₀.comp_tendsto ht).const_mul_left (1 / 2 : ℝ)).trans_isBigO hb
  apply hg.congr_left
  intro X
  have he := hcos 1 X
  rw [one_smul, one_mul] at he
  dsimp only [Function.comp_apply]
  rw [he, ← show u X = Real.sqrt (H X X / 2) from rfl,
    Real.cos_two_mul, ← hu2 X]
  ring

/-- Continuity on exponential curves suffices for the infinitesimal round-trip
classification, with the metric fixed by the least positive return times. -/
theorem comparison_classification_of_continuous_rays (D : ContinuousData L G) :
    ∃ H : LinearMap.BilinForm ℝ L, H.IsSymm ∧
      (∀ X : L, 0 ≤ H X X) ∧
      (∀ X : L, H X X = 0 → X = 0) ∧
      (∀ (t : ℝ) (X : L), D.phi (D.exp (t • X)) = Real.cos (t * Real.sqrt (H X X / 2))^2) ∧
      (∀ X : L, X ≠ 0 → ∃ T > 0,
        (∀ t : ℝ, D.exp (t • X) = 1 ↔ ∃ k : ℤ, t = T * (k : ℝ)) ∧
        H X X = 2 * Real.pi^2 / T^2) ∧
      (∀ (t : ℝ) (X : L),
        D.exp (t • X) = 1 ↔ ∃ n : ℤ, t * Real.sqrt (H X X / 2) = Real.pi * n) ∧
      (∀ X Y : L, ⁅X, Y⁆ = 0 → X = 0 ∨ ∃ c : ℝ, Y = c • X) ∧
      (∀ C X Y : L, H ⁅C, X⁆ Y + H X ⁅C, Y⁆ = 0) ∧
      (finrank ℝ L = 0 ∨ finrank ℝ L = 1 ∨ finrank ℝ L = 3) ∧
      (finrank ℝ L = 3 →
        ∃ (b : Basis (Fin 3) ℝ L) (μ : ℝ), 0 < μ ∧
          (∀ i j : Fin 3, H (b i) (b j) = if i = j then 1 else 0) ∧
          ⁅b 0, b 1⁆ = μ • b 2 ∧
          ⁅b 1, b 2⁆ = μ • b 0 ∧
          ⁅b 2, b 0⁆ = μ • b 1) := by
  obtain ⟨H, hsym, hnonneg, hlat, hcos⟩ := exists_period_metric D
  let d : Data L G :=
    { exp_mem := D.exp_mem
      conj_mem := D.conj_mem
      phi := D.phi
      h := H
      symmetric := hsym
      bounded := D.bounded
      faithful := D.faithful
      duplication := D.duplication
      conjugation := D.conjugation
      expansion := comparison_expansion D H hnonneg hcos }
  obtain ⟨_, hdef, _, hperiod, hcent, hinv, hdim, hframe⟩ :=
    RoundTripClassification.comparison_classification d
  exact ⟨H, hsym, hnonneg, hdef, hcos, hlat, hperiod, hcent, hinv, hdim, hframe⟩

end TraceForm

end
end D5.S3.Quantum.Algebra.Comparison.RoundTripPeriodMetric
