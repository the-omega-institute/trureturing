/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteBoundaryCover
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteBoundaryCover
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSpecialFiber]
   utility: none
   digest: Boundary limits of the compact trace graph admit six-dimensional observation covers. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSpecialFiber
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteOrdinaryTrace
import Mathlib.Analysis.Complex.RealDeriv

/-! Projective polynomial incidence persists on the compact graph. At a
base point it determines the exceptional amplitude plane. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteBoundaryCover

open Set Filter PeriodicMPSFiveSiteCompactSource PeriodicMPSFiveSiteCoordinates
  PeriodicMPSFiveSiteTraceChart PeriodicMPSFiveSiteAlignedFiber
  PeriodicMPSProjectiveCoordinates PeriodicMPSFiveSiteNormalization
open scoped Topology ComplexConjugate

open private traceRatio continuousAt_traceRatio
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactChart
open private projector_column alignedPencil alignedPencil_continuous quadrics
  pencil_incidence exists_rep
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSpecialFiber
open private traceDirection pencil
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCompactSource

noncomputable section

private def alignedAmplitude (p : Ambient) (k : Fin 8) : Fin 8 → ℂ :=
  shear (-traceRatio p) (fun i => p.2 i k)

private theorem alignedAmplitude_continuousAt {p : Ambient} (ht : p.1.1 0 0 ≠ 0) (k : Fin 8) :
    ContinuousAt (fun q => alignedAmplitude q k) p := by
  have ht' := continuousAt_traceRatio ht
  apply continuousAt_pi.mpr
  intro i
  fin_cases i <;> simp [alignedAmplitude, shear] <;> fun_prop

set_option maxHeartbeats 900000 in
-- The normalized trace and pencil representatives are obtained from fixed projective columns.
private theorem ordinary_aligned_values (u : Inputs) (ht : (ordinary u).1.1 0 0 ≠ 0)
    (j : Fin 6) (k : Fin 8) :
    ∃ (v : Fin 4 → ℂ) (c g : ℂ),
      alignedPencil (ordinary u) j = c • v ∧ alignedAmplitude (ordinary u) k = g • quadrics v := by
  let t := u.val 0
  let s := u.val 1 / t
  let d := u.val 2
  let m := t * u.val 1 - u.val 4
  let z := m - 2 * s * d
  let w := u.val 3 - s * z - s ^ 2 * d
  let v : Fin 4 → ℂ := ![3 * d - t ^ 2, 2 * d - t ^ 2, z, w]
  let a := coordinates t (u.val 1) d (u.val 3) (u.val 4)
  let c : ℂ := ↑((PeriodicMPSProjectiveCoordinates.mass (pencil u.val))⁻¹) * conj (pencil u.val j)
  let g : ℂ := ↑((PeriodicMPSProjectiveCoordinates.mass a)⁻¹) * conj (a k)
  have htn : t ≠ 0 := (projector_diag_ne_zero_iff (traceDirection u.val) 0).mp ht
  have htr : traceRatio (ordinary u) = s := projector_ratio (traceDirection u.val) 1 0 htn
  have hs : t * s = u.val 1 := mul_div_cancel₀ _ htn
  refine ⟨v, c, g * t, ?_, ?_⟩
  · unfold alignedPencil
    rw [htr]
    have hc := projector_column (pencil u.val) j
    have hentry (i : Fin 6) : (ordinary u).1.2 i j = c * pencil u.val i := congrFun hc i
    simp only [hentry]
    funext i
    fin_cases i <;>
      simp [v, pencil, d, m, t, z, w, Pi.smul_apply, smul_eq_mul, pow_two] <;> ring
  · have ha : a = t • chart s (3 * d - t ^ 2) (2 * d - t ^ 2) z w := by
      have h := frame_trace_coordinates t 1 s d m (u.val 3)
      have he : t ^ 2 * s - m = u.val 4 := by
        dsimp only [m]
        rw [pow_two, mul_assoc, hs]
        ring
      have hm : z + 2 * s * d = m := by dsimp only [z]; ring
      have hw : w + s * z + s ^ 2 * d = u.val 3 := by dsimp only [w]; ring
      simp only [mul_one, hs, he] at h
      have hf := frame_first_chart s (t ^ 2) d z w
      rw [hm, hw] at hf
      rwa [hf] at h
    unfold alignedAmplitude
    rw [htr]
    change shear (-s) (fun i => projector a i k) = _
    rw [projector_column, shear_smul, show shear (-s) a = t • quadrics v by
      rw [ha, shear_smul, chart, shear_add, neg_add_cancel, shear_zero]
      rfl, smul_smul]

private theorem compact_equation {p : Ambient} (hp : p ∈ source) (ht : p.1.1 0 0 ≠ 0)
    (j : Fin 6) (k : Fin 8) (F : (Fin 4 → ℂ) × (Fin 8 → ℂ) → ℂ) (hF : Continuous F)
    (hzero : ∀ (v : Fin 4 → ℂ) (c g : ℂ), F (c • v, g • quadrics v) = 0) :
    F (alignedPencil p j, alignedAmplitude p k) = 0 := by
  haveI : NeBot (𝓝[range ordinary] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have ht' : ∀ᶠ q : Ambient in 𝓝[range ordinary] p, q.1.1 0 0 ≠ 0 :=
    nhdsWithin_le_nhds ((show ContinuousAt (fun q : Ambient => q.1.1 0 0) p by fun_prop)
      (isOpen_ne.mem_nhds ht))
  let G : Ambient → ℂ := fun q => F (alignedPencil q j, alignedAmplitude q k)
  have hG : ContinuousAt G p := hF.continuousAt.comp
    ((alignedPencil_continuous ht j).prodMk (alignedAmplitude_continuousAt ht k))
  have he : G =ᶠ[𝓝[range ordinary] p] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin, ht'] with q hq hqt
    obtain ⟨u, rfl⟩ := hq
    obtain ⟨v, c, g, hpencil, hamp⟩ := ordinary_aligned_values u hqt j k
    dsimp only [G]
    rw [hpencil, hamp, hzero]
  exact tendsto_nhds_unique hG.continuousWithinAt (tendsto_const_nhds.congr' he.symm)

private theorem continuous_quadrics : Continuous quadrics := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [quadrics, aligned] <;> fun_prop

private theorem quadrics_scale (v : Fin 4 → ℂ) (c : ℂ) :
    quadrics (c • v) = c ^ 2 • quadrics v := by
  funext i
  fin_cases i <;> simp [quadrics, aligned, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem compact_proportional {p : Ambient} (hp : p ∈ source) (ht : p.1.1 0 0 ≠ 0)
    (j : Fin 6) (k i l : Fin 8) :
    quadrics (alignedPencil p j) i * alignedAmplitude p k l =
      quadrics (alignedPencil p j) l * alignedAmplitude p k i := by
  have hq (n : Fin 8) : Continuous (fun v : Fin 4 → ℂ => quadrics v n) :=
    continuous_pi_iff.mp continuous_quadrics n
  refine sub_eq_zero.mp (compact_equation hp ht j k
    (fun q => quadrics q.1 i * q.2 l - quadrics q.1 l * q.2 i) (by fun_prop) ?_)
  intro v c g
  rw [show (c • v, g • quadrics v).1 = c • v from rfl, quadrics_scale]
  simp [Pi.smul_apply, smul_eq_mul]
  ring

private theorem compact_exceptional_equations {p : Ambient} (hp : p ∈ source)
    (ht : p.1.1 0 0 ≠ 0) (j : Fin 6) (k : Fin 8) :
    let v := alignedPencil p j
    let f := alignedAmplitude p k
    v 0 * v 1 * f 3 = v 0 * v 2 * f 1 + v 1 * (v 1 - v 0) * f 2 ∧
    v 1 * f 4 = v 3 * f 1 ∧ f 5 = f 4 ∧ v 0 * f 6 = v 3 * f 2 ∧ f 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine sub_eq_zero.mp (compact_equation hp ht j k
      (fun q => q.1 0 * q.1 1 * q.2 3 - (q.1 0 * q.1 2 * q.2 1 +
        q.1 1 * (q.1 1 - q.1 0) * q.2 2)) (by fun_prop) ?_)
    intro v c g
    simp [quadrics, aligned, Pi.smul_apply, smul_eq_mul]
    ring
  · refine sub_eq_zero.mp (compact_equation hp ht j k
      (fun q => q.1 1 * q.2 4 - q.1 3 * q.2 1) (by fun_prop) ?_)
    intro v c g
    simp [quadrics, aligned, Pi.smul_apply, smul_eq_mul]
    ring
  · refine sub_eq_zero.mp (compact_equation hp ht j k
      (fun q => q.2 5 - q.2 4) (by fun_prop) ?_)
    intro v c g
    simp [quadrics, aligned, Pi.smul_apply]
  · refine sub_eq_zero.mp (compact_equation hp ht j k
      (fun q => q.1 0 * q.2 6 - q.1 3 * q.2 2) (by fun_prop) ?_)
    intro v c g
    simp [quadrics, aligned, Pi.smul_apply, smul_eq_mul]
    ring
  · refine compact_equation hp ht j k (fun q => q.2 7) (by fun_prop) ?_
    intro v c g
    simp [quadrics, aligned, Pi.smul_apply]

private theorem projector_of_column {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ}
    (hP : P ∈ projective) (i : ι) (hi : P i i ≠ 0) :
    P = projector (fun j => P j i) := by
  obtain ⟨q, hq, rfl⟩ := exists_rep hP
  have hqi := (projector_diag_ne_zero_iff q i).mp hi
  rw [projector_column, projector_scale _]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero (mass_pos _ hq).ne'))
    ((map_ne_zero (starRingEnd ℂ)).2 hqi)

private theorem exists_diagonal_ne_zero {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ}
    (hP : P ∈ projective) : ∃ i, P i i ≠ 0 := by
  obtain ⟨q, hq, rfl⟩ := exists_rep hP
  apply not_forall_not.mp
  intro h
  apply hq
  funext i
  by_contra hi
  exact h i ((projector_diag_ne_zero_iff q i).mpr hi)

private theorem shear_neg_left (s : ℂ) (f : Fin 8 → ℂ) :
    shear s (shear (-s) f) = f := by
  rw [shear_add, add_neg_cancel, shear_zero]

private theorem shear_ne_zero {s : ℂ} {f : Fin 8 → ℂ} (hf : f ≠ 0) : shear s f ≠ 0 := by
  intro h
  have hz : shear (-s) (0 : Fin 8 → ℂ) = 0 := by
    funext i
    fin_cases i <;> simp [shear]
  exact hf (by simpa [shear_add, hz] using congrArg (shear (-s)) h)

private theorem amp_of_column {p : Ambient} (hp : p ∈ source) (k : Fin 8)
    (hk : p.2 k k ≠ 0) :
    alignedAmplitude p k ≠ 0 ∧ p.2 = projector (shear (traceRatio p) (alignedAmplitude p k)) := by
  have hn : (fun i => p.2 i k) ≠ 0 := fun e => hk (congrFun e k)
  refine ⟨shear_ne_zero hn, ?_⟩
  rw [alignedAmplitude, shear_neg_left]
  exact projector_of_column (source_amplitude_projective hp) k hk

private theorem quadrics_nonzero_lift {p : Ambient} (hp : p ∈ source) (ht : p.1.1 0 0 ≠ 0)
    (j : Fin 6) (hv : quadrics (alignedPencil p j) ≠ 0) :
    p.2 = projector (shear (traceRatio p) (quadrics (alignedPencil p j))) := by
  obtain ⟨k, hk⟩ := exists_diagonal_ne_zero (source_amplitude_projective hp)
  let q := quadrics (alignedPencil p j)
  let f := alignedAmplitude p k
  obtain ⟨hf, hP⟩ := amp_of_column hp k hk
  obtain ⟨l, hl⟩ : ∃ l, q l ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have hf' : f l ≠ 0 := by
    intro h
    apply hf
    funext i
    have h' : q i * f l = q l * f i := compact_proportional hp ht j k i l
    rw [h, mul_zero] at h'
    exact (mul_eq_zero.mp h'.symm).resolve_left hl
  let c := f l / q l
  have hc : c ≠ 0 := div_ne_zero hf' hl
  have he : f = c • q := by
    funext i
    have h : q i * f l = q l * f i := compact_proportional hp ht j k i l
    change f i = f l / q l * q i
    rw [div_mul_eq_mul_div, eq_div_iff hl]
    simpa only [mul_comm] using h.symm
  rw [hP]
  change projector (shear (traceRatio p) f) = projector (shear (traceRatio p) q)
  rw [he, shear_smul, projector_scale _ hc]

private theorem pencil_nonzero_aligned {p : Ambient} (hp : p ∈ source) (ht : p.1.1 0 0 ≠ 0)
    (j : Fin 6) (hj : p.1.2 j j ≠ 0) :
    alignedPencil p j ≠ 0 := by
  intro hz
  let D : Fin 6 → ℂ := fun i => p.1.2 i j
  let s := traceRatio p
  have h0 : 3 * D 3 - D 0 = 0 := congrFun hz 0
  have h1 : 2 * D 3 - D 0 = 0 := congrFun hz 1
  have hd : D 3 = 0 := by linear_combination h0 - h1
  have ha : D 0 = 0 := by linear_combination 3 * hd - h0
  have hm : D 4 - 2 * s * D 3 = 0 := congrFun hz 2
  have hm' : D 4 = 0 := by simpa [hd] using hm
  have he : D 5 - s * (D 4 - 2 * s * D 3) - s ^ 2 * D 3 = 0 := congrFun hz 3
  have he' : D 5 = 0 := by simpa [hd, hm'] using he
  have h01 := pencil_incidence hp j 1 0 (fun v => by simp [pencil]; ring)
  change p.1.1 0 0 * D 1 = p.1.1 1 0 * D 0 at h01
  rw [ha, mul_zero] at h01
  have hD₁ : D 1 = 0 := (mul_eq_zero.mp h01).resolve_left ht
  have h12 := pencil_incidence hp j 2 1 (fun v => by simp [pencil]; ring)
  change p.1.1 0 0 * D 2 = p.1.1 1 0 * D 1 at h12
  rw [hD₁, mul_zero] at h12
  have hD₂ : D 2 = 0 := (mul_eq_zero.mp h12).resolve_left ht
  exact hj (show D j = 0 by fin_cases j <;> assumption)

set_option maxHeartbeats 1000000 in
-- Kernel reduction checks the eight explicit coordinates of the exceptional vector.
private theorem exceptional_lift {p : Ambient} (hp : p ∈ source) (ht : p.1.1 0 0 ≠ 0)
    (j : Fin 6) (hj : p.1.2 j j ≠ 0) (hbase : quadrics (alignedPencil p j) = 0) :
    ∃ (r : ℂ) (v : Fin 3 → ℂ), -r ^ 2 + 3 * r - 1 = 0 ∧ v ≠ 0 ∧
      p.2 = projector (shear (traceRatio p) (exceptional r (v 0) (v 1) (v 2))) := by
  let q := alignedPencil p j
  let x := q 0
  let y := q 1
  obtain ⟨hw, hz, hxy⟩ := (aligned_eq_zero_iff _ _ _ _).mp hbase
  change q 3 = 0 at hw
  change q 2 = 0 at hz
  change -x ^ 2 + 3 * x * y - y ^ 2 = 0 at hxy
  have hq : q ≠ 0 := pencil_nonzero_aligned hp ht j hj
  have hx : x ≠ 0 := by
    intro h
    have hy : y = 0 := sq_eq_zero_iff.mp (by simpa [h] using hxy)
    apply hq
    funext i
    fin_cases i <;> assumption
  have hy : y ≠ 0 := by
    intro h
    exact hx (sq_eq_zero_iff.mp (by simpa [h] using hxy))
  let r := x / y
  have hr : -r ^ 2 + 3 * r - 1 = 0 := by
    dsimp only [r]
    field_simp
    linear_combination hxy
  have hr₀ : r ≠ 0 := div_ne_zero hx hy
  have hr₁ : 3 - 2 * r ≠ 0 := by
    intro h
    have he : (5 : ℂ) = 0 := by linear_combination 4 * hr + (3 - 2 * r) * h
    norm_num at he
  obtain ⟨k, hk⟩ := exists_diagonal_ne_zero (source_amplitude_projective hp)
  let f := alignedAmplitude p k
  obtain ⟨hf, hP⟩ := amp_of_column hp k hk
  obtain ⟨h₃, h₄, h₅, h₆, h₇⟩ := compact_exceptional_equations hp ht j k
  change f ≠ 0 at hf
  change f 7 = 0 at h₇
  change x * y * f 3 = x * q 2 * f 1 + y * (y - x) * f 2 at h₃
  change y * f 4 = q 3 * f 1 at h₄
  change x * f 6 = q 3 * f 2 at h₆
  have hrxy : r * y = x := div_mul_cancel₀ _ hy
  have hf₃ : f 3 = (1 - r) * (f 2 / r) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hr₀).mpr
    apply (mul_left_cancel₀ (pow_ne_zero 2 hy))
    rw [hz, mul_zero, zero_mul, zero_add] at h₃
    linear_combination h₃ + y * (f 3 + f 2) * hrxy
  have hf₄ : f 4 = 0 := by
    rw [hw, zero_mul] at h₄
    exact (mul_eq_zero.mp h₄).resolve_left hy
  have hf₅ : f 5 = 0 := h₅.trans hf₄
  have hf₆ : f 6 = 0 := by
    rw [hw, zero_mul] at h₆
    exact (mul_eq_zero.mp h₆).resolve_left hx
  let v : Fin 3 → ℂ := ![f 0 / (3 - 2 * r), f 1, f 2 / r]
  have hF : f = exceptional r (v 0) (v 1) (v 2) := by
    funext i
    fin_cases i <;> simp [v, exceptional, mul_div_cancel₀, hr₀, hr₁, hf₃, hf₄, hf₅, hf₆, h₇]
  have hv : v ≠ 0 := by
    intro h
    apply hf
    rw [hF, h]
    funext i
    fin_cases i <;> simp [exceptional]
  exact ⟨r, v, hr, hv, hP.trans (congrArg (fun a => projector (shear (traceRatio p) a)) hF)⟩

private def traceFlip : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def pencilFlip : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 0, 5, 4, 3]
  invFun := ![2, 1, 0, 5, 4, 3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def amplitudeFlip : Equiv.Perm (Fin 8) where
  toFun := ![7, 6, 4, 5, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 2, 3, 1, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem projector_comp {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) (v : ι → ℂ) :
    projector (v ∘ e) = (projector v).submatrix e e := by
  have hm : PeriodicMPSProjectiveCoordinates.mass (v ∘ e) =
      PeriodicMPSProjectiveCoordinates.mass v :=
    Equiv.sum_comp e (fun i => Complex.normSq (v i))
  ext i j
  simp [projector, hm, outer, Matrix.smul_apply, Matrix.submatrix_apply]

private def flip (p : Ambient) : Ambient :=
  ((p.1.1.submatrix traceFlip traceFlip, p.1.2.submatrix pencilFlip pencilFlip),
    p.2.submatrix amplitudeFlip amplitudeFlip)

private theorem flip_flip (p : Ambient) : flip (flip p) = p := by
  have hT (i : Fin 2) : traceFlip (traceFlip i) = i := traceFlip.left_inv i
  have hD (i : Fin 6) : pencilFlip (pencilFlip i) = i := pencilFlip.left_inv i
  have hP (i : Fin 8) : amplitudeFlip (amplitudeFlip i) = i := amplitudeFlip.left_inv i
  apply Prod.ext
  · apply Prod.ext <;> ext i j <;> simp [flip, Matrix.submatrix_apply, hT, hD]
  · ext i j
    simp [flip, Matrix.submatrix_apply, hP]

private theorem coordinates_flip (t s d e k : ℂ) :
    coordinates s t e d k = coordinates t s d e k ∘ amplitudeFlip := by
  funext i
  fin_cases i <;> simp [coordinates, amplitudeFlip] <;> ring

private theorem flip_source {p : Ambient} (hp : p ∈ source) : flip p ∈ source := by
  have hf : Continuous flip := by
    unfold flip
    refine (Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_)
    all_goals apply continuous_pi; intro i; apply continuous_pi; intro j
    all_goals simp only [Matrix.submatrix_apply]; fun_prop
  apply closure_mono _ (image_closure_subset_closure_image hf ⟨p, hp, rfl⟩)
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  let v : Fin 5 → ℂ := ![u.val 1, u.val 0, u.val 3, u.val 2, u.val 4]
  have hc : coordinates (v 0) (v 1) (v 2) (v 3) (v 4) =
      coordinates (u.val 0) (u.val 1) (u.val 2) (u.val 3) (u.val 4) ∘ amplitudeFlip :=
    coordinates_flip _ _ _ _ _
  have hv : coordinates (v 0) (v 1) (v 2) (v 3) (v 4) ≠ 0 := by
    rw [hc]
    intro h
    apply u.property
    funext i
    simpa using congrFun h (amplitudeFlip.symm i)
  have ht : traceDirection v = traceDirection u.val ∘ traceFlip := by
    funext i
    fin_cases i <;> rfl
  have hd : pencil v = pencil u.val ∘ pencilFlip := by
    funext i
    fin_cases i <;> simp [v, pencil, pencilFlip, mul_comm]
  exact ⟨⟨v, hv⟩, by simp [ordinary, flip, ht, hd, hc, projector_comp]⟩

private theorem flip_traceRatio_zero {p : Ambient} (hp : p ∈ source) (ht : p.1.1 0 0 = 0) :
    (flip p).1.1 0 0 ≠ 0 ∧ traceRatio (flip p) = 0 := by
  obtain ⟨t, htn, hP⟩ := exists_rep (source_subset_projective hp).1.1
  have ht₀ : t 0 = 0 := by
    by_contra h
    exact ((projector_diag_ne_zero_iff t 0).mpr h) (hP.symm ▸ ht)
  have ht₁ : t 1 ≠ 0 := by
    intro h
    exact htn (funext (fun i => by fin_cases i <;> assumption))
  constructor
  · change p.1.1 1 1 ≠ 0
    rw [hP, projector_diag_ne_zero_iff]
    exact ht₁
  · change p.1.1 0 1 / p.1.1 1 1 = 0
    rw [hP, projector_ratio _ _ _ ht₁, ht₀, zero_div]

private theorem frame_scale (s c a d m e : ℂ) :
    frame 1 s (c * a) (c * d) (c * m) (c * e) = c ^ 2 • frame 1 s a d m e := by
  funext i
  fin_cases i <;> simp [frame, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem frame_of_pencil (p : Ambient) (j : Fin 6) :
    shear (traceRatio p) (quadrics (alignedPencil p j)) =
      frame 1 (traceRatio p) (p.1.2 0 j) (p.1.2 3 j) (p.1.2 4 j) (p.1.2 5 j) := by
  let s := traceRatio p
  let d := p.1.2 3 j
  let z := p.1.2 4 j - 2 * s * d
  let w := p.1.2 5 j - s * z - s ^ 2 * d
  have hz : z + 2 * s * d = p.1.2 4 j := by dsimp [z]; ring
  have hw : w + s * z + s ^ 2 * d = p.1.2 5 j := by dsimp [w]; ring
  have he := frame_first_chart s (p.1.2 0 j) d z w
  rw [hz, hw] at he
  exact he.symm

private theorem zero_squared_trace_column {p : Ambient} (hp : p ∈ source)
    (h : p.1.2 0 0 = 0) (j : Fin 6) : p.1.2 0 j = 0 := by
  obtain ⟨v, hv, hP⟩ := exists_rep (source_subset_projective hp).1.2
  have hv₀ : v 0 = 0 := by
    by_contra hn
    exact ((projector_diag_ne_zero_iff v 0).mpr hn) (hP.symm ▸ h)
  simp [hP, projector, outer, hv₀, Matrix.smul_apply]

private theorem nonzero_determinant_pencil {p : Ambient} (hp : p ∈ source)
    (ht : p.1.1 0 0 ≠ 0) (h : p.1.2 0 0 = 0) (j : Fin 6) (hj : p.1.2 j j ≠ 0) :
    (![p.1.2 3 j, p.1.2 4 j, p.1.2 5 j] : Fin 3 → ℂ) ≠ 0 := by
  intro hz
  apply pencil_nonzero_aligned hp ht j hj
  have h₀ := zero_squared_trace_column hp h j
  have h₃ : p.1.2 3 j = 0 := congrFun hz 0
  have h₄ : p.1.2 4 j = 0 := congrFun hz 1
  have h₅ : p.1.2 5 j = 0 := congrFun hz 2
  simp [alignedPencil, h₀, h₃, h₄, h₅]

private theorem outside_chart_base {p : Ambient}
    (ht : p.1.1 0 0 ≠ 0) (hd : p.1.2 0 0 ≠ 0)
    (hb : p ∉ PeriodicMPSFiveSiteOrdinaryTrace.chartDomain) :
    quadrics (alignedPencil p 0) = 0 := by
  let d := p.1.2 0 0
  let q := PeriodicMPSFiveSiteOrdinaryTrace.decode p
  have hA : PeriodicMPSFiveSiteOrdinaryTrace.amplitude q = 0 := by
    by_contra h
    exact hb ⟨ht, hd, h⟩
  have hq₁ : d * q 1 = p.1.2 3 0 := mul_div_cancel₀ _ hd
  have hq₂ : d * q 2 = p.1.2 4 0 := mul_div_cancel₀ _ hd
  have hq₃ : d * q 3 = p.1.2 5 0 := mul_div_cancel₀ _ hd
  have he := frame_scale (traceRatio p) d 1 (q 1) (q 2) (q 3)
  rw [mul_one, hq₁, hq₂, hq₃] at he
  change frame 1 (traceRatio p) d (p.1.2 3 0) (p.1.2 4 0) (p.1.2 5 0) =
    d ^ 2 • PeriodicMPSFiveSiteOrdinaryTrace.amplitude q at he
  by_contra hn
  exact shear_ne_zero hn (by rw [frame_of_pencil, he, hA, smul_zero])

private def patch {n : ℕ} (j : Fin (n + 1)) (q : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) j 1 q

private theorem projective_patch {n : ℕ} {v : Fin (n + 1) → ℂ} (hv : v ≠ 0) :
    ∃ (j : Fin (n + 1)) (q : Fin n → ℂ) (c : ℂ), c ≠ 0 ∧ v = c • patch j q := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let q := fun i => v (j.succAbove i) / v j
  refine ⟨j, q, v j, hj, ?_⟩
  funext i
  by_cases h : i = j
  · subst i
    simp [patch, Pi.smul_apply, smul_eq_mul]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    simp [patch, q, Pi.smul_apply, smul_eq_mul, mul_div_cancel₀ _ hj]

private def baseRoot (b : Bool) : ℂ :=
  (3 + (if b then (Real.sqrt 5 : ℂ) else -(Real.sqrt 5 : ℂ))) / 2

private theorem eq_baseRoot (r : ℂ) (hr : -r ^ 2 + 3 * r - 1 = 0) :
    ∃ b : Bool, r = baseRoot b := by
  have hs : (Real.sqrt 5 : ℂ) ^ 2 = (5 : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num))
  have hf : (2 * r - 3 - (Real.sqrt 5 : ℂ)) * (2 * r - 3 + (Real.sqrt 5 : ℂ)) = 0 := by
    linear_combination -4 * hr - hs
  rcases mul_eq_zero.mp hf with h | h
  · refine ⟨true, ?_⟩
    simp only [baseRoot, ite_true]
    linear_combination (1 / 2 : ℂ) * h
  · refine ⟨false, ?_⟩
    simp only [baseRoot, Bool.false_eq_true, ite_false]
    linear_combination (1 / 2 : ℂ) * h

private theorem exceptional_scale (r c : ℂ) (v : Fin 3 → ℂ) :
    exceptional r ((c • v) 0) ((c • v) 1) ((c • v) 2) =
      c • exceptional r (v 0) (v 1) (v 2) := by
  funext i
  fin_cases i <;> simp [exceptional, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The index specifies a projective chart in one of the boundary families. -/
abbrev BoundaryFamily := Fin 4 ⊕ (Fin 3 ⊕ (Bool × Bool × Fin 3))

private def twoTail (q : Fin 3 → ℂ) : Fin 2 → ℂ := fun i => q i.succ

private def boundaryAmplitude : BoundaryFamily → (Fin 3 → ℂ) → Fin 8 → ℂ
  | .inl j, q => quadrics (patch j q) ∘ amplitudeFlip
  | .inr (.inl j), q =>
    let v := patch j (twoTail q)
    frame 1 (q 0) 0 (v 0) (v 1) (v 2)
  | .inr (.inr (flipped, b, j)), q =>
    let v := patch j (twoTail q)
    let a := shear (q 0) (exceptional (baseRoot b) (v 0) (v 1) (v 2))
    if flipped then a ∘ amplitudeFlip else a

private theorem boundary_flip_amplitude {p : Ambient} {v : Fin 8 → ℂ}
    (h : (flip p).2 = projector v) : p.2 = projector (v ∘ amplitudeFlip) := by
  rw [projector_comp, ← h]
  exact (congrArg Prod.snd (flip_flip p)).symm

private theorem exceptional_family {p : Ambient} (hp : p ∈ source)
    (ht : p.1.1 0 0 ≠ 0) (j : Fin 6) (hj : p.1.2 j j ≠ 0)
    (hbase : quadrics (alignedPencil p j) = 0) :
    ∃ (b : Bool) (i : Fin 3) (q : Fin 3 → ℂ),
      p.2 = projector (boundaryAmplitude (.inr (.inr (false, b, i))) q) ∧
      boundaryAmplitude (.inr (.inr (false, b, i))) q ≠ 0 := by
  obtain ⟨r, v, hr, hv, hP⟩ := exceptional_lift hp ht j hj hbase
  obtain ⟨b, rfl⟩ := eq_baseRoot r hr
  obtain ⟨i, u, c, hc, hV⟩ := projective_patch hv
  let q : Fin 3 → ℂ := ![traceRatio p, u 0, u 1]
  have ht' : twoTail q = u := by
    funext i
    fin_cases i <;> rfl
  have hn : exceptional (baseRoot b) (v 0) (v 1) (v 2) ≠ 0 := by
    obtain ⟨k, hk⟩ := exists_diagonal_ne_zero (source_amplitude_projective hp)
    intro h
    rw [hP, h] at hk
    have hzero : shear (traceRatio p) (0 : Fin 8 → ℂ) = 0 := by
      funext i
      fin_cases i <;> simp [shear]
    exact hk (by simp [hzero, projector, outer, Matrix.smul_apply])
  refine ⟨b, i, q, ?_, ?_⟩
  · rw [hP, hV, exceptional_scale, shear_smul, projector_scale _ hc]
    simp [boundaryAmplitude, ht', q]
  · intro h
    apply shear_ne_zero (s := traceRatio p) hn
    rw [hV, exceptional_scale, shear_smul]
    have : shear (traceRatio p)
        (exceptional (baseRoot b) (patch i u 0) (patch i u 1) (patch i u 2)) = 0 := by
      simpa [boundaryAmplitude, ht', q] using h
    rw [this, smul_zero]

private theorem flip_vector_ne_zero {v : Fin 8 → ℂ} (hv : v ≠ 0) :
    v ∘ amplitudeFlip ≠ 0 := by
  intro h
  apply hv
  funext i
  simpa using congrFun h (amplitudeFlip.symm i)

private theorem boundary_amplitude_cover {p : Ambient} (hp : p ∈ source)
    (hb : p ∉ PeriodicMPSFiveSiteOrdinaryTrace.chartDomain) :
    ∃ (i : BoundaryFamily) (q : Fin 3 → ℂ), boundaryAmplitude i q ≠ 0 ∧
      p.2 = projector (boundaryAmplitude i q) := by
  by_cases ht : p.1.1 0 0 = 0
  · let p' := flip p
    have hp' : p' ∈ source := flip_source hp
    obtain ⟨ht', hs⟩ := flip_traceRatio_zero hp ht
    obtain ⟨j, hj⟩ := exists_diagonal_ne_zero (source_subset_projective hp').1.2
    let v := alignedPencil p' j
    by_cases hv : quadrics v = 0
    · obtain ⟨b, i, q, he, hn⟩ := exceptional_family hp' ht' j hj hv
      have hflip := boundary_flip_amplitude (p := p) he
      exact ⟨.inr (.inr (true, b, i)), q, flip_vector_ne_zero hn, hflip⟩
    · obtain ⟨i, q, c, hc, hV⟩ := projective_patch (pencil_nonzero_aligned hp' ht' j hj)
      have hql : quadrics (patch i q) ≠ 0 := by
        intro h
        exact hv (by rw [show v = alignedPencil p' j by rfl, hV, quadrics_scale, h, smul_zero])
      have he := quadrics_nonzero_lift hp' ht' j hv
      rw [hs, shear_zero, hV, quadrics_scale, projector_scale _ (pow_ne_zero 2 hc)] at he
      exact ⟨.inl i, q, flip_vector_ne_zero hql, boundary_flip_amplitude he⟩
  · by_cases hd : p.1.2 0 0 = 0
    · obtain ⟨j, hj⟩ := exists_diagonal_ne_zero (source_subset_projective hp).1.2
      by_cases hz : quadrics (alignedPencil p j) = 0
      · obtain ⟨b, i, q, he, hn⟩ := exceptional_family hp ht j hj hz
        exact ⟨.inr (.inr (false, b, i)), q, hn, he⟩
      · let v : Fin 3 → ℂ := ![p.1.2 3 j, p.1.2 4 j, p.1.2 5 j]
        obtain ⟨i, q, c, hc, hV⟩ := projective_patch (nonzero_determinant_pencil hp ht hd j hj)
        let u : Fin 3 → ℂ := ![traceRatio p, q 0, q 1]
        have hu : twoTail u = q := by
          funext k
          fin_cases k <;> rfl
        let w := patch i q
        change v = c • w at hV
        have hframe : shear (traceRatio p) (quadrics (alignedPencil p j)) =
            c ^ 2 • boundaryAmplitude (.inr (.inl i)) u := by
          rw [frame_of_pencil, zero_squared_trace_column hp hd]
          simp only [boundaryAmplitude, hu]
          change frame 1 (traceRatio p) 0 (v 0) (v 1) (v 2) =
            c ^ 2 • frame 1 (traceRatio p) 0 (w 0) (w 1) (w 2)
          rw [hV]
          simpa only [Pi.smul_apply, smul_eq_mul, mul_zero] using
            frame_scale (traceRatio p) c 0 (w 0) (w 1) (w 2)
        have hn : boundaryAmplitude (.inr (.inl i)) u ≠ 0 := by
          intro h
          exact shear_ne_zero hz (by rw [hframe, h, smul_zero])
        refine ⟨.inr (.inl i), u, hn, ?_⟩
        rw [quadrics_nonzero_lift hp ht j hz, hframe, projector_scale _ (pow_ne_zero 2 hc)]
    · obtain ⟨b, i, q, he, hn⟩ := exceptional_family hp ht 0 hd (outside_chart_base ht hd hb)
      exact ⟨.inr (.inr (false, b, i)), q, hn, he⟩

private theorem differentiable_patch {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (j : Fin (n + 1)) (v : E → Fin n → ℂ)
    (hv : Differentiable ℝ v) :
    Differentiable ℝ (fun q => patch j (v q)) := by
  apply differentiable_pi.mpr
  intro i
  by_cases h : i = j
  · subst i
    simp [patch]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    simpa only [patch, Fin.insertNth_apply_succAbove] using (differentiable_pi.mp hv k)

private theorem differentiable_boundaryAmplitude (i : BoundaryFamily) :
    Differentiable ℝ (boundaryAmplitude i) := by
  rcases i with j | j | ⟨flipped, b, j⟩
  · have hv := differentiable_patch j (fun q : Fin 3 → ℂ => q) differentiable_id
    have h (k : Fin 4) : Differentiable ℝ (fun q : Fin 3 → ℂ => patch j q k) :=
      differentiable_pi.mp hv k
    apply differentiable_pi.mpr
    intro k
    change Differentiable ℝ (fun q : Fin 3 → ℂ => quadrics (patch j q) (amplitudeFlip k))
    generalize amplitudeFlip k = l
    fin_cases l <;> simp [quadrics, aligned] <;> fun_prop
  · have hv := differentiable_patch j twoTail (by
      apply differentiable_pi.mpr
      intro n
      exact (ContinuousLinearMap.proj n.succ : (Fin 3 → ℂ) →L[ℝ] ℂ).differentiable)
    have h (k : Fin 3) : Differentiable ℝ
        (fun q : Fin 3 → ℂ => patch j (twoTail q) k) := differentiable_pi.mp hv k
    apply differentiable_pi.mpr
    intro k
    fin_cases k <;> simp [boundaryAmplitude, frame] <;> fun_prop
  · have hv := differentiable_patch j twoTail (by
      apply differentiable_pi.mpr
      intro n
      exact (ContinuousLinearMap.proj n.succ : (Fin 3 → ℂ) →L[ℝ] ℂ).differentiable)
    have h (k : Fin 3) : Differentiable ℝ
        (fun q : Fin 3 → ℂ => patch j (twoTail q) k) := differentiable_pi.mp hv k
    have ha : Differentiable ℝ (fun q : Fin 3 → ℂ =>
        let v := patch j (twoTail q)
        shear (q 0) (exceptional (baseRoot b) (v 0) (v 1) (v 2))) := by
      apply differentiable_pi.mpr
      intro k
      fin_cases k <;> simp [shear, exceptional] <;> fun_prop
    cases flipped
    · exact ha
    · exact differentiable_pi.mpr fun k => differentiable_pi.mp ha (amplitudeFlip k)

private theorem differentiable_normalizedGram {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → Fin 8 → ℂ) (hf : Differentiable ℝ f) :
    DifferentiableOn ℝ (fun q => normalizedGram (f q)) {q | f q ≠ 0} := by
  have hf' (i : Fin 4) (j : Fin 8) :
      Differentiable ℝ (fun q => flatten (f q) i j) := by
    fin_cases i <;> fin_cases j <;> exact differentiable_pi.mp hf _
  have hg (i j : Fin 4) : Differentiable ℝ (fun q => PeriodicMPSFiveSiteSpecialFiber.gram (f q) i j) := by
    let a (k : Fin 8) (q : E) := flatten (f q) i k * conj (flatten (f q) j k)
    have hd : Differentiable ℝ (∑ k, a k) := Differentiable.sum fun k _ =>
      (hf' i k).mul (Complex.differentiable_conj.comp (hf' j k))
    have he : (∑ k, a k) = fun q => PeriodicMPSFiveSiteSpecialFiber.gram (f q) i j := by
      funext q
      simp [a, Finset.sum_apply, PeriodicMPSFiveSiteSpecialFiber.gram, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Complex.star_def]
    exact he ▸ hd
  have hm : Differentiable ℝ (fun q => PeriodicMPSFiveSiteNormalization.mass (f q)) := by
    let a (i : Fin 4) (q : E) := PeriodicMPSFiveSiteSpecialFiber.gram (f q) i i
    have hd : Differentiable ℝ (∑ i, a i) := Differentiable.sum fun i _ => hg i i
    have he : Complex.reCLM ∘ (∑ i, a i) = fun q => PeriodicMPSFiveSiteNormalization.mass (f q) := by
      funext q
      simp only [Function.comp_apply, Finset.sum_apply, PeriodicMPSFiveSiteNormalization.mass,
        Matrix.trace, Matrix.diag]
      rfl
    exact he ▸ Complex.reCLM.differentiable.comp hd
  intro q hq
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun x => (PeriodicMPSFiveSiteNormalization.mass (f x))⁻¹ •
    PeriodicMPSFiveSiteSpecialFiber.gram (f x) i j) q
  exact (hm.differentiableAt.inv (mass_positive _ hq).ne').smul (hg i j).differentiableAt

/-- The observations outside the first ordinary trace chart admit a finite
cover by differentiable images of three complex variables. -/
theorem boundary_observation_cover :
    ∃ (D : BoundaryFamily → Set (Fin 3 → ℂ))
      (g : BoundaryFamily → (Fin 3 → ℂ) → Matrix (Fin 4) (Fin 4) ℂ),
      (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      observation '' (source \ PeriodicMPSFiveSiteOrdinaryTrace.chartDomain) ⊆
        ⋃ i, g i '' D i := by
  refine ⟨fun i => {q | boundaryAmplitude i q ≠ 0},
    fun i q => normalizedGram (boundaryAmplitude i q),
    fun i => differentiable_normalizedGram _ (differentiable_boundaryAmplitude i), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨i, q, hq, he⟩ := boundary_amplitude_cover hp.1 hp.2
  exact mem_iUnion.mpr ⟨i, q, hq, (observation_of_projector hq he).symm⟩

private abbrev realIndices : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv (m := 3) (n := 3)

private def complexCoordinates (x : Fin 6 → ℝ) : Fin 3 → ℂ := fun i =>
  ⟨x (realIndices (Sum.inl i)), x (realIndices (Sum.inr i))⟩

private theorem complexCoordinates_surjective : Function.Surjective complexCoordinates := by
  intro q
  refine ⟨(Sum.elim (fun i => (q i).re) (fun i => (q i).im)) ∘ realIndices.symm, ?_⟩
  funext i
  exact Complex.ext (by simp [complexCoordinates, Function.comp_def])
    (by simp [complexCoordinates, Function.comp_def])

private theorem differentiable_complexCoordinates : Differentiable ℝ complexCoordinates := by
  apply differentiable_pi.mpr
  intro i
  change Differentiable ℝ (fun x : Fin 6 → ℝ =>
    Complex.equivRealProdCLM.symm (x (realIndices (Sum.inl i)), x (realIndices (Sum.inr i))))
  exact Complex.equivRealProdCLM.symm.differentiable.comp
    ((differentiable_apply _).prodMk (differentiable_apply _))

/-- The boundary observations are covered in six real coordinates. -/
theorem real_boundary_observation_cover :
    ∃ (D : BoundaryFamily → Set (Fin 6 → ℝ))
      (g : BoundaryFamily → (Fin 6 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ),
      (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      observation '' (source \ PeriodicMPSFiveSiteOrdinaryTrace.chartDomain) ⊆
        ⋃ i, g i '' D i := by
  refine ⟨fun i => {q | boundaryAmplitude i (complexCoordinates q) ≠ 0},
    fun i q => normalizedGram (boundaryAmplitude i (complexCoordinates q)), ?_, ?_⟩
  · intro i
    exact differentiable_normalizedGram _
      ((differentiable_boundaryAmplitude i).comp differentiable_complexCoordinates)
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, q, hq, he⟩ := boundary_amplitude_cover hp.1 hp.2
    obtain ⟨x, rfl⟩ := complexCoordinates_surjective q
    exact mem_iUnion.mpr ⟨i, x, hq, (observation_of_projector hq he).symm⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteBoundaryCover
