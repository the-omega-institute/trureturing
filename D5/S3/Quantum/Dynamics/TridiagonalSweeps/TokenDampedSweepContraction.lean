/- GID: D5/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Token-1 damping contracts the spectrum and all trajectories of every finite chain. -/

/-
result: proof_shape: content.
escape_witness: damped_sweep_eigen_norm_lt_one excludes every unit-modulus
  eigenvector using the Q-loss equality case and finite-path observability.
admission_basis: open-problem-resolution (#14768; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14784
Direct frozen dependencies: CliffordPathRealizations.sum_fin_next
  (declaration statement_id sha256:edd273e059e28fa11f8373977a42e149f4e775fb01970f89f6b7c380c86d29de)
  and CliffordPathRealizations.sum_fin_prev
  (baseline private declaration statement_id sha256:cb090d57f8fd42ddf2111bebd62c06d95af7225cd34b1ba8414b307c35fca6a6)
  supply the adjacent-index sums.
  FixedPositivePartitionSseDistance.jordanShift
  (declaration statement_id sha256:b2021e0d48bb865e00af5328acca8cc1ce57745f504463fd068595ecd7c68aac)
  supplies the two directed adjacency masks in triRow.
  FinitePathDynamics is same-delivery supporting content.
The source's B_α and M_α are the definitions `Balpha` and `Malpha`.
This is a general theorem for every n = m + 1 with m >= 1, every positive velocity
vector, and every damping parameter strictly between zero and one; utility is none.
-/

import D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
import D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance
import Mathlib.LinearAlgebra.Eigenspace.Matrix

open Matrix Filter Topology
open D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics
namespace D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction

noncomputable def A (m : ℕ) (v : Fin (m + 1) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i.val % 2 = 0 then
    if i = j then 1 else 0
  else if i = j then v i.castSucc + v i.succ
  else if j.val + 1 = i.val then -2 * v i.succ
  else if i.val + 1 = j.val then -2 * v i.castSucc
  else 0

noncomputable def B (m : ℕ) (v : Fin (m + 1) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i.val % 2 = 0 then
    if i = j then -1
    else if j.val + 1 = i.val then 2 * v i.succ / (v i.castSucc + v i.succ)
    else if i.val + 1 = j.val then 2 * v i.castSucc / (v i.castSucc + v i.succ)
    else 0
  else if i = j then -(v i.castSucc + v i.succ) else 0

noncomputable def Balpha (m : ℕ) (v : Fin (m + 1) → ℝ) (α : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i.val = 0 then
    if i = j then (v i.succ * (1 - 2 * α) - α * v i.castSucc) /
      (v i.succ + α * v i.castSucc)
    else if i.val + 1 = j.val then 2 * α * v i.castSucc /
      (v i.succ + α * v i.castSucc)
    else 0
  else B m v i j

noncomputable def Malpha (m : ℕ) (v : Fin (m + 1) → ℝ) (α : ℝ) :
    Matrix (Fin m) (Fin m) ℝ := (A m v)⁻¹ * Balpha m v α

def claim : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (v : Fin (m + 1) → ℝ),
    (∀ j, 0 < v j) → ∀ α : ℝ, 0 < α → α < 1 →
      (∀ μ ∈ spectrum ℂ ((Malpha m v α).map (algebraMap ℝ ℂ)), ‖μ‖ < 1) ∧
      (∀ u : Fin m → ℝ, Tendsto (fun k : ℕ => (Malpha m v α ^ k).mulVec u)
        atTop (nhds 0))

private lemma A_mulVec_odd {m : ℕ} (v : Fin (m + 1) → ℝ) (u : Fin m → ℝ)
    (i : Fin m) (hi : i.val % 2 = 0) : (A m v).mulVec u i = u i := by
  simp [Matrix.mulVec, dotProduct, A, hi]

private lemma A_mulVec_even_of_odd_zero {m : ℕ} (v : Fin (m + 1) → ℝ)
    (u : Fin m → ℝ) (hu : ∀ j : Fin m, j.val % 2 = 0 → u j = 0)
    (i : Fin m) (hi : i.val % 2 ≠ 0) :
    (A m v).mulVec u i = (v i.castSucc + v i.succ) * u i := by
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single i]
  · simp [A, hi]
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    simp only [A, if_neg hi, if_neg hij]
    split_ifs with hl hr
    · rw [hu j (by omega), mul_zero]
    · rw [hu j (by omega), mul_zero]
    · exact zero_mul _
  · simp

private lemma A_kernel_trivial {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (u : Fin m → ℝ) (hu : (A m v).mulVec u = 0) : u = 0 := by
  have ho : ∀ i : Fin m, i.val % 2 = 0 → u i = 0 := by
    intro i hi
    have he := congrFun hu i
    simpa [A_mulVec_odd v u i hi] using he
  funext i
  by_cases hi : i.val % 2 = 0
  · exact ho i hi
  · have he := congrFun hu i
    rw [A_mulVec_even_of_odd_zero v u ho i hi] at he
    have hs : v i.castSucc + v i.succ ≠ 0 := ne_of_gt (add_pos (hv _) (hv _))
    exact (mul_eq_zero.mp he).resolve_left hs

private lemma A_isUnit {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j) :
    IsUnit (A m v) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u w huw
  have hz : (A m v).mulVec (u - w) = 0 := by
    rw [Matrix.mulVec_sub, huw, sub_self]
  exact sub_eq_zero.mp (A_kernel_trivial v hv (u - w) hz)

-- Pair coordinate i is the interior vertex i+1; both endpoint values are zero.
private noncomputable def Q {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ) : ℝ :=
  ∑ j : Fin (m + 1), Complex.normSq (zeroExtend z j.succ - zeroExtend z j.castSucc) / v j

private lemma Q_nonneg {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) : 0 ≤ Q v z := by
  exact Finset.sum_nonneg fun j _ => div_nonneg (Complex.normSq_nonneg _) (hv j).le

private lemma Q_eq_zero_imp {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (hq : Q v z = 0) : z = 0 := by
  have hd : ∀ j : Fin (m + 1), zeroExtend z j.succ = zeroExtend z j.castSucc := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => div_nonneg (Complex.normSq_nonneg _) (hv j).le)).mp hq
    intro j
    have he := hs j (Finset.mem_univ j)
    have hn : Complex.normSq (zeroExtend z j.succ - zeroExtend z j.castSucc) = 0 :=
      (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (hv j))
    exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hn)
  apply harmonic_dirichlet_zero v hv z
  intro i
  have hl := hd i.castSucc
  have hr := hd i.succ
  have he : i.succ.castSucc = i.castSucc.succ := by ext; rfl
  rw [extend_interior] at hl
  rw [he, extend_interior] at hr
  rw [sub_eq_zero.mpr hl, sub_eq_zero.mpr hr]
  simp

private lemma Q_pos {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (hz : z ≠ 0) : 0 < Q v z := by
  exact lt_of_le_of_ne (Q_nonneg v hv z) (Ne.symm (fun h => hz (Q_eq_zero_imp v hv z h)))

private lemma extend_smul {m : ℕ} (c : ℂ) (z : Fin m → ℂ) :
    zeroExtend (c • z) = c • zeroExtend z := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [zeroExtend]
  · simp only [zeroExtend, Fin.cases_succ, Pi.smul_apply]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [zeroExtend]
    · simp [zeroExtend]

private lemma Q_smul {m : ℕ} (v : Fin (m + 1) → ℝ) (c : ℂ) (z : Fin m → ℂ) :
    Q v (c • z) = Complex.normSq c * Q v z := by
  simp only [Q, extend_smul, Pi.smul_apply, smul_eq_mul, ← mul_sub,
    Complex.normSq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private noncomputable def localCenter (a b : ℝ) (l r : ℂ) : ℂ :=
  (a / (a + b) : ℝ) • r + (b / (a + b) : ℝ) • l

private lemma local_energy_decomposition (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (l r t : ℂ) :
    Complex.normSq (t - l) / a + Complex.normSq (r - t) / b =
      (a + b) / (a * b) * Complex.normSq (t - localCenter a b l r) +
      Complex.normSq (r - l) / (a + b) := by
  simp only [localCenter, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt (add_pos ha hb)]
  <;> ring

private lemma damped_local_energy (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (l r t : ℂ) (θ : ℝ) :
    let c := localCenter a b l r
    let t' := (1 - θ) • t + θ • ((2 : ℝ) • c - t)
    Complex.normSq (t' - l) / a + Complex.normSq (r - t') / b =
      Complex.normSq (t - l) / a + Complex.normSq (r - t) / b -
        4 * θ * (1 - θ) * ((a + b) / (a * b)) * Complex.normSq (t - c) := by
  dsimp only
  rw [local_energy_decomposition a b ha hb l r,
    local_energy_decomposition a b ha hb l r]
  have he : (1 - θ) • t + θ • ((2 : ℝ) • localCenter a b l r - t) -
      localCenter a b l r = (1 - 2 * θ) • (t - localCenter a b l r) := by
    module
  rw [he]
  have hn (c : ℝ) (z : ℂ) : Complex.normSq (c • z) = c * c * Complex.normSq z := by
    simp only [Complex.normSq_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  rw [hn]
  ring

private lemma theta_bounds (a b α : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hα : 0 < α) (hα1 : α < 1) :
    0 < α * (a + b) / (b + α * a) ∧ α * (a + b) / (b + α * a) < 1 := by
  have hd : 0 < b + α * a := add_pos hb (mul_pos hα ha)
  constructor
  · exact div_pos (mul_pos hα (add_pos ha hb)) hd
  · apply (div_lt_one hd).mpr
    nlinarith [mul_pos hb (sub_pos.mpr hα1)]

private lemma extend_update {m : ℕ} (z : Fin m → ℂ) (i : Fin m) (t : ℂ) :
    zeroExtend (Function.update z i t) = Function.update (zeroExtend z) i.castSucc.succ t := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [zeroExtend, Function.update_of_ne, Fin.ext_iff]
  · simp only [zeroExtend, Fin.cases_succ]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · have hn : Fin.last (m + 1) ≠ i.castSucc.succ := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hh
        omega
      simp [Function.update_of_ne hn, extend_last]
    · by_cases hki : k = i
      · subst k
        simp
      · have hne : k.castSucc.succ ≠ i.castSucc.succ := by
          intro h; exact hki (Fin.ext (by simpa using congrArg Fin.val h))
        simp [Function.update_of_ne hki, Function.update_of_ne hne, extend_interior]

private noncomputable def edgeEnergy {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) (j : Fin (m + 1)) : ℝ :=
  Complex.normSq (zeroExtend z j.succ - zeroExtend z j.castSucc) / v j

private lemma edgeEnergy_update_left {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) (i : Fin m) (t : ℂ) :
    edgeEnergy v (Function.update z i t) i.castSucc =
      Complex.normSq (t - zeroExtend z i.castSucc.castSucc) / v i.castSucc := by
  have hne : i.castSucc.castSucc ≠ i.castSucc.succ := by
    intro h; have hh := congrArg Fin.val h; simp at hh
  simp [edgeEnergy, extend_update, Function.update_of_ne hne]

private lemma edgeEnergy_update_right {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) (i : Fin m) (t : ℂ) :
    edgeEnergy v (Function.update z i t) i.succ =
      Complex.normSq (zeroExtend z i.succ.succ - t) / v i.succ := by
  have he : i.succ.castSucc = i.castSucc.succ := by ext; rfl
  have hne : i.succ.succ ≠ i.castSucc.succ := by
    intro h; have hh := congrArg Fin.val h; simp at hh
  simp [edgeEnergy, extend_update, he, Function.update_of_ne hne]

private lemma edgeEnergy_update_other {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) (i : Fin m) (t : ℂ) (j : Fin (m + 1))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) :
    edgeEnergy v (Function.update z i t) j = edgeEnergy v z j := by
  have hl' : j.succ ≠ i.castSucc.succ := by
    intro h; apply hl; exact Fin.ext (by simpa using congrArg Fin.val h)
  have hr' : j.castSucc ≠ i.castSucc.succ := by
    intro h; apply hr; exact Fin.ext (by simpa using congrArg Fin.val h)
  simp [edgeEnergy, extend_update, Function.update_of_ne hl', Function.update_of_ne hr']

private lemma Q_update {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) (i : Fin m) (t : ℂ) :
    Q v (Function.update z i t) = Q v z +
      (edgeEnergy v (Function.update z i t) i.castSucc - edgeEnergy v z i.castSucc) +
      (edgeEnergy v (Function.update z i t) i.succ - edgeEnergy v z i.succ) := by
  have hne : i.castSucc ≠ i.succ := by
    intro h; have hh := congrArg Fin.val h; simp at hh
  have hd : ∀ j : Fin (m + 1),
      edgeEnergy v (Function.update z i t) j - edgeEnergy v z j =
        (if j = i.castSucc then edgeEnergy v (Function.update z i t) i.castSucc -
            edgeEnergy v z i.castSucc else 0) +
        (if j = i.succ then edgeEnergy v (Function.update z i t) i.succ -
            edgeEnergy v z i.succ else 0) := by
    intro j
    by_cases hl : j = i.castSucc
    · subst j; simp [hne]
    by_cases hr : j = i.succ
    · subst j; simp [hne, Ne.symm hne]
    · simp [hl, hr, edgeEnergy_update_other v z i t j hl hr]
  have hs := congrArg (fun f : Fin (m + 1) → ℝ => ∑ j, f j) (funext hd)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hs
  change Q v (Function.update z i t) - Q v z = _ at hs
  linarith

private noncomputable def center {m : ℕ} (v : Fin (m + 1) → ℝ) (i : Fin m)
    (z : Fin m → ℂ) : ℂ :=
  localCenter (v i.castSucc) (v i.succ)
    (zeroExtend z i.castSucc.castSucc) (zeroExtend z i.succ.succ)

private noncomputable def reflectAt {m : ℕ} (v : Fin (m + 1) → ℝ) (i : Fin m)
    (z : Fin m → ℂ) : ℂ := (2 : ℝ) • center v i z - z i

private noncomputable def event {m : ℕ} (v : Fin (m + 1) → ℝ) (i : Fin m)
    (z : Fin m → ℂ) : Fin m → ℂ := Function.update z i (reflectAt v i z)

private noncomputable def dampedEvent {m : ℕ} (v : Fin (m + 1) → ℝ) (i : Fin m)
    (θ : ℝ) (z : Fin m → ℂ) : Fin m → ℂ :=
  Function.update z i ((1 - θ) • z i + θ • reflectAt v i z)

private lemma Q_dampedEvent_loss {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hv : ∀ j, 0 < v j) (z : Fin m → ℂ) (i : Fin m) (θ : ℝ) :
    Q v (dampedEvent v i θ z) = Q v z -
      4 * θ * (1 - θ) * ((v i.castSucc + v i.succ) / (v i.castSucc * v i.succ)) *
        Complex.normSq (z i - center v i z) := by
  rw [dampedEvent, Q_update, edgeEnergy_update_left, edgeEnergy_update_right]
  have he : i.succ.castSucc = i.castSucc.succ := by ext; rfl
  simp only [edgeEnergy, he, extend_interior]
  have hl := damped_local_energy (v i.castSucc) (v i.succ) (hv _) (hv _)
    (zeroExtend z i.castSucc.castSucc) (zeroExtend z i.succ.succ) (z i) θ
  dsimp only at hl
  change _ = _ - _ * Complex.normSq (z i - localCenter _ _ _ _) at hl
  dsimp only [center, reflectAt]
  linarith

private lemma Q_event {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (i : Fin m) : Q v (event v i z) = Q v z := by
  have he : dampedEvent v i 1 z = event v i z := by simp [dampedEvent, event]
  simpa [he] using Q_dampedEvent_loss v hv z i 1

private lemma Q_dampedEvent_le {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (i : Fin m) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    Q v (dampedEvent v i θ z) ≤ Q v z := by
  rw [Q_dampedEvent_loss v hv z i θ]
  have hp : 0 < 4 * θ * (1 - θ) * ((v i.castSucc + v i.succ) /
      (v i.castSucc * v i.succ)) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hθ) (sub_pos.mpr hθ1))
      (div_pos (add_pos (hv _) (hv _)) (mul_pos (hv _) (hv _)))
  exact sub_le_self _ (mul_nonneg hp.le (Complex.normSq_nonneg _))

private lemma Q_dampedEvent_eq_iff {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (i : Fin m) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    Q v (dampedEvent v i θ z) = Q v z ↔ event v i z = z := by
  have hp : 0 < 4 * θ * (1 - θ) * ((v i.castSucc + v i.succ) /
      (v i.castSucc * v i.succ)) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hθ) (sub_pos.mpr hθ1))
      (div_pos (add_pos (hv _) (hv _)) (mul_pos (hv _) (hv _)))
  rw [Q_dampedEvent_loss v hv z i θ]
  constructor
  · intro he
    have hn : Complex.normSq (z i - center v i z) = 0 := by nlinarith [Complex.normSq_nonneg (z i - center v i z)]
    have hz := sub_eq_zero.mp (Complex.normSq_eq_zero.mp hn)
    funext j
    by_cases hj : j = i
    · subst j; simp only [event, Function.update_self, reflectAt]; rw [hz]; module
    · simp [event, Function.update_of_ne hj]
  · intro he
    have hi := congrFun he i
    simp only [event, Function.update_self, reflectAt] at hi
    have hz : z i = center v i z := by
      simp only [Complex.real_smul, Complex.ofReal_ofNat] at hi
      linear_combination -(1 / 2 : ℂ) * hi
    simp [hz]

private lemma center_update_same_parity {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) (i j : Fin m) (t : ℂ) (hp : i.val % 2 = j.val % 2) :
    center v i (Function.update z j t) = center v i z := by
  have hl : i.castSucc.castSucc ≠ j.castSucc.succ := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  have hr : i.succ.succ ≠ j.castSucc.succ := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  simp [center, extend_update, Function.update_of_ne hl, Function.update_of_ne hr]

private lemma reflectAt_update_same_parity {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) (i j : Fin m) (t : ℂ) (hp : i.val % 2 = j.val % 2)
    (hij : i ≠ j) : reflectAt v i (Function.update z j t) = reflectAt v i z := by
  simp [reflectAt, center_update_same_parity v z i j t hp, Function.update_of_ne hij]

private noncomputable def foldEvents {m : ℕ} (v : Fin (m + 1) → ℝ)
    (L : List (Fin m)) (z : Fin m → ℂ) : Fin m → ℂ :=
  L.foldl (fun w i => event v i w) z

private lemma Q_foldEvents {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (L : List (Fin m)) (z : Fin m → ℂ) : Q v (foldEvents v L z) = Q v z := by
  change Q v (L.foldl (fun w i => event v i w) z) = Q v z
  simpa only [List.foldl_fixed] using
    (List.foldl_hom (Q v) (g₁ := fun w i => event v i w)
      (g₂ := fun q _ => q) (l := L) (init := z)
      (fun w i => (Q_event v hv w i).symm)).symm

private lemma foldEvents_apply_not_mem {m : ℕ} (v : Fin (m + 1) → ℝ)
    (L : List (Fin m)) (z : Fin m → ℂ) (i : Fin m) (hi : i ∉ L) :
    foldEvents v L z i = z i := by
  induction L generalizing z with
  | nil => rfl
  | cons j L ih =>
    have hj : i ≠ j := by simpa using (not_or.mp (by simpa using hi)).1
    have hL : i ∉ L := by simpa using (not_or.mp (by simpa using hi)).2
    change foldEvents v L (event v j z) i = z i
    rw [ih _ hL]
    simp [event, Function.update_of_ne hj]

private lemma foldEvents_apply_mem {m : ℕ} (v : Fin (m + 1) → ℝ)
    (L : List (Fin m)) (z : Fin m → ℂ) (i : Fin m) (hn : L.Nodup) (hi : i ∈ L)
    (hp : ∀ j ∈ L, i.val % 2 = j.val % 2) : foldEvents v L z i = reflectAt v i z := by
  induction L generalizing z with
  | nil => simp at hi
  | cons j L ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hij : i = j
    · subst j
      change foldEvents v L (event v i z) i = reflectAt v i z
      rw [foldEvents_apply_not_mem v L _ i hn'.1]
      simp [event]
    · have hi' : i ∈ L := (List.mem_cons.mp hi).resolve_left hij
      have hp' : ∀ k ∈ L, i.val % 2 = k.val % 2 := fun k hk => hp k (List.mem_cons_of_mem _ hk)
      change foldEvents v L (event v j z) i = reflectAt v i z
      rw [ih _ hn'.2 hi' hp']
      exact reflectAt_update_same_parity v z i j _ (hp j (by simp)) hij

private noncomputable def parityList (m : ℕ) (p : ℕ) : List (Fin m) :=
  (Finset.univ.filter fun i : Fin m => i.val % 2 = p).toList

private noncomputable def phase {m : ℕ} (v : Fin (m + 1) → ℝ) (p : ℕ)
    (z : Fin m → ℂ) : Fin m → ℂ := foldEvents v (parityList m p) z

private lemma phase_apply {m : ℕ} (v : Fin (m + 1) → ℝ) (p : ℕ) (z : Fin m → ℂ)
    (i : Fin m) : phase v p z i = if i.val % 2 = p then reflectAt v i z else z i := by
  by_cases hp : i.val % 2 = p
  · rw [if_pos hp]
    apply foldEvents_apply_mem
    · exact Finset.nodup_toList _
    · simp [parityList, hp]
    · intro j hj
      rw [hp]
      symm
      simpa [parityList] using hj
  · rw [if_neg hp]
    apply foldEvents_apply_not_mem
    simpa [parityList] using hp

private lemma Q_phase {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (p : ℕ) (z : Fin m → ℂ) : Q v (phase v p z) = Q v z := Q_foldEvents v hv _ _

private noncomputable def oddTailList (m : ℕ) : List (Fin m) :=
  (Finset.univ.filter fun i : Fin m => i.val % 2 = 0 ∧ i.val ≠ 0).toList

private noncomputable def oddTail {m : ℕ} (v : Fin (m + 1) → ℝ)
    (z : Fin m → ℂ) : Fin m → ℂ := foldEvents v (oddTailList m) z

private lemma oddTail_apply {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ) (i : Fin m) :
    oddTail v z i = if i.val % 2 = 0 ∧ i.val ≠ 0 then reflectAt v i z else z i := by
  by_cases hp : i.val % 2 = 0 ∧ i.val ≠ 0
  · rw [if_pos hp]
    apply foldEvents_apply_mem
    · exact Finset.nodup_toList _
    · simp [oddTailList, hp]
    · intro j hj
      have hj' : j.val % 2 = 0 ∧ j.val ≠ 0 := by simpa [oddTailList] using hj
      exact hp.1.trans hj'.1.symm
  · rw [if_neg hp]
    apply foldEvents_apply_not_mem
    simpa [oddTailList] using hp

private noncomputable def oddDamped {m : ℕ} (v : Fin (m + 1) → ℝ) (hm : 1 ≤ m)
    (θ : ℝ) (z : Fin m → ℂ) : Fin m → ℂ := oddTail v (dampedEvent v ((⟨0, hm⟩ : Fin m)) θ z)

private lemma oddDamped_apply {m : ℕ} (v : Fin (m + 1) → ℝ) (hm : 1 ≤ m)
    (θ : ℝ) (z : Fin m → ℂ) (i : Fin m) : oddDamped v hm θ z i =
      if i.val = 0 then (1 - θ) • z i + θ • reflectAt v i z
      else if i.val % 2 = 0 then reflectAt v i z else z i := by
  rw [oddDamped, oddTail_apply]
  by_cases hi0 : i.val = 0
  · have he : i = (⟨0, hm⟩ : Fin m) := Fin.ext hi0
    subst i
    simp [dampedEvent]
  · have hif : i ≠ (⟨0, hm⟩ : Fin m) := by intro h; exact hi0 (congrArg Fin.val h)
    by_cases hp : i.val % 2 = 0
    · simp only [hp, hi0, ne_eq, not_false_eq_true, and_self, if_true, if_false]
      unfold dampedEvent
      apply reflectAt_update_same_parity
      · simpa using hp
      · exact hif
    · simp [hp, hi0, dampedEvent, Function.update_of_ne hif]

private noncomputable def sweep {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ) :
    Fin m → ℂ := phase v 1 (phase v 0 z)

private noncomputable def sweepTheta {m : ℕ} (v : Fin (m + 1) → ℝ) (hm : 1 ≤ m)
    (θ : ℝ) (z : Fin m → ℂ) : Fin m → ℂ := phase v 1 (oddDamped v hm θ z)

private lemma Q_sweepTheta {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (hm : 1 ≤ m) (θ : ℝ) (z : Fin m → ℂ) :
    Q v (sweepTheta v hm θ z) = Q v (dampedEvent v ((⟨0, hm⟩ : Fin m)) θ z) := by
  rw [sweepTheta, Q_phase v hv, oddDamped, oddTail, Q_foldEvents v hv]

private lemma Q_sweepTheta_le {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (z : Fin m → ℂ) :
    Q v (sweepTheta v hm θ z) ≤ Q v z := by
  rw [Q_sweepTheta v hv]
  exact Q_dampedEvent_le v hv z _ θ hθ hθ1

private lemma Q_sweepTheta_eq_iff {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (z : Fin m → ℂ) :
    Q v (sweepTheta v hm θ z) = Q v z ↔ event v ((⟨0, hm⟩ : Fin m)) z = z := by
  rw [Q_sweepTheta v hv]
  exact Q_dampedEvent_eq_iff v hv z _ θ hθ hθ1

private lemma dampedEvent_eq_of_fixed {m : ℕ} (v : Fin (m + 1) → ℝ)
    (i : Fin m) (θ : ℝ) (z : Fin m → ℂ) (he : event v i z = z) :
    dampedEvent v i θ z = z := by
  have hi := congrFun he i
  simp only [event, Function.update_self] at hi
  have ht : (1 - θ) • z i + θ • reflectAt v i z = z i := by rw [hi]; module
  rw [dampedEvent, ht]
  simp

private lemma sweepTheta_of_fixed {m : ℕ} (v : Fin (m + 1) → ℝ) (hm : 1 ≤ m)
    (θ : ℝ) (z : Fin m → ℂ) (he : event v ((⟨0, hm⟩ : Fin m)) z = z) :
    sweepTheta v hm θ z = sweep v z := by
  have hd : oddDamped v hm θ z = phase v 0 z := by
    rw [oddDamped, dampedEvent_eq_of_fixed v _ θ z he]
    funext i
    rw [oddTail_apply, phase_apply]
    by_cases hi : i.val = 0
    · have hif : i = (⟨0, hm⟩ : Fin m) := Fin.ext hi
      subst i
      have ht := congrFun he ((⟨0, hm⟩ : Fin m))
      simp only [event, Function.update_self] at ht
      simpa using ht.symm
    · simp [hi]
  rw [sweepTheta, hd, sweep]

private lemma sum_left_neighbor {m : ℕ} (z : Fin m → ℂ) (i : Fin m) (c : ℂ) :
    (∑ j : Fin m, (if j.val + 1 = i.val then c else 0) * z j) =
      c * zeroExtend z i.castSucc.castSucc := by
  simp_rw [ite_mul, zero_mul]
  rw [D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations.sum_fin_prev]
  by_cases hi : 0 < i.val
  · rw [dif_pos hi]
    have he : i.castSucc.castSucc = (⟨i.val - 1, by omega⟩ : Fin m).castSucc.succ := by
      ext; simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [he, extend_interior]
  · rw [dif_neg hi]
    have he : i.castSucc.castSucc = 0 := Fin.ext (by simp only [Fin.val_castSucc, Fin.val_zero]; omega)
    simp [he, zeroExtend]

private lemma sum_right_neighbor {m : ℕ} (z : Fin m → ℂ) (i : Fin m) (c : ℂ) :
    (∑ j : Fin m, (if i.val + 1 = j.val then c else 0) * z j) =
      c * zeroExtend z i.succ.succ := by
  simp_rw [ite_mul, zero_mul]
  rw [D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations.sum_fin_next]
  by_cases hi : i.val + 1 < m
  · rw [dif_pos hi]
    have he : i.succ.succ = (⟨i.val + 1, hi⟩ : Fin m).castSucc.succ := by ext; rfl
    rw [he, extend_interior]
  · rw [dif_neg hi]
    have he : i.succ.succ = Fin.last (m + 1) := by
      ext; simp only [Fin.val_succ, Fin.val_last]; omega
    rw [he, extend_last, mul_zero]

private noncomputable def triRow {m : ℕ} (d l r : ℂ) (i j : Fin m) : ℂ :=
  (Matrix.diagonal (fun _ : Fin m => d) +
    l • ((D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance.jordanShift m).map
      (Nat.cast : ℕ → ℂ)).transpose +
    r • ((D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance.jordanShift m).map
      (Nat.cast : ℕ → ℂ))) i j

private lemma triRow_mulVec {m : ℕ} (d l r : ℂ) (z : Fin m → ℂ) (i : Fin m) :
    (∑ j : Fin m, triRow d l r i j * z j) =
      d * z i + l * zeroExtend z i.castSucc.castSucc + r * zeroExtend z i.succ.succ := by
  simp only [triRow, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Matrix.map_apply,
    D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance.jordanShift,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, smul_eq_mul, mul_ite, mul_one, mul_zero, add_mul, Finset.sum_add_distrib]
  rw [sum_left_neighbor, sum_right_neighbor]
  simp

private lemma A_complex_mulVec_odd {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (i : Fin m) (hi : i.val % 2 = 0) :
    ((A m v).map (algebraMap ℝ ℂ)).mulVec z i = z i := by
  simp [Matrix.mulVec, dotProduct, A, hi, Complex.coe_algebraMap, apply_ite]

private lemma A_complex_mulVec_even {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (i : Fin m) (hi : i.val % 2 ≠ 0) :
    ((A m v).map (algebraMap ℝ ℂ)).mulVec z i =
      (v i.castSucc + v i.succ : ℝ) • z i -
        (2 * v i.succ : ℝ) • zeroExtend z i.castSucc.castSucc -
        (2 * v i.castSucc : ℝ) • zeroExtend z i.succ.succ := by
  have he : ∀ j : Fin m, ((A m v).map (algebraMap ℝ ℂ)) i j =
      triRow (v i.castSucc + v i.succ) (-2 * v i.succ) (-2 * v i.castSucc) i j := by
    intro j
    simp only [Matrix.map_apply, A, if_neg hi, Complex.coe_algebraMap, triRow, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Matrix.map_apply,
    D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance.jordanShift,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hij : i = j
    · subst j
      simp
    · have hn : ¬(j.val + 1 = i.val ∧ i.val + 1 = j.val) := by omega
      split_ifs <;> simp_all
  unfold Matrix.mulVec dotProduct
  simp_rw [he]
  rw [triRow_mulVec]
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

private lemma B_complex_mulVec_odd {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (i : Fin m) (hi : i.val % 2 = 0) :
    ((B m v).map (algebraMap ℝ ℂ)).mulVec z i =
      -z i + (2 * v i.succ / (v i.castSucc + v i.succ) : ℝ) • zeroExtend z i.castSucc.castSucc +
        (2 * v i.castSucc / (v i.castSucc + v i.succ) : ℝ) • zeroExtend z i.succ.succ := by
  have he : ∀ j : Fin m, ((B m v).map (algebraMap ℝ ℂ)) i j =
      triRow (-1) (2 * v i.succ / (v i.castSucc + v i.succ))
        (2 * v i.castSucc / (v i.castSucc + v i.succ)) i j := by
    intro j
    simp only [Matrix.map_apply, B, if_pos hi, Complex.coe_algebraMap, triRow, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Matrix.map_apply,
    D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance.jordanShift,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hij : i = j
    · subst j; simp
    · have hn : ¬(j.val + 1 = i.val ∧ i.val + 1 = j.val) := by omega
      split_ifs <;> simp_all
  unfold Matrix.mulVec dotProduct
  simp_rw [he]
  rw [triRow_mulVec]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

private lemma B_complex_mulVec_even {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (i : Fin m) (hi : i.val % 2 ≠ 0) :
    ((B m v).map (algebraMap ℝ ℂ)).mulVec z i =
      -(v i.castSucc + v i.succ : ℝ) • z i := by
  simp [Matrix.mulVec, dotProduct, B, hi, Complex.coe_algebraMap, Complex.real_smul, apply_ite]

private lemma reflectAt_formula {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (i : Fin m) : reflectAt v i z = -z i +
      (2 * v i.succ / (v i.castSucc + v i.succ) : ℝ) • zeroExtend z i.castSucc.castSucc +
      (2 * v i.castSucc / (v i.castSucc + v i.succ) : ℝ) • zeroExtend z i.succ.succ := by
  unfold reflectAt center localCenter
  module

private lemma reflectAt_equation {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (i : Fin m) :
    (v i.castSucc + v i.succ : ℝ) • reflectAt v i z -
      (2 * v i.succ : ℝ) • zeroExtend z i.castSucc.castSucc -
      (2 * v i.castSucc : ℝ) • zeroExtend z i.succ.succ =
      -(v i.castSucc + v i.succ : ℝ) • z i := by
  have hs : v i.castSucc + v i.succ ≠ 0 := ne_of_gt (add_pos (hv _) (hv _))
  have hsC : (v i.castSucc : ℂ) + (v i.succ : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [reflectAt_formula]
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
  field_simp [hsC]
  ring

private lemma phase_left_same_parity {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (i : Fin m) (p : ℕ) (hi : i.val % 2 = p) :
    zeroExtend (phase v p z) i.castSucc.castSucc = zeroExtend z i.castSucc.castSucc := by
  have hs : (∑ j : Fin m, (if j.val + 1 = i.val then (1 : ℂ) else 0) * phase v p z j) =
      ∑ j : Fin m, (if j.val + 1 = i.val then (1 : ℂ) else 0) * z j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val + 1 = i.val
    · have hp : j.val % 2 ≠ p := by omega
      rw [phase_apply, if_neg hp]
    · simp [hj]
  simpa only [sum_left_neighbor, one_mul] using hs

private lemma phase_right_same_parity {m : ℕ} (v : Fin (m + 1) → ℝ) (z : Fin m → ℂ)
    (i : Fin m) (p : ℕ) (hi : i.val % 2 = p) :
    zeroExtend (phase v p z) i.succ.succ = zeroExtend z i.succ.succ := by
  have hs : (∑ j : Fin m, (if i.val + 1 = j.val then (1 : ℂ) else 0) * phase v p z j) =
      ∑ j : Fin m, (if i.val + 1 = j.val then (1 : ℂ) else 0) * z j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : i.val + 1 = j.val
    · have hp : j.val % 2 ≠ p := by omega
      rw [phase_apply, if_neg hp]
    · simp [hj]
  simpa only [sum_right_neighbor, one_mul] using hs

private lemma Balpha_complex_mulVec_first {m : ℕ} (v : Fin (m + 1) → ℝ) (α : ℝ)
    (z : Fin m → ℂ) (i : Fin m) (hi : i.val = 0) :
    ((Balpha m v α).map (algebraMap ℝ ℂ)).mulVec z i =
      ((v i.succ * (1 - 2 * α) - α * v i.castSucc) / (v i.succ + α * v i.castSucc) : ℝ) • z i +
      (2 * α * v i.castSucc / (v i.succ + α * v i.castSucc) : ℝ) • zeroExtend z i.succ.succ := by
  have he : ∀ j : Fin m, ((Balpha m v α).map (algebraMap ℝ ℂ)) i j =
      triRow ((v i.succ * (1 - 2 * α) - α * v i.castSucc) / (v i.succ + α * v i.castSucc))
        0 (2 * α * v i.castSucc / (v i.succ + α * v i.castSucc)) i j := by
    intro j
    simp only [Matrix.map_apply, Balpha, if_pos hi, Complex.coe_algebraMap, triRow, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Matrix.map_apply,
    D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance.jordanShift,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hij : i = j
    · subst j; simp
    · have hl : j.val + 1 ≠ i.val := by omega
      split_ifs <;> simp_all
  unfold Matrix.mulVec dotProduct
  simp_rw [he]
  rw [triRow_mulVec]
  simp only [zero_mul, add_zero, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_add]

private lemma Balpha_complex_mulVec_rest {m : ℕ} (v : Fin (m + 1) → ℝ) (α : ℝ)
    (z : Fin m → ℂ) (i : Fin m) (hi : i.val ≠ 0) :
    ((Balpha m v α).map (algebraMap ℝ ℂ)).mulVec z i =
      ((B m v).map (algebraMap ℝ ℂ)).mulVec z i := by
  simp [Matrix.mulVec, dotProduct, Balpha, hi]

private noncomputable def theta {m : ℕ} (v : Fin (m + 1) → ℝ) (hm : 1 ≤ m) (α : ℝ) : ℝ :=
  α * (v ((⟨0, hm⟩ : Fin m)).castSucc + v ((⟨0, hm⟩ : Fin m)).succ) /
    (v ((⟨0, hm⟩ : Fin m)).succ + α * v ((⟨0, hm⟩ : Fin m)).castSucc)

private lemma theta_pos_lt_one {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < theta v hm α ∧ theta v hm α < 1 := theta_bounds _ _ α (hv _) (hv _) hα hα1

private lemma damped_first_formula {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (α : ℝ) (hα : 0 < α) (z : Fin m → ℂ) (i : Fin m) (hi : i.val = 0) :
    let θ := α * (v i.castSucc + v i.succ) / (v i.succ + α * v i.castSucc)
    (1 - θ) • z i + θ • reflectAt v i z =
      ((v i.succ * (1 - 2 * α) - α * v i.castSucc) / (v i.succ + α * v i.castSucc) : ℝ) • z i +
      (2 * α * v i.castSucc / (v i.succ + α * v i.castSucc) : ℝ) • zeroExtend z i.succ.succ := by
  have hl : i.castSucc.castSucc = 0 := Fin.ext hi
  have hs : (v i.castSucc : ℂ) + (v i.succ : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (hv _) (hv _))
  have hd : (v i.succ : ℂ) + (α : ℂ) * (v i.castSucc : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (hv _) (mul_pos hα (hv _)))
  dsimp only
  rw [reflectAt_formula, hl]
  simp only [zeroExtend, Fin.cases_zero, smul_zero, add_zero, Complex.real_smul,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp [hs, hd]
  ring

private lemma sweep_stacked {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) :
    ((A m v).map (algebraMap ℝ ℂ)).mulVec (sweep v z) =
      ((B m v).map (algebraMap ℝ ℂ)).mulVec z := by
  funext i
  by_cases hi : i.val % 2 = 0
  · have hn : i.val % 2 ≠ 1 := by omega
    rw [A_complex_mulVec_odd v _ i hi, sweep, phase_apply, if_neg hn,
      phase_apply, if_pos hi, B_complex_mulVec_odd v z i hi, reflectAt_formula]
  · have hi1 : i.val % 2 = 1 := by omega
    rw [A_complex_mulVec_even v _ i hi, sweep,
      phase_left_same_parity v _ i 1 hi1, phase_right_same_parity v _ i 1 hi1,
      phase_apply, if_pos hi1, reflectAt_equation v hv,
      phase_apply, if_neg hi, B_complex_mulVec_even v z i hi]

private lemma sweepTheta_stacked {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (z : Fin m → ℂ) :
    ((A m v).map (algebraMap ℝ ℂ)).mulVec (sweepTheta v hm (theta v hm α) z) =
      ((Balpha m v α).map (algebraMap ℝ ℂ)).mulVec z := by
  funext i
  by_cases hi : i.val % 2 = 0
  · have hn : i.val % 2 ≠ 1 := by omega
    rw [A_complex_mulVec_odd v _ i hi, sweepTheta, phase_apply, if_neg hn, oddDamped_apply]
    by_cases hi0 : i.val = 0
    · have he : i = (⟨0, hm⟩ : Fin m) := Fin.ext hi0
      rw [if_pos hi0, Balpha_complex_mulVec_first v α z i hi0]
      simpa only [theta, ← he] using damped_first_formula v hv α hα z i hi0
    · rw [if_neg hi0, if_pos hi, Balpha_complex_mulVec_rest v α z i hi0,
        B_complex_mulVec_odd v z i hi, reflectAt_formula]
  · have hi1 : i.val % 2 = 1 := by omega
    have hi0 : i.val ≠ 0 := by omega
    rw [A_complex_mulVec_even v _ i hi, sweepTheta,
      phase_left_same_parity v _ i 1 hi1, phase_right_same_parity v _ i 1 hi1,
      phase_apply, if_pos hi1, reflectAt_equation v hv, oddDamped_apply,
      if_neg hi0, if_neg hi, Balpha_complex_mulVec_rest v α z i hi0,
      B_complex_mulVec_even v z i hi]

private lemma A_mul_inv {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j) :
    A m v * (A m v)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (A_isUnit v hv))

private lemma source_factorization {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (z : Fin m → ℂ) :
    ((Malpha m v α).map (algebraMap ℝ ℂ)).mulVec z = sweepTheta v hm (theta v hm α) z := by
  have hu : IsUnit ((A m v).map (algebraMap ℝ ℂ)) :=
    (A_isUnit v hv).map (algebraMap ℝ ℂ).mapMatrix
  apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  have hmprod : (A m v).map (algebraMap ℝ ℂ) * (Malpha m v α).map (algebraMap ℝ ℂ) =
      (Balpha m v α).map (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul]
    congr 1
    rw [Malpha, ← mul_assoc, A_mul_inv v hv, one_mul]
  rw [Matrix.mulVec_mulVec, hmprod, sweepTheta_stacked v hv hm α hα]

private lemma fixed_reflection_slopes {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (i : Fin m) (hi : reflectAt v i z = z i) :
    (zeroExtend z i.castSucc.succ - zeroExtend z i.castSucc.castSucc) / (v i.castSucc : ℂ) =
      (zeroExtend z i.succ.succ - zeroExtend z i.succ.castSucc) / (v i.succ : ℂ) := by
  have hv0 : (v i.castSucc : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hv i.castSucc)
  have hv1 : (v i.succ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hv i.succ)
  have hs : (v i.castSucc : ℂ) + (v i.succ : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (hv i.castSucc) (hv i.succ))
  have he := reflectAt_equation v hv z i
  rw [hi] at he
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_neg] at he
  have heq : i.succ.castSucc = i.castSucc.succ := by ext; rfl
  simp only [heq, extend_interior]
  apply (div_eq_div_iff hv0 hv1).mpr
  linear_combination (1 / 2 : ℂ) * he

private lemma dirichlet_fixed_zero {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (hfix : ∀ i : Fin m, reflectAt v i z = z i) : z = 0 := by
  apply D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.harmonic_dirichlet_zero v hv z
  intro i
  have h := fixed_reflection_slopes v hv z i (hfix i)
  have heq : i.succ.castSucc = i.castSucc.succ := by ext; rfl
  simpa only [heq, extend_interior, zeroExtend, Fin.cases_succ, Fin.snoc_castSucc] using h

private lemma sweep_fixed_zero {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (hz : sweep v z = z) : z = 0 := by
  have ho : phase v 0 z = z := by
    funext i
    by_cases hi : i.val % 2 = 0
    · have hi1 : i.val % 2 ≠ 1 := by omega
      have h := congrFun hz i
      rw [sweep, phase_apply, if_neg hi1] at h
      exact h
    · rw [phase_apply, if_neg hi]
  apply dirichlet_fixed_zero v hv z
  intro i
  by_cases hi : i.val % 2 = 0
  · have h := congrFun ho i
    simpa [phase_apply, hi] using h
  · have hi1 : i.val % 2 = 1 := by omega
    have h := congrFun hz i
    rw [sweep, ho, phase_apply, if_pos hi1] at h
    exact h

private lemma zero_propagates {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ) (c : ℂ) (hc : c ≠ 0)
    (he : ((A m v).map (algebraMap ℝ ℂ)).mulVec (c • z) =
      ((B m v).map (algebraMap ℝ ℂ)).mulVec z)
    (i : Fin m) (hi : z i = 0) (hl : zeroExtend z i.castSucc.castSucc = 0) :
    zeroExtend z i.succ.succ = 0 := by
  have h := congrFun he i
  by_cases hp : i.val % 2 = 0
  · rw [A_complex_mulVec_odd v _ i hp, B_complex_mulVec_odd v z i hp] at h
    simp only [Pi.smul_apply, smul_eq_mul, hi, hl, mul_zero, neg_zero, zero_add,
      Complex.real_smul, smul_zero] at h
    have hvn : ((2 * v i.castSucc / (v i.castSucc + v i.succ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast div_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt (hv _)))
        (ne_of_gt (add_pos (hv _) (hv _)))
    exact (mul_eq_zero.mp h.symm).resolve_left hvn
  · rw [A_complex_mulVec_even v _ i hp, B_complex_mulVec_even v z i hp] at h
    simp only [extend_smul, Pi.smul_apply, smul_eq_mul, hi, hl, mul_zero, zero_sub,
      Complex.real_smul, smul_zero] at h
    have hvn : (((2 * v i.castSucc : ℝ) : ℂ) * c) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast mul_ne_zero (by norm_num) (ne_of_gt (hv _))) hc
    have hmul : (((2 * v i.castSucc : ℝ) : ℂ) * c) * zeroExtend z i.succ.succ = 0 := by
      simpa only [neg_zero, zero_sub, neg_eq_zero, mul_assoc] using h
    exact (mul_eq_zero.mp hmul).resolve_left hvn

private lemma source_eigen_zero_of_first_zero {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hv : ∀ j, 0 < v j) (hm : 1 ≤ m) (z : Fin m → ℂ) (c : ℂ) (hc : c ≠ 0)
    (he : ((A m v).map (algebraMap ℝ ℂ)).mulVec (c • z) =
      ((B m v).map (algebraMap ℝ ℂ)).mulVec z)
    (hz : z ((⟨0, hm⟩ : Fin m)) = 0) : z = 0 := by
  apply D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.boundary_zero_observability hm z hz
  intro i hi hl
  exact zero_propagates v hv z c hc he i hi hl

private lemma sweep_eigen_fixed_first_zero {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hv : ∀ j, 0 < v j) (hm : 1 ≤ m) (z : Fin m → ℂ) (c : ℂ) (hc : c ≠ 0)
    (he : sweep v z = c • z) (hf : event v ((⟨0, hm⟩ : Fin m)) z = z) : z = 0 := by
  by_cases hc1 : c = 1
  · subst c
    apply sweep_fixed_zero v hv z
    simpa using he
  · have hi := congrFun he ((⟨0, hm⟩ : Fin m))
    have ht := congrFun hf ((⟨0, hm⟩ : Fin m))
    simp only [event, Function.update_self] at ht
    simp [sweep, phase_apply] at hi
    change reflectAt v ((⟨0, hm⟩ : Fin m)) z = c * z ((⟨0, hm⟩ : Fin m)) at hi
    have hz : z ((⟨0, hm⟩ : Fin m)) = 0 := by
      have hh : (c - 1) * z ((⟨0, hm⟩ : Fin m)) = 0 := by
        linear_combination ht - hi
      exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hc1)
    apply source_eigen_zero_of_first_zero v hv hm z c hc _ hz
    rw [← he]
    exact sweep_stacked v hv z

private lemma damped_sweep_eigen_norm_lt_one {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hv : ∀ j, 0 < v j) (hm : 1 ≤ m) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (z : Fin m → ℂ) (hz : z ≠ 0) (c : ℂ) (he : sweepTheta v hm θ z = c • z) : ‖c‖ < 1 := by
  have hq : 0 < Q v z := Q_pos v hv z hz
  have hn := Q_sweepTheta_le v hv hm θ hθ hθ1 z
  rw [he, Q_smul] at hn
  have hnle : ‖c‖ ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq] at hn
    have hs : ‖c‖ ^ 2 ≤ 1 := by
      apply (mul_le_mul_iff_right₀ hq).mp
      simpa only [one_mul, mul_one, mul_comm] using hn
    nlinarith [norm_nonneg c]
  have hnne : ‖c‖ ≠ 1 := by
    intro hc
    have hcq : Q v (sweepTheta v hm θ z) = Q v z := by
      rw [he, Q_smul, Complex.normSq_eq_norm_sq, hc]
      ring
    have hfix := (Q_sweepTheta_eq_iff v hv hm θ hθ hθ1 z).mp hcq
    have hundamped : sweep v z = c • z := by
      rw [← sweepTheta_of_fixed v hm θ z hfix]
      exact he
    have hc0 : c ≠ 0 := by intro h; simp [h] at hc
    exact hz (sweep_eigen_fixed_first_zero v hv hm z c hc0 hundamped hfix)
  exact lt_of_le_of_ne hnle hnne

private lemma spectral_bound {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∀ c ∈ spectrum ℂ ((Malpha m v α).map (algebraMap ℝ ℂ)), ‖c‖ < 1 := by
  intro c hc
  let N := (Malpha m v α).map (algebraMap ℝ ℂ)
  have hcs : c ∈ spectrum ℂ N.toLin' := by
    simpa only [Matrix.spectrum_toLin'] using hc
  have hce := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hcs
  obtain ⟨z, hz⟩ := hce.exists_hasEigenvector
  have he := hz.apply_eq_smul
  change N.mulVec z = c • z at he
  dsimp only [N] at he
  rw [source_factorization v hv hm α hα z] at he
  obtain ⟨hθ, hθ1⟩ := theta_pos_lt_one v hv hm α hα hα1
  exact damped_sweep_eigen_norm_lt_one v hv hm _ hθ hθ1 z hz.2 c he

theorem result : claim := by
  intro m hm v hv α hα hα1
  have hspec := spectral_bound v hv hm α hα hα1
  exact ⟨hspec, real_mulVec_powers_tendsto_zero hm _ hspec⟩

#print axioms result
end D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction
