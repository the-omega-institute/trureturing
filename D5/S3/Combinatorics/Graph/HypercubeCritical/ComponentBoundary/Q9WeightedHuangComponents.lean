/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedHuangComponents
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Separated balanced components of a 258-vertex Q9 set attain the weighted Huang bound. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! The ambient Clifford square turns equality in a selected block into an ambient
eigenvector equation. Balance and connectivity make each such block simple. -/

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangComponents

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj gamma gamma_apply IsBalanced IsSwitching)
open Q9MixedBoundaryCollisions (Separated)
open Q9WeightedHuangSaturation
open Module.End (mem_eigenspace_iff)
open private huangMatrix huangMatrix_symmetric from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private switching_sq matrix_support from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private outsideRestriction from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenDimension
open private Separated.symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions

set_option autoImplicit false
noncomputable section

private theorem weighted_apply {n : ℕ} (t : Fin n → ℝ) (v : Q n → ℝ) (x : Q n) :
    weightedHuang t v x = ∑ i, t i * (huangMatrix n x (flip x i) * v (flip x i)) := by
  simp only [weightedHuang, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, gamma_apply]

private theorem gamma_symmetric {n : ℕ} (i : Fin n) (u v : Q n → ℝ) :
    u ⬝ᵥ gamma i v = gamma i u ⬝ᵥ v := by
  let e : Q n ≃ Q n := (show Function.Involutive (fun x : Q n => flip x i) from
    fun x => BalancedCriticalSpectrum.flip_flip x i).toPerm
  calc
    u ⬝ᵥ gamma i v = ∑ x, u (e x) * gamma i v (e x) :=
      (e.sum_comp (fun x => u x * gamma i v x)).symm
    _ = gamma i u ⬝ᵥ v := by
      apply Finset.sum_congr rfl
      intro x _
      change u (flip x i) * gamma i v (flip x i) = gamma i u x * v x
      rw [gamma_apply, gamma_apply, BalancedCriticalSpectrum.flip_flip,
        huangMatrix_symmetric (flip x i) x]
      ring

private theorem weighted_symmetric {n : ℕ} (t : Fin n → ℝ) (u v : Q n → ℝ) :
    u ⬝ᵥ weightedHuang t v = weightedHuang t u ⬝ᵥ v := by
  simp only [weightedHuang, LinearMap.sum_apply, LinearMap.smul_apply, dotProduct_sum,
    sum_dotProduct, dotProduct_smul, smul_dotProduct, gamma_symmetric]

/-- A vector with Rayleigh numerator at least the positive Clifford bound
times its squared length satisfies the ambient eigenvector equation. -/
private theorem eigen_of_rayleigh {n : ℕ} (t : Fin n → ℝ) (v : Q n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsq : r ^ 2 = ∑ i, t i ^ 2)
    (h : r * (v ⬝ᵥ v) ≤ v ⬝ᵥ weightedHuang t v) :
    weightedHuang t v = r • v := by
  let H := weightedHuang t
  have hnorm : H v ⬝ᵥ H v = r ^ 2 * (v ⬝ᵥ v) := by
    rw [← weighted_symmetric t, weightedHuang_square, ← hsq, dotProduct_smul, smul_eq_mul]
  let d := H v - r • v
  have hres : d ⬝ᵥ d ≤ 0 := by
    change (H v - r • v) ⬝ᵥ (H v - r • v) ≤ 0
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hnorm, dotProduct_comm (H v) v]
    change r * (v ⬝ᵥ v) ≤ v ⬝ᵥ H v at h
    have hmul := mul_le_mul_of_nonneg_left h hr.le
    linarith only [hmul, show r ^ 2 * (v ⬝ᵥ v) = r * (r * (v ⬝ᵥ v)) by ring]
  have hnonneg : 0 ≤ d ⬝ᵥ d :=
    Finset.sum_nonneg (fun x _ => mul_self_nonneg (d x))
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp (le_antisymm hres hnonneg))

private theorem mem_supported_iff (t : Fin 9 → ℝ) (C : Finset (Q 9)) (v : Q 9 → ℝ) :
    v ∈ supportedWeightedEigenSpace t C ↔
      weightedHuang t v = Real.sqrt (∑ i, t i ^ 2) • v ∧ ∀ x ∉ C, v x = 0 := by
  rw [supportedWeightedEigenSpace, Submodule.mem_inf, mem_eigenspace_iff, LinearMap.mem_ker]
  exact and_congr_right (fun _ => ⟨fun h x hx => congrFun h ⟨x, hx⟩,
    fun h => funext (fun x => h x.1 x.2)⟩)

private theorem weighted_root_pos (t : Fin 9 → ℝ) (ht : ∀ i, 0 < t i) :
    0 < Real.sqrt (∑ i, t i ^ 2) :=
  Real.sqrt_pos.2 (Finset.sum_pos (fun i _ => pow_pos (ht i) _) Finset.univ_nonempty)

/-- Restricting a supported ambient eigenvector to a separated block preserves
the ambient eigenvalue, including the equations on omitted rows. -/
private theorem restrict_mem {t : Fin 9 → ℝ} (ht : ∀ i, 0 < t i)
    {C D : Finset (Q 9)} (hsep : Separated C D) {v : Q 9 → ℝ}
    (hv : v ∈ supportedWeightedEigenSpace t (C ∪ D)) :
    (fun x => if x ∈ C then v x else 0) ∈ supportedWeightedEigenSpace t C := by
  let u : Q 9 → ℝ := fun x => if x ∈ C then v x else 0
  let r := Real.sqrt (∑ i, t i ^ 2)
  obtain ⟨hvec, hout⟩ := (mem_supported_iff t (C ∪ D) v).mp hv
  have hrow (x : Q 9) (hx : x ∈ C) : weightedHuang t u x = r * u x := by
    have h := congrFun hvec x
    change weightedHuang t v x = r * v x at h
    rw [show u x = v x by simp [u, hx], ← h, weighted_apply, weighted_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : flip x i ∈ C
    · simp [u, hi]
    · have hd : flip x i ∉ D := fun hd => hsep.2 x hx _ hd (flip_adj x i)
      rw [hout _ (by simp [hi, hd])]
      simp [u, hi]
  have hdot : u ⬝ᵥ weightedHuang t u = u ⬝ᵥ (r • u) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ C
    · rw [hrow x hx]
      rfl
    · simp [u, hx]
  rw [dotProduct_smul, smul_eq_mul] at hdot
  exact (mem_supported_iff t C u).mpr
    ⟨eigen_of_rayleigh t u (weighted_root_pos t ht)
      (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (t i))) hdot.ge,
      fun x hx => by simp [u, hx]⟩

/-- In the switching gauge each selected row is an unsigned weighted neighbor sum. -/
private theorem switched_row {t : Fin 9 → ℝ} {C : Finset (Q 9)} {σ v : Q 9 → ℝ}
    (hs : IsSwitching C σ) (hv : ∀ x ∉ C, v x = 0) {x : Q 9} (hx : x ∈ C) :
    σ x * weightedHuang t v x = ∑ i, t i * (σ (flip x i) * v (flip x i)) := by
  rw [weighted_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : flip x i ∈ C
  · rw [hs.2 x hx _ hi (flip_adj x i)]
    linear_combination (t i * (σ (flip x i) * v (flip x i))) * switching_sq hs hx
  · simp [hv _ hi]

/-- On a connected balanced support, a top eigenvector that vanishes at one selected
vertex vanishes everywhere. -/
private theorem eq_zero_of_eval_zero {t : Fin 9 → ℝ} (ht : ∀ i, 0 < t i)
    {C : Finset (Q 9)} (hc : ((hypercube 9).induce (C : Set (Q 9))).Preconnected)
    (hb : IsBalanced C) {v : Q 9 → ℝ} (hv : v ∈ supportedWeightedEigenSpace t C)
    {x : Q 9} (hx : x ∈ C) : v x = 0 → v = 0 := by
  intro hz
  obtain ⟨σ, hs⟩ := hb
  obtain ⟨he, ho⟩ := (mem_supported_iff t C v).mp hv
  let u : Q 9 → ℝ := fun y => σ y * |v y|
  let r := Real.sqrt (∑ i, t i ^ 2)
  have huo : ∀ y ∉ C, u y = 0 := by
    intro y hy
    simp [u, ho y hy]
  have hsu (y : Q 9) : σ y * u y = |v y| := by
    by_cases hy : y ∈ C
    · change σ y * (σ y * |v y|) = |v y|
      rw [← mul_assoc, ← pow_two, switching_sq hs hy, one_mul]
    · simp [huo y hy, ho y hy]
  have hsq (y : Q 9) : u y * u y = v y * v y := by
    by_cases hy : y ∈ C
    · calc
        u y * u y = σ y ^ 2 * |v y| ^ 2 := by dsimp [u]; ring
        _ = v y * v y := by rw [switching_sq hs hy, sq_abs, one_mul, pow_two]
    · simp [huo y hy, ho y hy]
  have hnorm : u ⬝ᵥ u = v ⬝ᵥ v := Finset.sum_congr rfl (fun y _ => hsq y)
  have hdom : v ⬝ᵥ weightedHuang t v ≤ u ⬝ᵥ weightedHuang t u := by
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : y ∈ C
    · have hsquare := switching_sq hs hy
      calc
        v y * weightedHuang t v y =
            (σ y * v y) * (σ y * weightedHuang t v y) := by
          linear_combination (-v y * weightedHuang t v y) * hsquare
        _ ≤ |v y| * (σ y * weightedHuang t u y) := by
          rw [switched_row hs ho hy, switched_row hs huo hy, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          rw [hsu]
          have habs (z : Q 9) : |σ z * v z| = |v z| := by
            by_cases hzC : z ∈ C
            · rcases hs.1 z hzC with hsign | hsign <;> simp [hsign]
            · simp [ho z hzC]
          rw [mul_left_comm (σ y * v y), mul_left_comm |v y|]
          apply mul_le_mul_of_nonneg_left _ (ht i).le
          simpa only [abs_mul, habs] using le_abs_self ((σ y * v y) * (σ (flip y i) * v (flip y i)))
        _ = u y * weightedHuang t u y := by dsimp [u]; ring
    · simp [ho y hy, huo y hy]
  have hue : weightedHuang t u = r • u := by
    apply eigen_of_rayleigh t u (weighted_root_pos t ht)
      (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (t i)))
    rw [he, dotProduct_smul, smul_eq_mul, ← hnorm] at hdom
    exact hdom
  have step {y z : (C : Set (Q 9))}
      (hyz : ((hypercube 9).induce (C : Set (Q 9))).Adj y z)
      (hy : v y = 0) : v z = 0 := by
    have hrow := switched_row (t := t) hs huo y.property
    have hr := congrFun hue y.val
    change weightedHuang t u y = r * u y at hr
    have huy : u y = 0 := by simp [u, hy]
    simp only [hr, huy, mul_zero, hsu] at hrow
    obtain ⟨i, hi⟩ := adjacent_exists_flip (show (hypercube 9).Adj y.val z.val from hyz)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (ht i).le (abs_nonneg (v (flip y.val i))))).mp
      hrow.symm i (Finset.mem_univ i)
    change v z.val = 0
    rw [hi]
    exact abs_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ht i).ne')
  funext y
  change v y = 0
  by_cases hy : y ∈ C
  · obtain ⟨p⟩ := hc ⟨x, hx⟩ ⟨y, hy⟩
    have follow {a b : (C : Set (Q 9))}
        (p : ((hypercube 9).induce (C : Set (Q 9))).Walk a b) : v a = 0 → v b = 0 := by
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun ha => ih (step h ha)
    exact follow p hz
  · exact ho y hy

private theorem finrank_le_one {t : Fin 9 → ℝ} (ht : ∀ i, 0 < t i)
    {C : Finset (Q 9)} (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hb : IsBalanced C) : Module.finrank ℝ (supportedWeightedEigenSpace t C) ≤ 1 := by
  obtain ⟨x⟩ := hc.nonempty
  let eval : supportedWeightedEigenSpace t C →ₗ[ℝ] ℝ :=
    (LinearMap.proj x.val).comp (supportedWeightedEigenSpace t C).subtype
  have hinj : Function.Injective eval := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    exact Subtype.ext (eq_zero_of_eval_zero ht hc.preconnected hb v.property x.property hv)
  simpa using LinearMap.finrank_le_finrank_of_injective (f := eval) hinj

/-- Each of two separated connected balanced components on 258 vertices supports a
nonzero ambient eigenvector at the positive weighted Huang bound. -/
theorem exists_supported_eigenvectors (t : Fin 9 → ℝ) (ht : ∀ i, 0 < t i)
    {C D : Finset (Q 9)} (hcard : (C ∪ D).card = 258) (hsep : Separated C D)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    (∃ v ∈ supportedWeightedEigenSpace t C, v ≠ 0) ∧
      (∃ v ∈ supportedWeightedEigenSpace t D, v ≠ 0) := by
  let restrict (A B : Finset (Q 9)) (h : Separated A B) :
      supportedWeightedEigenSpace t (A ∪ B) →ₗ[ℝ] supportedWeightedEigenSpace t A :=
    { toFun := fun v => ⟨fun x => if x ∈ A then v.val x else 0, restrict_mem ht h v.property⟩
      map_add' := fun v w => Subtype.ext (funext fun x => by
        by_cases hx : x ∈ A <;> simp [hx])
      map_smul' := fun a v => Subtype.ext (funext fun x => by
        by_cases hx : x ∈ A <;> simp [hx]) }
  let rc := restrict C D hsep
  let rd : supportedWeightedEigenSpace t (C ∪ D) →ₗ[ℝ] supportedWeightedEigenSpace t D :=
    (restrict D C (Separated.symm hsep)).comp (Submodule.inclusion (by rw [Finset.union_comm]))
  let split := rc.prod rd
  have hinj : Function.Injective split := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply Subtype.ext
    funext x
    change v.val x = 0
    by_cases hx : x ∈ C ∪ D
    · rcases Finset.mem_union.mp hx with hxC | hxD
      · have h := congrArg (fun w => (Prod.fst w).val x) hv
        simpa [split, rc, restrict, hxC] using h
      · have h := congrArg (fun w => (Prod.snd w).val x) hv
        simpa [split, rd, restrict, hxD] using h
    · exact ((mem_supported_iff t (C ∪ D) v.val).mp v.property).2 x hx
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := split) hinj
  rw [Module.finrank_prod] at hdim
  have htwo := two_le_finrank_supportedWeightedEigenSpace t ht (C ∪ D) hcard
  have hC := finrank_le_one ht hc hbC
  have hD := finrank_le_one ht hd hbD
  have exists_of_pos (A : Finset (Q 9))
      (h : 0 < Module.finrank ℝ (supportedWeightedEigenSpace t A)) :
      ∃ v ∈ supportedWeightedEigenSpace t A, v ≠ 0 := by
    let := Module.nontrivial_of_finrank_pos h
    obtain ⟨v, hv⟩ := exists_ne (0 : supportedWeightedEigenSpace t A)
    exact ⟨v.val, v.property, fun he => hv (Subtype.ext he)⟩
  exact ⟨exists_of_pos C (by omega), exists_of_pos D (by omega)⟩

/-- Every pair of distinct axes occurs together at a vertex of each component. -/
theorem axes_meet (i j : Fin 9) (hij : i ≠ j)
    {C D : Finset (Q 9)} (hcard : (C ∪ D).card = 258) (hsep : Separated C D)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    (∃ x ∈ C, flip x i ∈ C ∧ flip x j ∈ C) ∧
      (∃ x ∈ D, flip x i ∈ D ∧ flip x j ∈ D) := by
  let t : Fin 9 → ℝ := fun k => if k = i ∨ k = j then 1 else 1 / 100
  have ht (k : Fin 9) : 0 < t k := by dsimp [t]; split <;> norm_num
  have hti : t i = 1 := by simp [t]
  have htj : t j = 1 := by simp [t]
  let R : Finset (Fin 9) := (Finset.univ.erase i).erase j
  have hju : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  have hR : R.card = 7 := by
    dsimp only [R]
    rw [Finset.card_erase_of_mem hju, Finset.card_erase_of_mem (Finset.mem_univ i)]
    decide
  have hsplit (f : Fin 9 → ℝ) : ∑ k, f k = (∑ k ∈ R, f k) + f j + f i := by
    dsimp only [R]
    rw [Finset.sum_erase_add _ f hju, Finset.sum_erase_add _ f (Finset.mem_univ i)]
  let r := Real.sqrt (∑ k, t k ^ 2)
  have hr : 107 / 100 < r := by
    have hq : r ^ 2 = ∑ k, t k ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg (t k))
    rw [hsplit, hti, htj] at hq
    have htail : 0 ≤ ∑ k ∈ R, t k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg (t k)
    by_contra! h
    have hsq := mul_self_le_mul_self (weighted_root_pos t ht).le h
    nlinarith
  have meet (A : Finset (Q 9)) {v : Q 9 → ℝ}
      (hv : v ∈ supportedWeightedEigenSpace t A) (hn : v ≠ 0) :
      ∃ x ∈ A, flip x i ∈ A ∧ flip x j ∈ A := by
    obtain ⟨he, ho⟩ := (mem_supported_iff t A v).mp hv
    obtain ⟨x, _, hm⟩ := Finset.exists_max_image Finset.univ (fun x => |v x|)
      Finset.univ_nonempty
    have hpos : 0 < |v x| := by
      by_contra! h
      apply hn
      funext y
      exact abs_eq_zero.mp (le_antisymm ((hm y (Finset.mem_univ y)).trans h) (abs_nonneg _))
    have hx : x ∈ A := by
      by_contra h
      simp [ho x h] at hpos
    by_contra h
    have hmiss : flip x i ∉ A ∨ flip x j ∉ A := by
      by_contra! hh
      exact h ⟨x, hx, hh⟩
    let a (k : Fin 9) := |t k * (huangMatrix 9 x (flip x k) * v (flip x k))|
    have ha (k : Fin 9) : a k = t k * |v (flip x k)| := by
      dsimp [a]
      rw [abs_mul, abs_of_pos (ht k), abs_mul, matrix_support, ite_eq_left (flip_adj x k), one_mul]
    have hpair : a j + a i ≤ |v x| := by
      rw [ha, ha, hti, htj, one_mul, one_mul]
      rcases hmiss with hi | hj
      · simpa [ho _ hi] using hm (flip x j) (Finset.mem_univ _)
      · simpa [ho _ hj] using hm (flip x i) (Finset.mem_univ _)
    have htail : ∑ k ∈ R, a k ≤ (7 / 100) * |v x| := by
      calc
        ∑ k ∈ R, a k ≤ ∑ _k ∈ R, (1 / 100 : ℝ) * |v x| := by
          apply Finset.sum_le_sum
          intro k hk
          rw [ha, show t k = 1 / 100 by
            have hk' := Finset.mem_erase.mp hk
            simp [t, hk'.1, (Finset.mem_erase.mp hk'.2).1]]
          exact mul_le_mul_of_nonneg_left (hm _ (Finset.mem_univ _)) (by norm_num)
        _ = _ := by rw [Finset.sum_const, hR, nsmul_eq_mul]; ring
    have hrow := congrFun he x
    change weightedHuang t v x = r * v x at hrow
    have habs : r * |v x| ≤ ∑ k, a k := by
      have hrpos : 0 < r := weighted_root_pos t ht
      rw [← abs_of_pos hrpos, ← abs_mul, ← hrow, weighted_apply]
      exact Finset.abs_sum_le_sum_abs _ _
    rw [hsplit] at habs
    have hle : r * |v x| ≤ (107 / 100) * |v x| := by linarith only [hpair, htail, habs]
    exact (not_le_of_gt (mul_lt_mul_of_pos_right hr hpos)) hle
  obtain ⟨⟨v, hv, hv0⟩, w, hw, hw0⟩ :=
    exists_supported_eigenvectors t ht hcard hsep hc hd hbC hbD
  exact ⟨meet C hv hv0, meet D hw hw0⟩

end
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangComponents
