/- GID: D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.claim; result=D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.result; claim=D5/S3/Quantum/Entanglement/Witness/DensityTensorNuclearNormEqualityRefutation.claim
   digest: A flagged Bell mixture refutes the pure-state nuclear-norm equality case. -/

import D5.S3.Quantum.PureState.PureStateHandshake

/-! Complex nuclear norms of coefficient tensors and a mixed equality-case counterexample. -/

set_option linter.style.longLine false

noncomputable section

open scoped BigOperators ComplexOrder TensorProduct
open Matrix

namespace D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Mathlib's projective tensor norm in the product of the standard Euclidean bases. -/
def nuclearNorm {κ : Type*} [Fintype κ] (m : κ → ℕ)
    (t : ((j : κ) → Fin (m j)) → ℂ) : ℝ := by
  classical
  exact ‖(Basis.piTensorProduct (fun j => PiLp.basisFun 2 ℂ (Fin (m j)))).equivFun.symm t‖

/-- Maximal nuclear norm among Euclidean unit tensors. -/
def alpha {κ : Type*} [Fintype κ] (m : κ → ℕ) : ℝ := by
  classical
  exact sSup {s : ℝ | ∃ t : ((j : κ) → Fin (m j)) → ℂ,
    ‖WithLp.toLp 2 t‖ = 1 ∧ s = nuclearNorm m t}

/-- The row and column modes of a matrix, regarded as separate tensor factors. -/
def densityTensor {d : ℕ} {n : Fin d → ℕ}
    (a : Matrix ((j : Fin d) → Fin (n j)) ((j : Fin d) → Fin (n j)) ℂ) :
    ((j : Fin d ⊕ Fin d) → Fin (Sum.elim n n j)) → ℂ :=
  fun i => a (fun j => i (Sum.inl j)) (fun j => i (Sum.inr j))

/-- The equality-case conjecture of Derksen, Friedland, Lim and Wang. -/
def claim : Prop :=
  ∀ (d : ℕ) (n : Fin d → ℕ)
    (a : Matrix ((j : Fin d) → Fin (n j)) ((j : Fin d) → Fin (n j)) ℂ),
    a.PosSemidef → a.trace = 1 →
    nuclearNorm (Sum.elim n n) (densityTensor a) = alpha n ^ 2 →
    ∃ t : ((j : Fin d) → Fin (n j)) → ℂ,
      ‖WithLp.toLp 2 t‖ = 1 ∧ nuclearNorm n t = alpha n ∧ a = vecMulVec t (star t)

private lemma tensor_coordinates {κ : Type*} [Fintype κ] (m : κ → ℕ)
    (x : (j : κ) → EuclideanSpace ℂ (Fin (m j))) :
    (Basis.piTensorProduct (fun j => PiLp.basisFun 2 ℂ (Fin (m j)))).equivFun
      (PiTensorProduct.tprod ℂ x) = fun i => ∏ j, x j (i j) := by
  classical
  ext i
  exact Basis.piTensorProduct_repr_tprod_apply _ x i

private lemma nuclear_le {κ : Type*} [Fintype κ] (m : κ → ℕ)
    (t : ((j : κ) → Fin (m j)) → ℂ) (r : ℕ)
    (x : Fin r → (j : κ) → Fin (m j) → ℂ)
    (hx : t = fun i => ∑ a, ∏ j, x a j (i j)) :
    nuclearNorm m t ≤ ∑ a, ∏ j, ‖WithLp.toLp 2 (x a j)‖ := by
  classical
  let b := Basis.piTensorProduct (fun j => PiLp.basisFun 2 ℂ (Fin (m j)))
  have he : b.equivFun.symm t =
      ∑ a, PiTensorProduct.tprod ℂ (fun j => WithLp.toLp 2 (x a j)) := by
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply, map_sum]
    ext i
    simpa only [Finset.sum_apply, b, tensor_coordinates, PiLp.toLp_apply] using congrFun hx i
  change ‖b.equivFun.symm t‖ ≤ _
  rw [he]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
    PiTensorProduct.projectiveSeminorm_tprod_le (fun j => WithLp.toLp 2 (x a j)))

private lemma dual_bound {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (t : ((j : κ) → Fin (m j)) → ℂ)
    (s : ((((j : κ) → Fin (m j)) → ℂ)) →ₗ[ℂ] ℂ)
    (hs : ∀ x : (j : κ) → Fin (m j) → ℂ,
      ‖s (fun i => ∏ j, x j (i j))‖ ≤ ∏ j, ‖WithLp.toLp 2 (x j)‖) :
    ‖s t‖ ≤ nuclearNorm m t := by
  classical
  let b := Basis.piTensorProduct (fun j => PiLp.basisFun 2 ℂ (Fin (m j)))
  let l := s.comp b.equivFun.toLinearMap
  let f := l.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hf (x : (j : κ) → EuclideanSpace ℂ (Fin (m j))) :
      ‖f x‖ ≤ 1 * ∏ j, ‖x j‖ := by
    change ‖s (b.equivFun (PiTensorProduct.tprod ℂ x))‖ ≤ _
    rw [tensor_coordinates]
    simpa only [one_mul, WithLp.toLp_ofLp] using hs (fun j => WithLp.ofLp (x j))
  let fc := f.mkContinuous 1 hf
  have hn : ‖fc‖ ≤ 1 := f.mkContinuous_norm_le zero_le_one hf
  have heval : PiTensorProduct.lift fc.toMultilinearMap (b.equivFun.symm t) = s t := by
    change PiTensorProduct.lift (PiTensorProduct.lift.symm l) (b.equivFun.symm t) = s t
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg s (b.equivFun.apply_symm_apply t)
  change ‖s t‖ ≤ ‖b.equivFun.symm t‖
  rw [← heval]
  exact (PiTensorProduct.norm_eval_le_projectiveSeminorm fc _).trans
    ((mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _))

private lemma row_bound (n : ℕ)
    (t : ((j : Fin 2) → Fin ((![2, n] : Fin 2 → ℕ) j)) → ℂ) :
    nuclearNorm ((![2, n] : Fin 2 → ℕ)) t ≤ Real.sqrt 2 * ‖WithLp.toLp 2 t‖ := by
  classical
  let m := (![2, n] : Fin 2 → ℕ)
  let e : ((j : Fin 2) → Fin (m j)) ≃ Fin 2 × Fin n := piFinTwoEquiv _
  let rows : Fin 2 → Fin n → ℂ := fun a b => t (e.symm (a, b))
  let x : Fin 2 → (j : Fin 2) → Fin (m j) → ℂ := fun a =>
    Fin.cons (fun b => if b = a then 1 else 0) (Fin.cons (rows a) (fun j => Fin.elim0 j))
  have hx : t = fun i => ∑ a, ∏ j, x a j (i j) := by
    funext i
    have hi : e.symm (i 0, i 1) = i := e.symm_apply_apply i
    have hi0 : i 0 = (0 : Fin 2) ∨ i 0 = (1 : Fin 2) :=
      (show ∀ a : Fin 2, a = 0 ∨ a = 1 by decide) (i 0)
    rcases hi0 with h | h
    · simpa [Fin.sum_univ_two, Fin.prod_univ_two, x, h, rows] using congrArg t hi.symm
    · simpa [Fin.sum_univ_two, Fin.prod_univ_two, x, h, rows] using congrArg t hi.symm
  have hc : (∑ a, ∏ j, ‖WithLp.toLp 2 (x a j)‖) = ∑ a, ‖WithLp.toLp 2 (rows a)‖ := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Fin.prod_univ_two]
    change ‖WithLp.toLp 2 (fun b : Fin 2 => if b = a then 1 else 0)‖ *
      ‖WithLp.toLp 2 (rows a)‖ = ‖WithLp.toLp 2 (rows a)‖
    simp only [← Pi.single_apply, PiLp.toLp_single, PiLp.norm_single, norm_one, one_mul]
  have hn : ∑ a, ‖WithLp.toLp 2 (rows a)‖ ^ 2 = ‖WithLp.toLp 2 t‖ ^ 2 := by
    simp_rw [PiLp.norm_sq_eq_of_L2]
    rw [← e.symm.sum_comp (fun i => ‖t i‖ ^ 2), Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a, ∏ j, ‖WithLp.toLp 2 (x a j)‖ := nuclear_le m t 2 x hx
    _ = ∑ a, ‖WithLp.toLp 2 (rows a)‖ := hc
    _ ≤ Real.sqrt 2 * Real.sqrt (∑ a, ‖WithLp.toLp 2 (rows a)‖ ^ 2) := by
      simpa [Fin.sum_univ_two] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin 2 => (1 : ℝ))
          (fun a => ‖WithLp.toLp 2 (rows a)‖)
    _ = Real.sqrt 2 * ‖WithLp.toLp 2 t‖ := by rw [hn, Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 t))]

private lemma bell_bound (x : Fin 2 → ℂ) (y : Fin 4 → ℂ) :
    ‖x 0 * y 0 + x 1 * y 1‖ ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  simpa [EuclideanSpace.inner_toLp_toLp, dotProduct, PiLp.norm_eq_of_L2, PiLp.toLp_apply,
    Fin.sum_univ_succ, mul_comm] using
      norm_inner_le_norm (𝕜 := ℂ)
        (WithLp.toLp 2 (![star (x 0), star (x 1), 0, 0] : Fin 4 → ℂ))
        (WithLp.toLp 2 y)

private lemma flag_bound (x z : Fin 2 → ℂ) (y w : Fin 4 → ℂ) :
    ‖(x 0 * y 0 + x 1 * y 1) * (z 0 * w 0 + z 1 * w 1) +
      (x 0 * y 2 + x 1 * y 3) * (z 0 * w 2 + z 1 * w 3)‖ ≤
      ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ * ‖WithLp.toLp 2 z‖ * ‖WithLp.toLp 2 w‖ := by
  let a : Fin 2 → Fin 2 → ℂ := fun b i => y ⟨i.val + 2 * b.val, by omega⟩
  let c : Fin 2 → Fin 2 → ℂ := fun b i => w ⟨i.val + 2 * b.val, by omega⟩
  have hy : ∑ b, ‖WithLp.toLp 2 (a b)‖ ^ 2 = ‖WithLp.toLp 2 y‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    dsimp [a]
    ring
  have hw : ∑ b, ‖WithLp.toLp 2 (c b)‖ ^ 2 = ‖WithLp.toLp 2 w‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    dsimp [c]
    ring
  have hcs : ∑ b, ‖WithLp.toLp 2 (a b)‖ * ‖WithLp.toLp 2 (c b)‖ ≤ ‖WithLp.toLp 2 y‖ * ‖WithLp.toLp 2 w‖ := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun b => ‖WithLp.toLp 2 (a b)‖) (fun b => ‖WithLp.toLp 2 (c b)‖)
    rwa [hy, hw, Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 y)),
      Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 w))] at h
  have hb (b : Fin 2) :
      ‖(∑ i, x i * a b i) * (∑ i, z i * c b i)‖ ≤
        ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 z‖ * (‖WithLp.toLp 2 (a b)‖ * ‖WithLp.toLp 2 (c b)‖) := by
    rw [norm_mul]
    have hx : ‖∑ i, x i * a b i‖ ≤
        ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 (a b)‖ := by
      simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply,
        star_star, PiLp.norm_eq_of_L2, PiLp.toLp_apply, norm_star, mul_comm] using
          norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 (star x)) (WithLp.toLp 2 (a b))
    have hz : ‖∑ i, z i * c b i‖ ≤
        ‖WithLp.toLp 2 z‖ * ‖WithLp.toLp 2 (c b)‖ := by
      simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply,
        star_star, PiLp.norm_eq_of_L2, PiLp.toLp_apply, norm_star, mul_comm] using
          norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 (star z)) (WithLp.toLp 2 (c b))
    convert mul_le_mul hx hz
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) using 1; ring
  calc
    _ = ‖∑ b, (∑ i, x i * a b i) * (∑ i, z i * c b i)‖ := by
      simp only [Fin.sum_univ_two]
      rfl
    _ ≤ ∑ b, ‖(∑ i, x i * a b i) * (∑ i, z i * c b i)‖ := norm_sum_le _ _
    _ ≤ ∑ b, ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 z‖ * (‖WithLp.toLp 2 (a b)‖ * ‖WithLp.toLp 2 (c b)‖) :=
      Finset.sum_le_sum fun b _ => hb b
    _ = ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 z‖ * ∑ b, ‖WithLp.toLp 2 (a b)‖ * ‖WithLp.toLp 2 (c b)‖ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 z‖ * (‖WithLp.toLp 2 y‖ * ‖WithLp.toLp 2 w‖) :=
      mul_le_mul_of_nonneg_left hcs (mul_nonneg (norm_nonneg (WithLp.toLp 2 x)) (norm_nonneg (WithLp.toLp 2 z)))
    _ = _ := by ring

private lemma pure_idempotent {ι : Type*} [Fintype ι] (t : ι → ℂ)
    (ht : ‖WithLp.toLp 2 t‖ = 1) :
    vecMulVec t (star t) * vecMulVec t (star t) = vecMulVec t (star t) := by
  have hd : star t ⬝ᵥ t = (1 : ℂ) := by
    rw [dotProduct_comm]
    have hnorm : ∑ i, ‖t i‖ ^ 2 = 1 := by
      simpa only [ht, PiLp.toLp_apply, one_pow] using
        (PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) (WithLp.toLp 2 t)).symm
    simpa only [EuclideanSpace.inner_toLp_toLp, ← RCLike.ofReal_pow,
      PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply, hnorm, RCLike.ofReal_one] using
        inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 t)
  have h := (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake t hd 0).1
  change vecMulVec t (star t) * vecMulVec t (star t) = vecMulVec t (star t) at h
  exact h

set_option maxHeartbeats 2000000 in
-- The finite counterexample expands eight rank-one terms across four tensor modes.
/-- A mixed density tensor attains the conjectured pure-state maximum. -/
theorem result : ¬ claim := by
  classical
  intro hc
  let n : Fin 2 → ℕ := ![2, 4]
  let e : ((j : Fin 2) → Fin (n j)) ≃ Fin 2 × Fin 4 := piFinTwoEquiv _
  have he0 (p : Fin 2 × Fin 4) : e.symm p 0 = p.1 := rfl
  have he1 (p : Fin 2 × Fin 4) : e.symm p 1 = p.2 := rfl
  let v : Fin 2 → ((j : Fin 2) → Fin (n j)) → ℂ := fun b i =>
    if (e i).2.val = (e i).1.val + 2 * b.val then (Real.sqrt 2 : ℂ)⁻¹ else 0
  let a := (1 / 2 : ℂ) • (vecMulVec (v 0) (star (v 0)) + vecMulVec (v 1) (star (v 1)))
  have hroot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hrootc : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast hroot
  have hrootcne : (Real.sqrt 2 : ℂ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hrootpos)
  have hcoeff : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, hrootc]
    norm_num
  have hcoeffnorm : ‖(Real.sqrt 2 : ℂ)⁻¹‖ ^ 2 = 1 / 2 := by
    rw [← norm_pow, hcoeff]
    norm_num
  have hv : ‖WithLp.toLp 2 (v 0)‖ = 1 := by
    rw [PiLp.norm_eq_of_L2, ← e.symm.sum_comp (fun i => ‖v 0 i‖ ^ 2)]
    simp only [Fintype.sum_prod_type, v, Equiv.apply_symm_apply]
    norm_num [Fin.sum_univ_succ, hcoeffnorm]
  let sb : ((((j : Fin 2) → Fin (n j)) → ℂ)) →ₗ[ℂ] ℂ :=
    LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (e.symm (0, 0)) +
      LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (e.symm (1, 1))
  have hsb : ∀ x : (j : Fin 2) → Fin (n j) → ℂ,
      ‖sb (fun i => ∏ j, x j (i j))‖ ≤ ∏ j, ‖WithLp.toLp 2 (x j)‖ := by
    intro x
    simp only [sb, LinearMap.add_apply, LinearMap.proj_apply, Fin.prod_univ_two,
      he0, he1]
    change ‖x 0 (0 : Fin 2) * x 1 (0 : Fin 4) +
      x 0 (1 : Fin 2) * x 1 (1 : Fin 4)‖ ≤ _
    exact bell_bound (x 0) (x 1)
  have hsbv : ‖sb (v 0)‖ = Real.sqrt 2 := by
    change ‖v 0 (e.symm (0, 0)) + v 0 (e.symm (1, 1))‖ = _
    simp only [v, Equiv.apply_symm_apply]
    norm_num only [Fin.val_zero, Fin.val_one, mul_zero, add_zero, ite_true]
    have heq : (Real.sqrt 2 : ℂ)⁻¹ + (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) := by
      apply (mul_left_injective₀ hrootcne)
      norm_num only [add_mul, inv_mul_cancel₀ hrootcne, ← sq, hrootc]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrootpos]
  have hb : nuclearNorm n (v 0) = Real.sqrt 2 := by
    apply le_antisymm
    · simpa [n, hv] using row_bound 4 (v 0)
    · rw [← hsbv]
      exact dual_bound n (v 0) sb hsb
  have halpha : alpha n = Real.sqrt 2 := by
    have hbound : ∀ s ∈ {s : ℝ | ∃ t : ((j : Fin 2) → Fin (n j)) → ℂ,
        ‖WithLp.toLp 2 t‖ = 1 ∧ s = nuclearNorm n t}, s ≤ Real.sqrt 2 := by
      rintro s ⟨t, ht, rfl⟩
      simpa only [ht, mul_one] using row_bound 4 t
    let ic : Fintype ((j : Fin 2) → Fin (n j)) :=
      @Pi.instFintype (Fin 2) (fun j => Fin (n j))
        (fun i j => Classical.propDecidable (i = j)) (Fin.fintype 2)
        (fun j => Fin.fintype (n j))
    change sSup {s : ℝ | ∃ t, (letI := ic; ‖WithLp.toLp 2 t‖) = 1 ∧ s = nuclearNorm n t} = _
    let istd : Fintype ((j : Fin 2) → Fin (n j)) :=
      @Pi.instFintype (Fin 2) (fun j => Fin (n j)) (instDecidableEqFin 2)
        (Fin.fintype 2) (fun j => Fin.fintype (n j))
    have hu (t : ((j : Fin 2) → Fin (n j)) → ℂ) :
        (letI := ic; ‖WithLp.toLp 2 t‖) = (letI := istd; ‖WithLp.toLp 2 t‖) :=
      congrArg (fun f : Fintype ((j : Fin 2) → Fin (n j)) =>
        letI := f; ‖WithLp.toLp 2 t‖) (Subsingleton.elim ic istd)
    simp_rw [hu]
    exact le_antisymm (csSup_le ⟨_, v 0, hv, rfl⟩ hbound)
      (le_csSup ⟨_, hbound⟩ ⟨v 0, hv, hb.symm⟩)
  have hpos : a.PosSemidef := by
    exact ((posSemidef_vecMulVec_self_star (v 0)).add
      (posSemidef_vecMulVec_self_star (v 1))).smul (by
        rw [Complex.nonneg_iff]
        norm_num)
  have hgram : ∀ b c : Fin 2, star (v b) ⬝ᵥ v c = if b = c then 1 else 0 := by
    intro b c
    change (∑ i, star (v b i) * v c i) = _
    rw [← e.symm.sum_comp (fun i => star (v b i) * v c i)]
    simp only [Fintype.sum_prod_type, v, Equiv.apply_symm_apply]
    fin_cases b <;> fin_cases c <;>
      norm_num [Fin.sum_univ_succ, ← sq, hcoeff]
  have htrace : a.trace = 1 := by
    change trace ((1 / 2 : ℂ) • _) = _
    rw [trace_smul, trace_add, trace_vecMulVec, trace_vecMulVec,
      dotProduct_comm (v 0), dotProduct_comm (v 1), hgram, hgram]
    norm_num
  have hupper : nuclearNorm (Sum.elim n n) (densityTensor a) ≤ 2 := by
    let q : Fin 8 ≃ Fin 2 × Fin 2 × Fin 2 := Fintype.equivOfCardEq (by decide)
    let x : Fin 8 → (j : Fin 2 ⊕ Fin 2) → Fin (Sum.elim n n j) → ℂ := fun r =>
      Sum.rec
        (Fin.cons (fun b => if b = (q r).2.1 then 1 / 4 else 0)
          (Fin.cons (fun b => if b = ⟨(q r).2.1.val + 2 * (q r).1.val, by change _ < 4; omega⟩
            then 1 else 0) (fun j => Fin.elim0 j)))
        (Fin.cons (fun b => if b = (q r).2.2 then 1 else 0)
          (Fin.cons (fun b => if b = ⟨(q r).2.2.val + 2 * (q r).1.val, by change _ < 4; omega⟩
            then 1 else 0) (fun j => Fin.elim0 j)))
    have hx : densityTensor a = fun i => ∑ r, ∏ j, x r j (i j) := by
      funext i
      rw [← q.symm.sum_comp (fun r => ∏ j, x r j (i j))]
      change (1 / 2 : ℂ) *
        ((if (i (.inl 1)).val = (i (.inl 0)).val + 2 * (0 : Fin 2).val
          then (Real.sqrt 2 : ℂ)⁻¹ else 0) * star
          (if (i (.inr 1)).val = (i (.inr 0)).val + 2 * (0 : Fin 2).val
            then (Real.sqrt 2 : ℂ)⁻¹ else 0) +
         (if (i (.inl 1)).val = (i (.inl 0)).val + 2 * (1 : Fin 2).val
          then (Real.sqrt 2 : ℂ)⁻¹ else 0) * star
          (if (i (.inr 1)).val = (i (.inr 0)).val + 2 * (1 : Fin 2).val
            then (Real.sqrt 2 : ℂ)⁻¹ else 0)) = _
      simp only [x, Equiv.apply_symm_apply, Fintype.sum_prod_type,
        Fintype.prod_sum_type, Fin.prod_univ_two, Fin.cons_zero, Fin.cons_one,
        Fin.sum_univ_two]
      generalize h₀ : (i (.inl 0) : Fin 2) = r
      generalize h₁ : (i (.inl 1) : Fin 4) = s
      generalize h₂ : (i (.inr 0) : Fin 2) = u
      generalize h₃ : (i (.inr 1) : Fin 4) = w
      fin_cases r <;> fin_cases s <;> fin_cases u <;> fin_cases w <;>
        norm_num [← sq, hcoeff]
    have hcost : (∑ r, ∏ j, ‖WithLp.toLp 2 (x r j)‖) = 2 := by
      have hterm (r : Fin 8) : (∏ j, ‖WithLp.toLp 2 (x r j)‖) = 1 / 4 := by
        rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two]
        change (‖WithLp.toLp 2 (fun b : Fin 2 => if b = (q r).2.1 then 1 / 4 else 0)‖ *
          ‖WithLp.toLp 2 (fun b : Fin 4 => if b =
            ⟨(q r).2.1.val + 2 * (q r).1.val, by omega⟩ then 1 else 0)‖) *
          (‖WithLp.toLp 2 (fun b : Fin 2 => if b = (q r).2.2 then 1 else 0)‖ *
          ‖WithLp.toLp 2 (fun b : Fin 4 => if b =
            ⟨(q r).2.2.val + 2 * (q r).1.val, by omega⟩ then 1 else 0)‖) = _
        simp only [← Pi.single_apply, PiLp.toLp_single, PiLp.norm_single]
        norm_num
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
    rw [← hcost]
    exact nuclear_le (Sum.elim n n) (densityTensor a) 8 x hx
  let sf : ((((j : Fin 2 ⊕ Fin 2) → Fin (Sum.elim n n j)) → ℂ)) →ₗ[ℂ] ℂ :=
    ∑ b : Fin 2, ∑ i : Fin 2, ∑ k : Fin 2,
      LinearMap.proj (R := ℂ) (φ := fun _ => ℂ)
        (Sum.rec (e.symm (i, ⟨i.val + 2 * b.val, by omega⟩))
        (e.symm (k, ⟨k.val + 2 * b.val, by omega⟩)))
  have hsf : ∀ x : (j : Fin 2 ⊕ Fin 2) → Fin (Sum.elim n n j) → ℂ,
      ‖sf (fun i => ∏ j, x j (i j))‖ ≤ ∏ j, ‖WithLp.toLp 2 (x j)‖ := by
    intro x
    have h := flag_bound (x (.inl 0)) (x (.inr 0)) (x (.inl 1)) (x (.inr 1))
    have he : sf (fun i => ∏ j, x j (i j)) =
        (x (.inl 0) (0 : Fin 2) * x (.inl 1) (0 : Fin 4) +
            x (.inl 0) (1 : Fin 2) * x (.inl 1) (1 : Fin 4)) *
          (x (.inr 0) (0 : Fin 2) * x (.inr 1) (0 : Fin 4) +
            x (.inr 0) (1 : Fin 2) * x (.inr 1) (1 : Fin 4)) +
        (x (.inl 0) (0 : Fin 2) * x (.inl 1) (2 : Fin 4) +
            x (.inl 0) (1 : Fin 2) * x (.inl 1) (3 : Fin 4)) *
          (x (.inr 0) (0 : Fin 2) * x (.inr 1) (2 : Fin 4) +
            x (.inr 0) (1 : Fin 2) * x (.inr 1) (3 : Fin 4)) := by
      simp only [sf, Fin.sum_univ_two, LinearMap.add_apply,
        LinearMap.proj_apply, Fintype.prod_sum_type, Fin.prod_univ_two, he0, he1]
      norm_num only [Fin.val_zero, Fin.val_one]
      simp only [show (⟨0, by decide⟩ : Fin 4) = (0 : Fin 4) from rfl,
        show (⟨1, by decide⟩ : Fin 4) = (1 : Fin 4) from rfl,
        show (⟨2, by decide⟩ : Fin 4) = (2 : Fin 4) from rfl,
        show (⟨3, by decide⟩ : Fin 4) = (3 : Fin 4) from rfl]
      ring
    rw [he]
    simpa only [Fintype.prod_sum_type, Fin.prod_univ_two, mul_assoc] using h
  have hsfa : ‖sf (densityTensor a)‖ = 2 := by
    have heval (b i k : Fin 2) :
        densityTensor a (Sum.rec (e.symm (i, ⟨i.val + 2 * b.val, by omega⟩))
          (e.symm (k, ⟨k.val + 2 * b.val, by omega⟩))) = 1 / 4 := by
      change (1 / 2 : ℂ) *
        (v 0 (e.symm (i, _)) * star (v 0 (e.symm (k, _))) +
         v 1 (e.symm (i, _)) * star (v 1 (e.symm (k, _)))) = _
      simp only [v, Equiv.apply_symm_apply]
      fin_cases b <;> fin_cases i <;> fin_cases k <;>
        norm_num [← sq, hcoeff]
    simp only [sf, LinearMap.add_apply, LinearMap.proj_apply,
      heval, Fin.sum_univ_two]
    norm_num
  have hn : nuclearNorm (Sum.elim n n) (densityTensor a) = alpha n ^ 2 := by
    rw [halpha, hroot]
    apply le_antisymm hupper
    rw [← hsfa]
    exact dual_bound (Sum.elim n n) (densityTensor a) sf hsf
  obtain ⟨t, ht, _, hat⟩ := hc 2 n a hpos htrace hn
  have hid : a * a = a := by
    rw [hat]
    exact pure_idempotent t ht
  have hhalf : a * a = (1 / 2 : ℂ) • a := by
    dsimp only [a]
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
      vecMulVec_mul_vecMulVec, hgram, one_smul, ite_eq_right (by decide :
        (0 : Fin 2) ≠ 1), ite_eq_right (by decide : (1 : Fin 2) ≠ 0), zero_smul,
      vecMulVec_zero, add_zero, zero_add, ite_true, smul_add, smul_zero]
  have hnonzero : a ≠ 0 := by
    intro hz
    rw [hz, trace_zero] at htrace
    norm_num at htrace
  apply hnonzero
  ext i j
  have hij := congrArg (fun b => b i j) (hid.symm.trans hhalf)
  change a i j = (1 / 2 : ℂ) * a i j at hij
  change a i j = 0
  linear_combination 2 * hij

end D5.S3.Quantum.Entanglement.Witness.DensityTensorNuclearNormEqualityRefutation
