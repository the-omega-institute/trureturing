/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Commuting coordinate averages on finite binary configurations. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Update

/-! Commuting coordinate averages on finite binary configurations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

private noncomputable def bitAvg (n : ℕ) (k : Fin n) :
    Module.End ℂ ((Fin n → Fin 2) → V) where
  toFun := fun f x => (2 : ℂ)⁻¹ • ∑ b : Fin 2, f (Function.update x k b)
  map_add' := by
    intro f g
    funext x
    simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add]
  map_smul' := by
    intro c f
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply, ← Finset.smul_sum]
    exact smul_comm _ _ _

private lemma bitAvg_idempotent (n : ℕ) (k : Fin n) :
    bitAvg (V := V) n k * bitAvg n k = bitAvg n k := by
  apply LinearMap.ext
  intro f
  funext x
  change (2 : ℂ)⁻¹ • (∑ b : Fin 2,
    (2 : ℂ)⁻¹ • ∑ c : Fin 2, f (Function.update (Function.update x k b) k c)) =
      (2 : ℂ)⁻¹ • ∑ b : Fin 2, f (Function.update x k b)
  simp only [Fin.sum_univ_two, Function.update_idem]
  module

private lemma bitAvg_commute (n : ℕ) (k l : Fin n) :
    Commute (bitAvg (V := V) n k) (bitAvg n l) := by
  by_cases h : k = l
  · subst l
    exact Commute.refl _
  · change bitAvg (V := V) n k * bitAvg n l = bitAvg n l * bitAvg n k
    apply LinearMap.ext
    intro f
    funext x
    change (2 : ℂ)⁻¹ • (∑ b : Fin 2,
      (2 : ℂ)⁻¹ • ∑ c : Fin 2, f (Function.update (Function.update x k b) l c)) =
      (2 : ℂ)⁻¹ • (∑ b : Fin 2,
      (2 : ℂ)⁻¹ • ∑ c : Fin 2, f (Function.update (Function.update x l b) k c))
    simp only [← Finset.smul_sum, Function.update_comm h]
    rw [Finset.sum_comm]

noncomputable def avg (n : ℕ) (s : Finset (Fin n)) :
    Module.End ℂ ((Fin n → Fin 2) → V) :=
  s.noncommProd (bitAvg n) (by intro i hi j hj hij; exact bitAvg_commute n i j)

lemma avg_empty (n : ℕ) : avg (V := V) n ∅ = 1 :=
  Finset.noncommProd_empty _ _

private lemma avg_insert (n : ℕ) (s : Finset (Fin n)) (k : Fin n) (hk : k ∉ s) :
    avg (V := V) n (insert k s) = bitAvg n k * avg n s :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hk

private lemma bitAvg_mul_avg_of_mem (n : ℕ) (s : Finset (Fin n))
    (k : Fin n) (hk : k ∈ s) : bitAvg (V := V) n k * avg n s = avg n s := by
  have hs : avg (V := V) n s = bitAvg n k * avg n (s.erase k) := by
    rw [← avg_insert n (s.erase k) k (Finset.notMem_erase k s), Finset.insert_erase hk]
  rw [hs, ← mul_assoc, bitAvg_idempotent]

lemma avg_mul (n : ℕ) (s t : Finset (Fin n)) :
    avg (V := V) n s * avg n t = avg n (s ∪ t) := by
  induction s using Finset.induction_on with
  | empty => rw [avg_empty, one_mul, Finset.empty_union]
  | @insert k s hk ih =>
    rw [avg_insert n s k hk, mul_assoc, ih, Finset.insert_union]
    by_cases h : k ∈ s ∪ t
    · rw [Finset.insert_eq_of_mem h]
      exact bitAvg_mul_avg_of_mem n _ k h
    · exact (avg_insert n _ k h).symm

lemma avg_commute (n : ℕ) (s t : Finset (Fin n)) :
    Commute (avg (V := V) n s) (avg n t) := by
  delta avg
  apply Finset.noncommProd_commute
  intro j hj
  exact (Finset.noncommProd_commute s (bitAvg n)
    (by intro i hi l hl hil; exact bitAvg_commute n i l)
    (bitAvg n j) (by intro i hi; exact bitAvg_commute n j i)).symm

lemma avg_pair_apply (n : ℕ) (k l : Fin n) (h : k ≠ l)
    (f : (Fin n → Fin 2) → V) (x : Fin n → Fin 2) :
    avg n {k, l} f x = (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
      f (Function.update (Function.update x k b) l c) := by
  rw [avg_insert n {l} k (by simpa only [Finset.mem_singleton] using h)]
  have hs : avg (V := V) n {l} = bitAvg n l := Finset.noncommProd_singleton _ _
  rw [hs]
  change (2 : ℂ)⁻¹ • (∑ b : Fin 2,
    (2 : ℂ)⁻¹ • ∑ c : Fin 2, f (Function.update (Function.update x k b) l c)) = _
  rw [← Finset.smul_sum, smul_smul]
  norm_num

lemma avg_map (n : ℕ) (s : Finset (Fin n)) (l : V →ₗ[ℂ] W)
    (f : (Fin n → Fin 2) → V) (x : Fin n → Fin 2) :
    l (avg n s f x) = avg n s (fun y => l (f y)) x := by
  induction s using Finset.induction_on generalizing x with
  | empty => rw [avg_empty, avg_empty]; rfl
  | @insert k s hk ih =>
    rw [avg_insert n s k hk, avg_insert n s k hk]
    change l ((2 : ℂ)⁻¹ • ∑ b : Fin 2, avg n s f (Function.update x k b)) =
      (2 : ℂ)⁻¹ • ∑ b : Fin 2, avg n s (fun y => l (f y)) (Function.update x k b)
    rw [map_smul, map_sum]
    simp only [ih]

private lemma avg_fill (n : ℕ) (s : Finset (Fin n))
    (f : (Fin n → Fin 2) → V) (x : Fin n → Fin 2) :
    avg n s f x = ((2 : ℂ) ^ s.card)⁻¹ •
      ∑ b : ({j // j ∈ s} → Fin 2), f (Function.updateFinset x s b) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    rw [avg_empty]
    have hf (b : {j : Fin n // j ∈ (∅ : Finset (Fin n))} → Fin 2) :
        Function.updateFinset x ∅ b = x := Function.updateFinset_empty
    simp only [hf, Finset.card_empty, pow_zero, inv_one, one_smul]
    simp
  | @insert k s hk ih =>
    let e : ({j // j ∈ insert k s} → Fin 2) ≃
        Fin 2 × ({j // j ∈ s} → Fin 2) :=
      { toFun := fun d => (d ⟨k, Finset.mem_insert_self k s⟩,
          fun j => d ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
        invFun := fun z j => if hj : j.val = k then z.1
          else z.2 ⟨j.val, (Finset.mem_insert.mp j.property).resolve_left hj⟩
        left_inv := by
          intro d
          funext j
          dsimp
          split_ifs with hj
          · exact congrArg d (Subtype.ext hj.symm)
          · rfl
        right_inv := by
          intro z
          apply Prod.ext
          · simp
          · funext j
            have hj : j.val ≠ k := fun h => hk (h ▸ j.property)
            simp [hj] }
    have hsum : (∑ d : ({j // j ∈ insert k s} → Fin 2),
        f (Function.updateFinset x (insert k s) d)) =
        ∑ z : Fin 2 × ({j // j ∈ s} → Fin 2),
          f (Function.updateFinset (Function.update x k z.1) s z.2) := by
      apply Fintype.sum_equiv e
      intro d
      congr 1
      funext j
      by_cases hj : j = k
      · subst j
        (delta Function.updateFinset; simp [hk, e])
      · by_cases hs : j ∈ s <;>
          (delta Function.updateFinset; simp [hs, hj, e])
    rw [avg_insert n s k hk]
    change (2 : ℂ)⁻¹ • (∑ b : Fin 2, avg n s f (Function.update x k b)) = _
    simp only [ih]
    rw [← Finset.smul_sum, smul_smul, Finset.card_insert_of_notMem hk,
      pow_succ, mul_inv_rev, hsum, Fintype.sum_prod_type]

lemma avg_univ (n : ℕ) (f : (Fin n → Fin 2) → V) (x : Fin n → Fin 2) :
    avg n Finset.univ f x = ((2 : ℂ) ^ n)⁻¹ • ∑ y : Fin n → Fin 2, f y := by
  classical
  rw [avg_fill, Finset.card_univ, Fintype.card_fin]
  congr 1
  let e : ({j : Fin n // j ∈ (Finset.univ : Finset (Fin n))} → Fin 2) ≃
      (Fin n → Fin 2) :=
    { toFun := fun b j => b ⟨j, Finset.mem_univ j⟩
      invFun := fun b j => b j.val
      left_inv := by intro b; funext j; rfl
      right_inv := by intro b; rfl }
  apply Fintype.sum_equiv e
  intro b
  congr 1
  funext j
  (delta Function.updateFinset; simp [e])

end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
