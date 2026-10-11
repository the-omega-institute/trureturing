/- GID: D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/TwoInvolutionWordRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous words in two involutions with a four-dimensional invariant power space. -/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators
open Module Submodule

namespace D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank

variable {A : Type*} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A]

/-- All products of exactly the specified length, with the empty product included. -/
def products (u v : A) : ℕ → Set A
  | 0 => {1}
  | n + 1 => (fun x => u * x) '' products u v n ∪
      (fun x => v * x) '' products u v n

/-- The complex linear space of homogeneous operator words. -/
def wordSpace (u v : A) (n : ℕ) : Submodule ℂ A := span ℂ (products u v n)

/-- The first four powers of the relative product. -/
def powerSpace (u v : A) : Submodule ℂ A :=
  span ℂ (Set.range fun i : Fin 4 => (u * v) ^ i.val)

private def leftMap (u : A) : A →ₗ[ℂ] A where
  toFun x := u * x
  map_add' _ _ := mul_add _ _ _
  map_smul' _ _ := mul_smul_comm _ _ _

private def leftEquiv (u : A) (hu : u * u = 1) : A ≃ₗ[ℂ] A where
  toLinearMap := leftMap u
  invFun x := u * x
  left_inv x := by
    change u * (u * x) = x
    simp only [← mul_assoc, hu, one_mul]
  right_inv x := by
    change u * (u * x) = x
    simp only [← mul_assoc, hu, one_mul]

omit [Module.Finite ℂ A] in
private theorem space_succ (u v : A) (n : ℕ) :
    wordSpace u v (n + 1) = (wordSpace u v n).map (leftMap u) ⊔
      (wordSpace u v n).map (leftMap v) := by
  simp only [wordSpace, products, span_union, map_span, leftMap,
    LinearMap.coe_mk, AddHom.coe_mk]

private theorem rank_mono (u v : A) (hu : u * u = 1) :
    Monotone (fun n => finrank ℂ (wordSpace u v n)) := by
  apply monotone_nat_of_le_succ
  intro n
  have he := (leftEquiv u hu).finrank_map_eq (wordSpace u v n)
  calc
    finrank ℂ (wordSpace u v n) = finrank ℂ ((wordSpace u v n).map (leftMap u)) := he.symm
    _ ≤ finrank ℂ (wordSpace u v (n + 1)) := by
      apply Submodule.finrank_mono
      rw [space_succ]
      exact le_sup_left

omit [Module.Finite ℂ A] in
private theorem subset_power (u v : A) (i : Fin 4) :
    (u * v) ^ i.val ∈ powerSpace u v := subset_span ⟨i, rfl⟩

private theorem upper_four (u v : A) (hu : u * u = 1) (_hv : v * v = 1)
    (hR : ∀ x ∈ powerSpace u v, (u * v) * x ∈ powerSpace u v)
    (hD : ∀ x ∈ powerSpace u v, (v * u) * x ∈ powerSpace u v) (n : ℕ) :
    finrank ℂ (wordSpace u v n) ≤ 4 := by
  let P := powerSpace u v
  let Q := P.map (leftMap u)
  have hP : finrank ℂ P ≤ 4 := by
    exact (finrank_range_le_card (R := ℂ) (fun i : Fin 4 => (u * v) ^ i.val)).trans_eq
      (Fintype.card_fin 4)
  have hQ : finrank ℂ Q ≤ 4 := by
    exact ((leftEquiv u hu).finrank_map_eq P).le.trans hP
  have hUP : P.map (leftMap u) ≤ Q := le_rfl
  have hVP : P.map (leftMap v) ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(u * v) * x, hR x hx, ?_⟩
    change u * ((u * v) * x) = v * x
    simp only [← mul_assoc, hu, one_mul]
  have hUQ : Q.map (leftMap u) ≤ P := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    change u * (u * x) ∈ P
    rw [← mul_assoc, hu, one_mul]
    exact hx
  have hVQ : Q.map (leftMap v) ≤ P := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa only [leftMap, LinearMap.coe_mk, AddHom.coe_mk, ← mul_assoc] using hD x hx
  have hbound : ∀ k, wordSpace u v k ≤ P ∨ wordSpace u v k ≤ Q := by
    intro k
    induction k with
    | zero =>
      left
      apply span_le.mpr
      rintro x (rfl : x = 1)
      simpa using subset_power u v (0 : Fin 4)
    | succ k ih =>
      rw [space_succ]
      rcases ih with ih | ih
      · right
        exact sup_le ((map_mono ih).trans hUP) ((map_mono ih).trans hVP)
      · left
        exact sup_le ((map_mono ih).trans hUQ) ((map_mono ih).trans hVQ)
  rcases hbound n with hn | hn
  · exact (Submodule.finrank_mono hn).trans hP
  · exact (Submodule.finrank_mono hn).trans hQ

omit [Module.Finite ℂ A] in
private theorem word_mem (u v : A) {n : ℕ} {x : A}
    (hx : x ∈ products u v n) :
    u * x ∈ products u v (n + 1) ∧ v * x ∈ products u v (n + 1) :=
  ⟨Or.inl ⟨x, hx, rfl⟩, Or.inr ⟨x, hx, rfl⟩⟩

private theorem lower_small (u v : A) (hu : u * u = 1) (hv : v * v = 1)
    (hli : LinearIndependent ℂ (fun i : Fin 4 => (u * v) ^ i.val)) (n : ℕ) (hn : n ≤ 3) :
    n + 1 ≤ finrank ℂ (wordSpace u v n) := by
  have hi : ∀ m, m ≤ 4 →
      finrank ℂ (span ℂ (Set.range fun i : Fin m => (u * v) ^ i.val)) = m := by
    intro m hm
    have hinj : Function.Injective (fun i : Fin m =>
        (⟨i.val, lt_of_lt_of_le i.isLt hm⟩ : Fin 4)) := by
      intro i j h
      exact Fin.ext (congrArg (Fin.val (n := 4)) h)
    simpa only [Function.comp_def, Fintype.card_fin] using
      finrank_span_eq_card (R := ℂ) (hli.comp _ hinj)
  have h1 : (1 : A) ∈ products u v 0 := rfl
  have hU := (word_mem u v h1).1
  have hV := (word_mem u v h1).2
  simp only [mul_one] at hU hV
  have hUU := (word_mem u v hU).1
  have hUV := (word_mem u v hV).1
  have hVU := (word_mem u v hU).2
  have hUUU := (word_mem u v hUU).1
  have hUUV := (word_mem u v hUV).1
  have hUVU := (word_mem u v hVU).1
  have hVUV := (word_mem u v hUV).2
  have hRunit : (u * v) * (v * u) = 1 := by
    simp only [mul_assoc, ← mul_assoc v v u, hv, one_mul, hu]
  interval_cases n
  · have hsub : span ℂ (Set.range fun i : Fin 1 => (u * v) ^ i.val) ≤ wordSpace u v 0 := by
      apply span_le.mpr
      rintro x ⟨i, rfl⟩
      fin_cases i
      simpa only [pow_zero, wordSpace] using (subset_span (R := ℂ) h1)
    exact (hi 1 (by omega)).symm.le.trans (Submodule.finrank_mono hsub)
  · have hsub : span ℂ (Set.range fun i : Fin 2 => (u * v) ^ i.val) ≤
        (wordSpace u v 1).map (leftMap u) := by
      apply span_le.mpr
      rintro x ⟨i, rfl⟩
      fin_cases i
      · refine ⟨u, subset_span hU, ?_⟩
        simpa [leftMap] using hu
      · exact ⟨v, subset_span hV, by simp [leftMap]⟩
    have he := (leftEquiv u hu).finrank_map_eq (wordSpace u v 1)
    exact (hi 2 (by omega)).symm.le.trans ((Submodule.finrank_mono hsub).trans_eq he)
  · have hRu : (u * v) * (u * v) = (u * v) ^ 2 := by simp [pow_two]
    have hRinv : (v * u) * (u * v) = 1 := by
      simp only [mul_assoc, ← mul_assoc u u v, hu, one_mul, hv]
    have hsub : span ℂ (Set.range fun i : Fin 3 => (u * v) ^ i.val) ≤
        (wordSpace u v 2).map (leftMap (u * v)) := by
      apply span_le.mpr
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact ⟨v * u, subset_span hVU, by simpa [leftMap] using hRunit⟩
      · exact ⟨u * u, subset_span hUU, by simp [leftMap, hu]⟩
      · exact ⟨u * v, subset_span hUV, by simpa [leftMap] using hRu⟩
    let er := (leftEquiv v hv).trans (leftEquiv u hu)
    have he : finrank ℂ ((wordSpace u v 2).map (leftMap (u * v))) = finrank ℂ (wordSpace u v 2) := by
      have heq : er.toLinearMap = leftMap (u * v) := by
        ext x
        exact (mul_assoc _ _ _).symm
      rw [← heq]
      exact er.finrank_map_eq (wordSpace u v 2)
    exact (hi 3 (by omega)).symm.le.trans ((Submodule.finrank_mono hsub).trans_eq he)
  · let m := u * v * u
    have hm : m * m = 1 := by
      dsimp [m]
      calc
        (u * v * u) * (u * v * u) = u * v * (u * u) * v * u := by noncomm_ring
        _ = 1 := by simp only [hu, mul_one, mul_assoc, hv]
    have hsub : powerSpace u v ≤ (wordSpace u v 3).map (leftMap m) := by
      apply span_le.mpr
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact ⟨u * (v * u), subset_span hUVU, by simpa [leftMap, m, mul_assoc] using hm⟩
      · refine ⟨u * (u * u), subset_span hUUU, ?_⟩
        simp [leftMap, m, hu, mul_assoc, ← mul_assoc u u]
      · refine ⟨u * (u * v), subset_span hUUV, ?_⟩
        simp [leftMap, m, hu, ← mul_assoc, pow_two]
      · refine ⟨v * (u * v), subset_span hVUV, ?_⟩
        simp [leftMap, m, pow_succ, mul_assoc]
    have he := (leftEquiv m hm).finrank_map_eq (wordSpace u v 3)
    exact (hi 4 (by omega)).symm.le.trans ((Submodule.finrank_mono hsub).trans_eq he)

/-- Homogeneous rank grows by one until the four-dimensional power space is filled. -/
theorem homogeneous_word_rank (u v : A) (hu : u * u = 1) (hv : v * v = 1)
    (hli : LinearIndependent ℂ (fun i : Fin 4 => (u * v) ^ i.val))
    (hR : ∀ x ∈ powerSpace u v, (u * v) * x ∈ powerSpace u v)
    (hD : ∀ x ∈ powerSpace u v, (v * u) * x ∈ powerSpace u v) (n : ℕ) :
    finrank ℂ (wordSpace u v n) = min (n + 1) 4 := by
  have hub := upper_four u v hu hv hR hD n
  by_cases hn : n ≤ 3
  · have hlo := lower_small u v hu hv hli n hn
    have hsmall : finrank ℂ (wordSpace u v n) ≤ n + 1 := by
      interval_cases n
      · have heq : wordSpace u v 0 = span ℂ (Set.range fun _ : Fin 1 => (1 : A)) := by
          simp [wordSpace, products]
        rw [heq]
        simpa only [Set.finrank, Fintype.card_fin] using
          finrank_range_le_card (R := ℂ) (fun _ : Fin 1 => (1 : A))
      · change finrank ℂ (span ℂ (products u v 1)) ≤ 2
        have heq : products u v 1 = Set.range (![u, v] : Fin 2 → A) := by
          ext x
          simp only [products, Set.image_singleton, mul_one, Set.singleton_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
            Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
        rw [heq]
        simpa only [Set.finrank, Fintype.card_fin] using
          finrank_range_le_card (R := ℂ) (![u, v] : Fin 2 → A)
      · change finrank ℂ (span ℂ (products u v 2)) ≤ 3
        have heq : products u v 2 = Set.range (![1, u * v, v * u] : Fin 3 → A) := by
          ext x
          simp only [products, Set.image_union, Set.image_singleton, mul_one,
            Set.mem_union, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_succ,
            Matrix.cons_val_zero, Matrix.cons_val_succ, hu, hv]
          simp [eq_comm, or_assoc, or_left_comm, or_comm]
        rw [heq]
        simpa only [Set.finrank, Fintype.card_fin] using
          finrank_range_le_card (R := ℂ) (![1, u * v, v * u] : Fin 3 → A)
      · exact hub
    rw [min_eq_left (by omega)]
    exact le_antisymm hsmall hlo
  · rw [min_eq_right (by omega)]
    exact le_antisymm hub ((lower_small u v hu hv hli 3 (by omega)).trans
      (rank_mono u v hu (by omega)))

omit [Module.Finite ℂ A] in
private theorem scaled_left_map (u : A) (z : ℂ) (hz : z ≠ 0) (P : Submodule ℂ A) :
    P.map (leftMap (z • u)) = P.map (leftMap u) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨z • y, P.smul_mem z hy, by simp [leftMap]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨z⁻¹ • y, P.smul_mem _ hy, ?_⟩
    simp [leftMap, smul_smul, hz]

/-- Independent nonzero rescalings of the two generators preserve every word space. -/
theorem wordSpace_scale (u v : A) (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) (n : ℕ) :
    wordSpace (z • u) (w • v) n = wordSpace u v n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [space_succ, space_succ, ih, scaled_left_map u z hz,
      scaled_left_map v w hw]

omit [Module.Finite ℂ A] in
private theorem products_map {B : Type*} [Ring B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (u v : A) (n : ℕ) :
    products (f u) (f v) n = f '' products u v n := by
  induction n with
  | zero => simp [products]
  | succ n ih =>
    simp only [products, ih, Set.image_union, Set.image_image]
    congr 1 <;> congr 1 <;> funext x <;> simp

/-- Algebra transport preserves the exact homogeneous product family. -/
theorem wordSpace_map {B : Type*} [Ring B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (u v : A) (n : ℕ) :
    wordSpace (f u) (f v) n = (wordSpace u v n).map f.toLinearMap := by
  simp only [wordSpace, products_map, map_span]
  rfl

#print axioms homogeneous_word_rank
#print axioms wordSpace_scale
#print axioms wordSpace_map

end D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank
