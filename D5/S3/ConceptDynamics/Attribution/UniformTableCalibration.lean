/- GID: D5/S3/ConceptDynamics/Attribution/UniformTableCalibration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/UniformTableCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational covariant kernels admit optimal uniform calibrations from integer orbit minors. -/

import D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
import D5.S3.Combinatorics.Matroids.LinearRado
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.UniformTableCalibration

variable {I J : Type*} [Fintype J]

private noncomputable def form (c x : J → ℝ) : ℝ := ∑ j, c j * x j

private theorem form_step (c x v : J → ℝ) (t : ℝ) :
    form c (fun j => x j + t * v j) = form c x + t * form c v := by
  unfold form
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem form_smul (c v : J → ℝ) (s : ℝ) :
    form c (fun j => s * v j) = s * form c v := by
  unfold form
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

open Classical in
private theorem exists_independent_optimum (A : I → J → ℝ) (b : I → ℝ) (cost : J → ℝ)
    (normalization : ∃ i, ∀ j, 0 < A i j)
    (optimum : ∃ x : J → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, form (A i) x = b i) ∧
      (∀ y : J → ℝ, (∀ j, 0 ≤ y j) → (∀ i, form (A i) y = b i) → form cost y ≤ form cost x)) :
    ∃ x : J → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, form (A i) x = b i) ∧
      (∀ y : J → ℝ, (∀ j, 0 ≤ y j) → (∀ i, form (A i) y = b i) → form cost y ≤ form cost x) ∧
      LinearIndepOn ℝ (fun j i => A i j) (↑(univ.filter (fun j => 0 < x j)) : Set J) := by
  classical
  let support (x : J → ℝ) := univ.filter (fun j => 0 < x j)
  let optimal (x : J → ℝ) := (∀ j, 0 ≤ x j) ∧ (∀ i, form (A i) x = b i) ∧
    (∀ y : J → ℝ, (∀ j, 0 ≤ y j) → (∀ i, form (A i) y = b i) → form cost y ≤ form cost x)
  have exists_size : ∃ n : ℕ, ∃ x, optimal x ∧ (support x).card = n := by
    obtain ⟨x, hx⟩ := optimum
    exact ⟨(support x).card, x, hx, rfl⟩
  obtain ⟨x, ⟨hx₀, hxA, hxmax⟩, hxsize⟩ := Nat.find_spec exists_size
  refine ⟨x, hx₀, hxA, hxmax, ?_⟩
  change LinearIndepOn ℝ (fun j i => A i j) (↑(support x) : Set J)
  by_contra dependent
  obtain ⟨v, hv, k, hk, hk₀⟩ := not_linearIndepOn_finset_iff.mp dependent
  let w (j : J) := if j ∈ support x then v j else 0
  have hw (i : I) : form (A i) w = 0 := by
    have hsum := congrFun hv i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
    unfold form
    rw [← Finset.sum_subset (Finset.subset_univ (support x)) (f := fun j => A i j * w j)
      (by intro j _ h; simp [w, h])]
    simpa only [w, sum_congr, mul_comm] using
      (calc
        (∑ j ∈ support x, A i j * w j) = ∑ j ∈ support x, v j * A i j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [w, hj, mul_comm]
        _ = 0 := hsum)
  let s : ℝ := if 0 ≤ form cost w then 1 else -1
  let d (j : J) := s * w j
  have sd : s ≠ 0 := by unfold s; split <;> norm_num
  have hdA (i : I) : form (A i) d = 0 := by
    rw [show form (A i) d = s * form (A i) w from form_smul _ _ _, hw, mul_zero]
  have hdCost : 0 ≤ form cost d := by
    rw [show form cost d = s * form cost w from form_smul _ _ _]
    unfold s
    split <;> linarith
  have hd₀ (j : J) (hj : j ∉ support x) : d j = 0 := by simp [d, w, hj]
  have hdk : d k ≠ 0 := by simpa [d, w, hk, sd] using hk₀
  obtain ⟨i, hi⟩ := normalization
  let falling := univ.filter fun j => d j < 0
  have falling_has : falling.Nonempty := by
    by_contra h
    have hdnonneg (j : J) : 0 ≤ d j :=
      le_of_not_gt fun hj => h ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hi j).le (hdnonneg j))).mp (hdA i) k (mem_univ k)
    exact hdk ((mul_eq_zero.mp hzero).resolve_left (hi k).ne')
  let ratio (j : J) := x j / (-d j)
  let ratios := falling.image ratio
  have ratios_has : ratios.Nonempty := falling_has.image _
  let t := ratios.min' ratios_has
  obtain ⟨j₀, hj₀, hjmin⟩ := Finset.mem_image.mp (Finset.min'_mem ratios ratios_has)
  have hfind (j : J) (hj : d j < 0) : t ≤ ratio j :=
    Finset.min'_le ratios _ (Finset.mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩, rfl⟩)
  have negative : d j₀ < 0 := (mem_filter.mp hj₀).2
  have active : j₀ ∈ support x := by
    by_contra h
    exact negative.ne (hd₀ j₀ h)
  change ratio j₀ = t at hjmin
  have step_pos : 0 < t := hjmin ▸ div_pos (mem_filter.mp active).2 (neg_pos.mpr negative)
  let y (j : J) := x j + t * d j
  have hy₀ (j : J) : 0 ≤ y j := by
    by_cases hj : d j < 0
    · have ht := (le_div_iff₀ (neg_pos.mpr hj)).mp (hfind j hj)
      dsimp [y]
      linarith [ht]
    · exact add_nonneg (hx₀ j) (mul_nonneg step_pos.le (le_of_not_gt hj))
  have hyA (i : I) : form (A i) y = b i := by
    rw [form_step, hxA, hdA, mul_zero, add_zero]
  have improved : form cost x ≤ form cost y := by
    rw [form_step]
    linarith [mul_nonneg step_pos.le hdCost]
  have hyopt : optimal y := ⟨hy₀, hyA, fun z h₀ hA => (hxmax z h₀ hA).trans improved⟩
  have hsub : support y ⊆ support x := by
    intro j hj
    by_contra h
    have hjpos := (mem_filter.mp hj).2
    have hxzero : x j = 0 := le_antisymm
      (le_of_not_gt fun hp => h (mem_filter.mpr ⟨mem_univ _, hp⟩)) (hx₀ j)
    simp [y, hxzero, hd₀ j h] at hjpos
  have dropped : j₀ ∉ support y := by
    have heq := (div_eq_iff (neg_pos.mpr negative).ne').mp hjmin
    have hzero : y j₀ = 0 := by dsimp [y]; linarith
    simp [support, hzero]
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun h => dropped (h ▸ active)⟩)
  exact (Nat.not_lt_of_ge (Nat.find_min' exists_size ⟨y, hyopt, rfl⟩))
    (hxsize ▸ hlt)

end D5.S3.ConceptDynamics.Attribution.UniformTableCalibration

open Matrix Module

namespace D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.SquareMinor

variable {I S : Type*} [Fintype I] [Fintype S] [DecidableEq S]

open Classical in
private theorem exists_minor (A : Matrix I S ℝ) (independent : LinearIndependent ℝ A.col) :
    ∃ f : S → I, Function.Injective f ∧ (A.submatrix f id).det ≠ 0 := by
  classical
  let e := (Fintype.equivFin I).symm
  let d := (Fintype.equivFin S).symm
  let M := A.submatrix e d
  have hM : LinearIndependent ℝ M.col := by
    let L : (I → ℝ) ≃ₗ[ℝ] (Fin (Fintype.card I) → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e
    exact (independent.comp d d.injective).map' L.toLinearMap L.ker
  have hRank : M.rank = Fintype.card S := by
    simpa only [Matrix.rank_transpose, Fintype.card_fin] using (hM.rank_matrix (M := Mᵀ))
  have hSpan : Submodule.span ℝ (Set.range M.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hRank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨f, hf, hdet⟩ := D5.S3.Combinatorics.Matroids.LinearRado.exists_nonsingular_rows M hSpan
  refine ⟨e ∘ f ∘ d.symm, e.injective.comp (hf.comp d.symm.injective), ?_⟩
  have hReindex : (A.submatrix (e ∘ f ∘ d.symm) id).submatrix d d = M.submatrix f id := by
    ext i j
    simp [M, Function.comp_def]
  rwa [← hReindex, det_submatrix_equiv_self] at hdet

end SquareMinor

open Matrix

namespace D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.IntegerMinor

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem cleared_basic_solution (B : Matrix I I ℤ) (p : I → ℝ) (z : I → ℤ) (m : ℕ)
    (equations : B.map (Int.castRingHom ℝ) *ᵥ p = fun i => (z i : ℝ) / (m : ℝ))
    (hm : 0 < m) :
    ∃ k : I → ℤ, ∀ i, (k i : ℝ) = (m : ℝ) * (B.det : ℝ) * p i := by
  let phi := Int.castRingHom ℝ
  let C := B.map phi
  have scaled_rhs : C *ᵥ ((m : ℝ) • p) = phi ∘ z := by
    rw [Matrix.mulVec_smul, equations]
    funext i
    change (m : ℝ) * ((z i : ℝ) / (m : ℝ)) = (z i : ℝ)
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne') 
  refine ⟨B.adjugate *ᵥ z, ?_⟩
  intro i
  have mapped := RingHom.map_mulVec phi B.adjugate z i
  have adj : B.adjugate.map phi = C.adjugate := phi.map_adjugate B
  rw [adj, ← scaled_rhs, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec] at mapped
  change _ = C.det * ((m : ℝ) * p i) at mapped
  have det : C.det = phi B.det := (phi.map_det B).symm
  rw [← mul_assoc, mul_comm C.det, det] at mapped
  exact mapped

end IntegerMinor

open Finset Matrix

namespace D5.S3.ConceptDynamics.Attribution.UniformTableCalibration

variable {I J : Type*} [Fintype I] [Fintype J]

set_option maxHeartbeats 700000 in
open Classical in
private theorem integer_optimum [DecidableEq J] (A : Matrix I J ℤ) (b : I → ℝ) (cost : J → ℝ)
    (normalization : ∃ i, ∀ j, 0 < A i j)
    (optimum : ∃ x : J → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, form (fun j => (A i j : ℝ)) x = b i) ∧
      (∀ y : J → ℝ, (∀ j, 0 ≤ y j) → (∀ i, form (fun j => (A i j : ℝ)) y = b i) →
        form cost y ≤ form cost x))
    (m : ℕ) (hm : 0 < m) (z : I → ℤ) (rhs : ∀ i, b i = (z i : ℝ) / m) :
    ∃ x : J → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, form (fun j => (A i j : ℝ)) x = b i) ∧
      (∀ y : J → ℝ, (∀ j, 0 ≤ y j) → (∀ i, form (fun j => (A i j : ℝ)) y = b i) →
        form cost y ≤ form cost x) ∧
      let S := {j : J // 0 < x j}
      ∃ f : S → I, Function.Injective f ∧
        let B : Matrix S S ℤ := A.submatrix f Subtype.val
        B.det ≠ 0 ∧ ∃ n : J → ℕ, ∀ j, (n j : ℝ) = ((m * B.det.natAbs : ℕ) : ℝ) * x j := by
  classical
  obtain ⟨i₀, hi₀⟩ := normalization
  obtain ⟨x, hx₀, hxA, hxmax, independent⟩ := exists_independent_optimum
    (fun i j => (A i j : ℝ)) b cost ⟨i₀, fun j => by exact_mod_cast hi₀ j⟩ optimum
  refine ⟨x, hx₀, hxA, hxmax, ?_⟩
  let S := {j : J // 0 < x j}
  let C : Matrix I S ℝ := fun i j => (A i j.val : ℝ)
  have LI : LinearIndependent ℝ C.col := by
    exact independent.comp (fun j : S => (⟨j.val, by simp⟩ :
      (↑(univ.filter (fun k : J => 0 < x k)) : Set J)))
      (fun a b hab => Subtype.ext (congrArg (fun j : (↑(univ.filter (fun k : J => 0 < x k)) : Set J) => j.val) hab))
  obtain ⟨f, hf, hdet⟩ := SquareMinor.exists_minor C LI
  let B : Matrix S S ℤ := A.submatrix f Subtype.val
  let cast := Int.castRingHom ℝ
  have hmap : B.map cast = C.submatrix f id := rfl
  have hB : B.det ≠ 0 := by
    intro hzero
    have det_map : (B.map cast).det = cast B.det := (cast.map_det B).symm
    apply hdet
    exact (congrArg (fun M : Matrix S S ℝ => M.det) hmap).symm.trans
      (det_map.trans ((congrArg cast hzero).trans cast.map_zero))
  refine ⟨f, hf, hB, ?_⟩
  have hEq : B.map cast *ᵥ (fun j : S => x j.val) = fun i => ((z (f i) : ℤ) : ℝ) / m := by
    funext i
    rw [← rhs, ← hxA]
    change (∑ j : S, (A (f i) j.val : ℝ) * x j.val) = ∑ j : J, (A (f i) j : ℝ) * x j
    let term (j : J) := (A (f i) j : ℝ) * x j
    change ∑ j : S, term j.val = ∑ j : J, term j
    have restrict := Finset.sum_subtype_eq_sum_filter (s := (univ : Finset J))
      (p := fun j => 0 < x j) term
    trans ∑ j ∈ univ.filter (fun j : J => 0 < x j), term j
    · simpa using restrict
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hxzero : x j = 0 := le_antisymm (le_of_not_gt (by simpa using hj)) (hx₀ j)
    simp [term, hxzero]
  obtain ⟨k, hk⟩ := IntegerMinor.cleared_basic_solution B (fun j : S => x j.val)
    (z ∘ f) m hEq hm
  let n (j : J) := if hx : 0 < x j then (k ⟨j, hx⟩).natAbs else 0
  refine ⟨n, fun j => ?_⟩
  by_cases hx : 0 < x j
  · have h := congrArg abs (hk ⟨j, hx⟩)
    simpa [n, hx, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs, abs_mul,
      abs_of_nonneg (hx₀ j), abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m)] using h
  · have hxzero : x j = 0 := le_antisymm (le_of_not_gt hx) (hx₀ j)
    simp [n, hxzero]

end D5.S3.ConceptDynamics.Attribution.UniformTableCalibration

open Finset
open D5.S3.ConceptDynamics.Attribution.TableOrbitWeights (orbitFrequency maximal_invariant_event_mass)

namespace D5.S3.ConceptDynamics.Attribution.UniformTableCalibration

variable {G T I : Type*} [Group G] [Fintype T] [MulAction G T] [Fintype I]

abbrev Orbit (G T : Type*) [Group G] [MulAction G T] :=
  MulAction.orbitRel.Quotient G T

private noncomputable instance : Fintype (Orbit G T) := Fintype.ofFinite _

def orbit (t : T) : Orbit G T := Quotient.mk'' t

open Classical in
noncomputable def orbitCount (A : Finset T) (o : Orbit G T) : ℕ :=
  (A.filter (fun t => orbit t = o)).card

private theorem count_pos (o : Orbit G T) : 0 < orbitCount univ o := by
  classical
  exact Finset.card_pos.mpr ⟨Quotient.out o, mem_filter.mpr ⟨mem_univ _, Quotient.out_eq o⟩⟩

private theorem event_frequency (A : Finset T) (o : Orbit G T) :
    orbitFrequency A o = (orbitCount A o : ℝ) / (orbitCount univ o : ℝ) := rfl

private theorem event_count_form (A : Finset T) (x : Orbit G T → ℝ) :
    (∑ t ∈ A, x (orbit t)) = form (fun o => (orbitCount A o : ℝ)) x := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := orbit (G := G)) (t := univ)
    (fun _ _ => mem_univ _)]
  unfold form
  apply Finset.sum_congr rfl
  intro o _
  calc
    _ = ∑ _t ∈ A.filter (fun t => orbit t = o), x o := by
      exact Finset.sum_congr rfl (fun t ht => congrArg x (mem_filter.mp ht).2)
    _ = (orbitCount A o : ℝ) * x o := by rw [sum_const, nsmul_eq_mul, orbitCount]

set_option maxHeartbeats 700000 in
open Classical in
private theorem uniform_invariant_events (event : I → Finset T) (mass : I → ℝ) (target : Finset T)
    (feasible : ∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
      (∀ (g : G) t, p (g • t) = p t) ∧ ∀ i, (∑ t ∈ event i, p t) = mass i)
    (m : ℕ) (hm : 0 < m) (z : I → ℤ) (hz : ∀ i, mass i = (z i : ℝ) / m) :
    let A : Matrix (Option I) (Orbit G T) ℤ := fun i o => orbitCount (i.elim univ event) o
    ∃ x : Orbit G T → ℝ,
      ∃ rows : {o // 0 < x o} → Option I, Function.Injective rows ∧
        let B := A.submatrix rows Subtype.val
        let N := m * B.det.natAbs
        0 < N ∧ ∃ n : T → ℕ, (∀ (g : G) t, n (g • t) = n t) ∧
          (∑ t, n t) = N ∧
          (∀ i, (∑ t ∈ event i, n t : ℕ) = (N : ℝ) * mass i) ∧
          (∀ t, (n t : ℝ) = (N : ℝ) * x (orbit t)) ∧
          (∀ p : T → ℝ, (∀ t, 0 ≤ p t) → (∑ t, p t) = 1 →
            (∀ (g : G) t, p (g • t) = p t) →
            (∀ i, (∑ t ∈ event i, p t) = mass i) →
            (∑ t ∈ target, p t) ≤ ((∑ t ∈ target, n t : ℕ) : ℝ) / N) := by
  classical
  let events (i : Option I) : Finset T := i.elim univ event
  let A : Matrix (Option I) (Orbit G T) ℤ := fun i o => orbitCount (events i) o
  let b (i : Option I) : ℝ := i.elim 1 mass
  let c (o : Orbit G T) : ℝ := orbitCount target o
  let d (o : Orbit G T) : ℝ := orbitCount univ o
  have hd (o : Orbit G T) : 0 < d o := Nat.cast_pos.mpr (count_pos o)
  have toOrbit (x : Orbit G T → ℝ) (F : Finset T) :
      (∑ o, (d o * x o) * orbitFrequency F o) = form (fun o => (orbitCount F o : ℝ)) x := by
    unfold form
    apply Finset.sum_congr rfl
    intro o _
    rw [event_frequency]
    change (d o * x o) * ((orbitCount F o : ℝ) / d o) = _
    field_simp [ne_of_gt (hd o)]
  have normalization (x : Orbit G T → ℝ) : form (fun o => (A none o : ℝ)) x = ∑ o, d o * x o := by
    simp [form, d, A, events]
  have rows_eq (x : Orbit G T → ℝ) (i : I) :
      form (fun o => (A (some i) o : ℝ)) x = ∑ o, (d o * x o) * orbitFrequency (event i) o := by
    rw [toOrbit]
    simp [A, events]
  obtain ⟨w, hw₀, hwtotal, hwm, hwopt, hrealize⟩ :=
    maximal_invariant_event_mass event mass target feasible
  let p (o : Orbit G T) := w o / d o
  have hp (o : Orbit G T) : d o * p o = w o := by
    exact mul_div_cancel₀ (w o) (hd o).ne'
  have hopt : ∃ x : Orbit G T → ℝ, (∀ o, 0 ≤ x o) ∧
      (∀ i, form (fun o => (A i o : ℝ)) x = b i) ∧
      (∀ y : Orbit G T → ℝ, (∀ o, 0 ≤ y o) →
        (∀ i, form (fun o => (A i o : ℝ)) y = b i) → form c y ≤ form c x) := by
    refine ⟨p, fun o => div_nonneg (hw₀ o) (hd o).le, ?_, ?_⟩
    · rintro (_ | i)
      · simpa only [normalization, hp, b, Option.elim_none] using hwtotal
      · simpa only [rows_eq, hp, b, Option.elim_some] using hwm i
    · intro y hy₀ hyRows
      have bound := hwopt (fun o => d o * y o) (fun o => mul_nonneg (hd o).le (hy₀ o))
        ((normalization y).symm.trans (hyRows none))
        (fun i => (rows_eq y i).symm.trans (hyRows (some i)))
      rw [toOrbit] at bound
      change form (fun o => (orbitCount target o : ℝ)) y ≤ form (fun o => (orbitCount target o : ℝ)) p
      rw [← toOrbit p target]
      simp_rw [hp]
      exact bound
  let rhs (i : Option I) : ℤ := i.elim m z
  have hb (i : Option I) : b i = (rhs i : ℝ) / m := by
    cases i with
    | none => change (1 : ℝ) = ((m : ℤ) : ℝ) / m
              rw [Int.cast_natCast, div_self (Nat.cast_ne_zero.mpr hm.ne')]
    | some i => exact hz i
  obtain ⟨x, hx₀, hxA, hxmax, f, hf, hdet, k, hk⟩ := integer_optimum A b c
    ⟨none, fun o => Int.natCast_pos.mpr (count_pos o)⟩ hopt m hm rhs hb
  let B : Matrix {o // 0 < x o} {o // 0 < x o} ℤ := A.submatrix f Subtype.val
  let N := m * B.det.natAbs
  have hN : 0 < N := Nat.mul_pos hm (Int.natAbs_pos.mpr hdet)
  let n (t : T) := k (orbit t)
  have ncount (F : Finset T) :
      ((∑ t ∈ F, n t : ℕ) : ℝ) = (N : ℝ) * form (fun o => (orbitCount F o : ℝ)) x := by
    push_cast
    simp_rw [n, hk]
    rw [← Finset.mul_sum, event_count_form]
  refine ⟨x, f, hf, hN, n, ?_, ?_, ?_, fun t => hk (orbit t), ?_⟩
  · intro g t
    exact congrArg k MulAction.orbitRel.Quotient.quotient_smul_eq
  · have normal : form (fun o => (orbitCount (univ : Finset T) o : ℝ)) x = 1 := by
      simpa [A, events, b] using hxA none
    change (∑ t, n t) = N
    apply Nat.cast_injective (R := ℝ)
    exact (ncount univ).trans (by rw [normal, mul_one])
  · intro i
    have cell : form (fun o => (orbitCount (event i) o : ℝ)) x = mass i := by
      simpa [A, events, b] using hxA (some i)
    exact (ncount (event i)).trans (congrArg ((N : ℝ) * ·) cell)
  · intro p' hn ht hi hrows
    obtain ⟨u, u₀, ut, um, uv⟩ := (hrealize (∑ t ∈ target, p' t)).mp ⟨p', hn, ht, hi, hrows, rfl⟩
    have hu := hwopt u u₀ ut um
    have better := hxmax p (fun o => div_nonneg (hw₀ o) (hd o).le) (by
      rintro (_ | i)
      · simpa only [normalization, hp, b, Option.elim_none] using hwtotal
      · simpa only [rows_eq, hp, b, Option.elim_some] using hwm i)
    rw [ncount]
    change _ ≤ (N : ℝ) * form c x / N
    rw [mul_comm, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
    rw [← uv]
    calc
      ∑ o, u o * orbitFrequency target o ≤ ∑ o, w o * orbitFrequency target o := hu
      _ = form c p := by rw [← toOrbit p target]; simp_rw [hp]
      _ ≤ form c x := better

end D5.S3.ConceptDynamics.Attribution.UniformTableCalibration


open Finset

namespace D5.S3.ConceptDynamics.Attribution.UniformTableCalibration.SeedCopies

universe u v

variable {G : Type u} {S : Type v} [Group G] [MulAction G S]

private def Copies (n : S → ℕ) := {p : S × ℕ // p.2 < n p.1}

private def copiesEquiv (n : S → ℕ) : Copies n ≃ Σ s, Fin (n s) where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨(p.1, p.2.val), p.2.isLt⟩
  left_inv := by rintro ⟨⟨s,i⟩,hi⟩; rfl
  right_inv := by rintro ⟨s,⟨i,hi⟩⟩; rfl

@[instance_reducible] private def copiesAction (n : S → ℕ) (invariant : ∀ (g : G) s, n (g • s) = n s) :
    MulAction G (Copies n) where
  smul g p := ⟨(g • p.val.1, p.val.2), by simpa only [invariant] using p.property⟩
  one_smul p := Subtype.ext (Prod.ext (one_smul G _) rfl)
  mul_smul g h p := Subtype.ext (Prod.ext (mul_smul g h _) rfl)

open Classical in
private theorem exact_card_count [Fintype S] (n : S → ℕ)
    (invariant : ∀ (g : G) s, n (g • s) = n s) :
    ∃ (S' : Type v) (_ : Fintype S') (_ : MulAction G S') (p : S' → S),
      (∀ (g : G) s', p (g • s') = g • p s') ∧
      (∀ (H : Subgroup G) s', (∀ h : H, (h : G) • s' = s') ↔
        ∀ h : H, (h : G) • p s' = p s') ∧
      (∀ A : S → Prop, (∑ s', if A (p s') then 1 else (0 : ℕ)) =
        ∑ s, if A s then n s else 0) := by
  classical
  let E := copiesEquiv n
  let : Fintype (Copies n) := Fintype.ofEquiv _ E.symm
  let : MulAction G (Copies n) := copiesAction n invariant
  let projection (p : Copies n) := p.val.1
  refine ⟨Copies n, inferInstance, copiesAction n invariant, projection, ?_, ?_, ?_⟩
  · intro g p
    rfl
  · intro H p
    constructor
    · exact fun hfixed h => congrArg (fun (t : Copies n) => t.val.1) (hfixed h)
    · exact fun hfixed h => Subtype.ext (Prod.ext (hfixed h) rfl)
  · intro A
    let f (p : Copies n) : ℕ := if A p.val.1 then 1 else 0
    change ∑ p, f p = _
    rw [← E.symm.sum_comp f]
    simp only [Fintype.sum_sigma]
    apply sum_congr rfl
    intro s _
    change (∑ _ : Fin (n s), if A s then 1 else (0 : ℕ)) = if A s then n s else 0
    by_cases hs : A s <;> simp [hs]

end SeedCopies

namespace D5.S3.ConceptDynamics.Attribution.UniformTableCalibration

open D5.S3.ConceptDynamics.Attribution
open D5.S3.ConceptDynamics.Attribution.FixedKernelMass (seedFixedMass)

universe u v w s

variable {G : Type u} {X : Type v} {Y : Type w}
variable [Group G] [MulAction G X] [MulAction G Y] [Fintype X] [Fintype Y]

attribute [local instance 2000] FiniteTableCalibration.tableSMul FiniteTableCalibration.tableAction

local instance (priority := 2100) tableSubgroupAction (H : Subgroup G) : MulAction H (X → Y) :=
  MulAction.compHom (X → Y) H.subtype

set_option maxHeartbeats 700000 in
open Classical in
/-- Rational covariant kernels attain the maximum subgroup-fixed seed mass on
equal-weight replicas of an optimal table law. A nonsingular integer orbit
minor bounds the number of copies through its absolute determinant. -/
theorem uniform_kernel_optimum (H : Subgroup G) (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
    (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ (g : G) x y, P (g • x) (g • y) = P x y)
    (m : ℕ) (hm : 0 < m) (z : X × Y → ℤ)
    (hz : ∀ x y, P x y = (z (x, y) : ℝ) / m) :
    let cell (xy : X × Y) := univ.filter (fun t : X → Y => t xy.1 = xy.2)
    let A : Matrix (Option (X × Y)) (Orbit G (X → Y)) ℤ :=
      fun i o => orbitCount (i.elim univ cell) o
    ∃ x : Orbit G (X → Y) → ℝ,
      ∃ rows : {o // 0 < x o} → Option (X × Y), Function.Injective rows ∧
        let N := m * (A.submatrix rows Subtype.val).det.natAbs
        0 < N ∧ ∃ (U : Type (max v w)) (_ : Fintype U) (_ : MulAction G U) (f : X → U → Y),
          Fintype.card U = N ∧
          (∀ x y, (∑ t : U, if f x t = y then (N : ℝ)⁻¹ else 0) = P x y) ∧
          (∀ (g : G) x t, f (g • x) (g • t) = g • f x t) ∧
          (∀ t : X → Y, FiniteTableCalibration.tableLaw (fun _ : U => (N : ℝ)⁻¹) f t =
            x (orbit t)) ∧
          ∀ (S : Type s) (_ : Fintype S) (_ : MulAction G S) (a : S → ℝ) (read : X → S → Y),
            (∀ t, 0 ≤ a t) → (∑ t, a t) = 1 → (∀ (g : G) t, a (g • t) = a t) →
            (∀ x y, (∑ t, if read x t = y then a t else 0) = P x y) →
            (∀ (g : G) x t, read (g • x) (g • t) = g • read x t) →
            seedFixedMass (G := H) a ≤ seedFixedMass (G := H) (fun _ : U => (N : ℝ)⁻¹) := by
  classical
  let cell (xy : X × Y) := univ.filter (fun t : X → Y => t xy.1 = xy.2)
  let fixed := univ.filter (fun t : X → Y => ∀ (h : H), (h : G) • t = t)
  let mass (xy : X × Y) := P xy.1 xy.2
  have bottom (x : X) : ∃ y : Y, 0 < P x y ∧
      ∀ h : (⊥ : Subgroup G), h • x = x → h • y = y := by
    have positive : 0 < ∑ y, P x y := by rw [normalized]; exact zero_lt_one
    obtain ⟨y, _, hy⟩ := (sum_pos_iff_of_nonneg fun y _ => nn x y).mp positive
    refine ⟨y, hy, fun h _ => ?_⟩
    change h.val • y = y
    rw [Subgroup.mem_bot.mp h.property, one_smul]
  obtain ⟨S, _, _, weight, read, positive, total, invariant, marginal, readCov, _⟩ :=
    (FiniteKernelStabilizers.stabilizer_possible_iff P nn normalized cov (⊥ : Subgroup G)).mpr bottom
  let table := FiniteTableCalibration.tableLaw weight read
  obtain ⟨pn, pt, pi, pm, _⟩ :=
    FiniteTableCalibration.calibration_table_law weight (fun t => (positive t).le) total read readCov P marginal
  have feasible : ∃ p : (X → Y) → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
      (∀ (g : G) t, p (g • t) = p t) ∧ ∀ i, (∑ t ∈ cell i, p t) = mass i :=
    ⟨table, pn, pt, pi invariant, fun i => by simpa only [cell, mass, sum_filter] using pm i.1 i.2⟩
  obtain ⟨x, rows, injective, hN, n, invariantN, totalN, rowN, weightN, optimal⟩ :=
    uniform_invariant_events cell mass fixed feasible m hm z (fun i => hz i.1 i.2)
  let A : Matrix (Option (X × Y)) (Orbit G (X → Y)) ℤ :=
    fun i o => orbitCount (i.elim univ cell) o
  let N := m * (A.submatrix rows Subtype.val).det.natAbs
  obtain ⟨U, _, _, proj, equiv, fix, counts⟩ := SeedCopies.exact_card_count n invariantN
  let f (x : X) (u : U) := proj u x
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have cardU : Fintype.card U = N := by
    have h : Fintype.card U = ∑ t, n t := by simpa using counts (fun _ => True)
    exact h.trans totalN
  have massCount (F : (X → Y) → Prop) :
      (∑ t : U, if F (proj t) then (N : ℝ)⁻¹ else 0) =
        ((∑ t : X → Y, if F t then n t else (0 : ℕ)) : ℝ) / N := by
    calc
      _ = ((∑ t : U, if F (proj t) then 1 else (0 : ℕ)) : ℝ) / N := by
        rw [div_eq_mul_inv]
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        split <;> simp
      _ = _ := by
        simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
          congrArg (fun count : ℕ => (count : ℝ) / N) (counts F)
  refine ⟨x, rows, injective, hN, U, inferInstance, inferInstance, f, cardU, ?_, ?_, ?_, ?_⟩
  · intro x y
    have h : (∑ t : U, if proj t x = y then (N : ℝ)⁻¹ else 0) =
        ((∑ t ∈ cell (x, y), n t : ℕ) : ℝ) / N := by
      simpa only [cell, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using massCount (fun t => t x = y)
    exact h.trans (by rw [rowN, mul_comm, mul_div_cancel_right₀ _ hNr])
  · intro g x t
    change proj (g • t) (g • x) = g • proj t x
    rw [equiv]
    change g • proj t (g⁻¹ • (g • x)) = _
    rw [inv_smul_smul]
  · intro t
    have fiber : (∑ v : X → Y, if v = t then n v else (0 : ℕ)) = n t := by
      simp
    have h := massCount (fun v => v = t)
    change (∑ u : U, if proj u = t then (N : ℝ)⁻¹ else 0) = _
    refine h.trans ?_
    calc
      _ = (n t : ℝ) / N := by
        simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using
          congrArg (fun k : ℕ => (k : ℝ) / N) fiber
      _ = x (orbit t) := by rw [weightN, mul_comm, mul_div_cancel_right₀ _ hNr]
  · intro V _ _ a read ha ht hi hmarg hc
    let p := FiniteTableCalibration.tableLaw a read
    obtain ⟨hpn, hpt, hpi, hpm, _⟩ :=
      FiniteTableCalibration.calibration_table_law a ha ht read hc P hmarg
    have hpbound :=
      (FiniteTableCalibration.calibration_table_law (G := H) a ha ht read
        (fun h => hc h.val) P hmarg).2.2.2.2
    have hscore := optimal p hpn hpt (hpi hi)
      (fun i => by simpa only [cell, mass, sum_filter] using hpm i.1 i.2)
    have src : seedFixedMass (G := H) p = ∑ t ∈ fixed, p t := rfl
    have dst : seedFixedMass (G := H) (fun _ : U => (N : ℝ)⁻¹) =
        ((∑ t ∈ fixed, n t : ℕ) : ℝ) / N := by
      unfold seedFixedMass
      simp only [sum_filter]
      change (∑ t : U, if ∀ h : H, (h : G) • t = t then (N : ℝ)⁻¹ else 0) = _
      simp_rw [fix]
      simpa only [fixed, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using massCount (fun t => ∀ h : H, (h : G) • t = t)
    exact hpbound.trans (src ▸ dst.symm ▸ hscore)

end D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
