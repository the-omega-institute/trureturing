/- GID: D5/S3/QuadraticForms/SymmetricRankOneGuards
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SymmetricRankOneGuards
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uncancelled polynomial guards for the scalar responses of symmetric block updates. -/

module

public import D5.S3.QuadraticForms.SymmetricRankOneKernel
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Uncancelled integer polynomials control the zero-nullity scalar branch. -/

public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.QuadraticForms.SymmetricRankOneKernel

open Polynomial
open scoped BigOperators

variable {ι : Type*}

/-- The numerator obtained by putting the child responses over the product denominator. -/
def responseNumerator [Fintype ι] [DecidableEq ι] (P Q : ι → ℤ[X]) : ℤ[X] :=
  ∑ i, P i * ∏ j ∈ Finset.univ.erase i, Q j

/-- The uncancelled denominator after coupling the child blocks with coefficient `t`. -/
def responseGuard [Fintype ι] [DecidableEq ι] (P Q : ι → ℤ[X]) (t : ℤ) : ℤ[X] :=
  (∏ i, Q i) + C t * responseNumerator P Q

private theorem eval_responseNumerator [Fintype ι] [DecidableEq ι]
    (P Q : ι → ℤ[X]) (x : ℝ) (hQ : ∀ i, (Q i).eval₂ (Int.castRingHom ℝ) x ≠ 0) :
    let ev := eval₂RingHom (Int.castRingHom ℝ) x
    ev (responseNumerator P Q) = (∑ i, ev (P i) / ev (Q i)) * ev (∏ i, Q i) := by
  dsimp only
  let ev := eval₂RingHom (Int.castRingHom ℝ) x
  change ev (responseNumerator P Q) = _
  rw [responseNumerator, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, ← Finset.mul_prod_erase Finset.univ Q (Finset.mem_univ i), map_mul]
  change ev (P i) * ev (∏ j ∈ Finset.univ.erase i, Q j) =
    ev (P i) / ev (Q i) * (ev (Q i) * ev (∏ j ∈ Finset.univ.erase i, Q j))
  have hi : ev (Q i) ≠ 0 := hQ i
  rw [← mul_assoc, div_mul_cancel₀ _ hi]

/-- If every child guard and the output guard are nonzero at a common shift, the
updated kernel has dimension zero and its scalar response is the uncancelled ratio. -/
theorem update_block_of_guard_ne_zero [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)]
    (A : ∀ i, F i →ₗ[ℝ] F i) (hA : ∀ i, (A i).IsSymmetric) (u : PiLp 2 F)
    (P Q : ι → ℤ[X]) (t : ℤ) (x : ℝ)
    (hQ : ∀ i, (Q i).eval₂ (Int.castRingHom ℝ) x ≠ 0)
    (hguard : (responseGuard P Q t).eval₂ (Int.castRingHom ℝ) x ≠ 0)
    (hchild : ∀ i, Module.finrank ℝ (LinearMap.ker (A i)) = 0 ∧
      ScalarResponse (A i) (u i)
        ((P i).eval₂ (Int.castRingHom ℝ) x / (Q i).eval₂ (Int.castRingHom ℝ) x)) :
    Module.finrank ℝ (LinearMap.ker (update (blockDiagonal A) u (t : ℝ))) = 0 ∧
    ScalarResponse (update (blockDiagonal A) u (t : ℝ)) u
      ((responseNumerator P Q).eval₂ (Int.castRingHom ℝ) x /
        (responseGuard P Q t).eval₂ (Int.castRingHom ℝ) x) := by
  let ev := eval₂RingHom (Int.castRingHom ℝ) x
  let S := ∑ i, ev (P i) / ev (Q i)
  let R := ev (∏ i, Q i)
  have hR : R ≠ 0 := by
    change ev (∏ i, Q i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hQ i
  have hP : ev (responseNumerator P Q) = S * R := eval_responseNumerator P Q x hQ
  have hguard' : ev (responseGuard P Q t) = (1 + (t : ℝ) * S) * R := by
    rw [responseGuard, map_add, map_mul, hP]
    have ht : ev (C t) = (t : ℝ) := by
      change (C t).eval₂ (Int.castRingHom ℝ) x = _
      rw [eval₂_C]
      rfl
    rw [ht]
    change R + (t : ℝ) * (S * R) = (1 + (t : ℝ) * S) * R
    ring
  have hres : 1 + (t : ℝ) * S ≠ 0 := by
    intro h
    apply hguard
    change ev (responseGuard P Q t) = 0
    rw [hguard', h, zero_mul]
  obtain ⟨hSymm, hsum, _, hresponse⟩ := blockDiagonal_states A hA u
  obtain ⟨hker, hscalar⟩ :=
    update_of_nonresonance hSymm (hresponse _ (fun i => (hchild i).2)) hres
  refine ⟨?_, ?_⟩
  · rw [hker, hsum]
    simp only [fun i => (hchild i).1, Finset.sum_const_zero]
  have hratio : ev (responseNumerator P Q) / ev (responseGuard P Q t) =
      S / (1 + (t : ℝ) * S) := by
    rw [hP, hguard']
    field_simp [hR, hres]
  change ScalarResponse _ _ (ev (responseNumerator P Q) / ev (responseGuard P Q t))
  rw [hratio]
  exact hscalar

/-- The response numerator has degree one less than the total child size, with leading
coefficient minus that size. The added numerator term leaves the guard monic. -/
theorem responseGuard_degrees [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (P Q : ι → ℤ[X]) (t : ℤ) (n : ι → ℕ) (hpos : ∀ i, 0 < n i)
    (hQ : ∀ i, (Q i).Monic ∧ (Q i).natDegree = n i)
    (hP : ∀ i, (P i).natDegree = n i - 1 ∧ (P i).leadingCoeff = -(n i : ℤ)) :
    let N := ∑ i, n i
    (responseNumerator P Q).natDegree = N - 1 ∧
    (responseNumerator P Q).leadingCoeff = -(N : ℤ) ∧
    (responseGuard P Q t).Monic ∧ (responseGuard P Q t).natDegree = N := by
  dsimp only
  let N := ∑ i, n i
  have hN : 0 < N := Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  let p (i : ι) := P i * ∏ j ∈ Finset.univ.erase i, Q j
  have hterm (i : ι) : (p i).natDegree = N - 1 ∧ (p i).leadingCoeff = -(n i : ℤ) := by
    have hm := monic_prod_of_monic (Finset.univ.erase i) Q (fun j _ => (hQ j).1)
    have hne : P i ≠ 0 := by
      have hp := hpos i
      intro h
      have hz := (hP i).2
      rw [h, leadingCoeff_zero] at hz
      omega
    change (P i * _).natDegree = _ ∧ (P i * _).leadingCoeff = _
    rw [natDegree_mul hne hm.ne_zero, leadingCoeff_mul, hm.leadingCoeff, mul_one,
      (hP i).1, (hP i).2,
      natDegree_prod_of_monic (Finset.univ.erase i) Q (fun j _ => (hQ j).1)]
    simp only [fun j => (hQ j).2, and_true]
    have hsum : (∑ j ∈ Finset.univ.erase i, n j) + n i = N :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have hp := hpos i
    omega
  have hdegree_le : (responseNumerator P Q).natDegree ≤ N - 1 :=
    natDegree_sum_le_of_forall_le Finset.univ p (fun i _ => (hterm i).1.le)
  have hcoeff : (responseNumerator P Q).coeff (N - 1) = -(N : ℤ) := by
    change (∑ i, p i).coeff (N - 1) = _
    rw [finsetSum_coeff]
    calc
      ∑ i, (p i).coeff (N - 1) = ∑ i, -(n i : ℤ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← (hterm i).1, coeff_natDegree, (hterm i).2]
      _ = -(N : ℤ) := by simp [N, Finset.sum_neg_distrib]
  have hdegree : (responseNumerator P Q).natDegree = N - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hdegree_le (by rw [hcoeff]; omega)
  have hprod := monic_prod_of_monic Finset.univ Q (fun i _ => (hQ i).1)
  have hproddeg : (∏ i, Q i).natDegree = N := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => (hQ i).1)]
    simp only [fun i => (hQ i).2, N]
  have hlower : (C t * responseNumerator P Q).natDegree < (∏ i, Q i).natDegree :=
    (natDegree_C_mul_le _ _).trans_lt (by rw [hdegree, hproddeg]; omega)
  exact ⟨hdegree, by rw [← coeff_natDegree, hdegree, hcoeff],
    hprod.add_of_left (degree_lt_degree hlower),
    (natDegree_add_eq_left_of_natDegree_lt hlower).trans hproddeg⟩

/-- The distinct real roots of a finite collection of integer guards. -/
noncomputable def realGuardCandidates (s : Finset ι) (Q : ι → ℤ[X]) : Finset ℝ := by
  classical
  exact s.biUnion fun i => ((Q i).map (Int.castRingHom ℝ)).roots.toFinset

/-- A predicate which fails off the guard roots has a finite exact shift criterion,
with at most the sum of the guard degrees distinct candidates. -/
theorem realGuardCandidates_spec (s : Finset ι) (Q : ι → ℤ[X])
    (hQ : ∀ i ∈ s, Q i ≠ 0) (target : ℝ → Prop)
    (hoff : ∀ x : ℝ, (∀ i ∈ s, (Q i).eval₂ (Int.castRingHom ℝ) x ≠ 0) → ¬ target x) :
    (realGuardCandidates s Q).card ≤ ∑ i ∈ s, (Q i).natDegree ∧
      ((∃ x : ℝ, target x) ↔ ∃ x ∈ realGuardCandidates s Q, target x) := by
  classical
  have hcard (i : ι) :
      (((Q i).map (Int.castRingHom ℝ)).roots.toFinset).card ≤ (Q i).natDegree :=
    (Multiset.toFinset_card_le _).trans (card_roots_map_le_natDegree _)
  refine ⟨Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun i _ => hcard i)), ?_⟩
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, hx⟩
    by_contra hn
    apply hoff x (fun i hi hz => hn ?_) hx
    have hmap : (Q i).map (Int.castRingHom ℝ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr (hQ i hi)
    exact Finset.mem_biUnion.mpr ⟨i, hi,
      Multiset.mem_toFinset.mpr ((mem_roots hmap).mpr (by
        rwa [IsRoot, ← eval₂_eq_eval_map]))⟩
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩

end D5.S3.QuadraticForms.SymmetricRankOneKernel
