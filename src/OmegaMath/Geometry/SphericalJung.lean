import OmegaBuild.Commands
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

compile_only_with_mathlib

/-!
Omega original.

A nearest point of a convex hull yields a spherical cap. When the point is
nonzero, its positive-weight support lies in a supporting affine hyperplane.
-/

open scoped InnerProductSpace
open Set

namespace Omega.Geometry.SphericalJung

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A proper subspace has a unit normal. -/
private theorem exists_unit_normal (K : Submodule ℝ E)
    (hK : Module.finrank ℝ K < Module.finrank ℝ E) :
    ∃ v : E, ‖v‖ = 1 ∧ v ∈ Kᗮ := by
  have hdim := K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mp hpos
  have hn : ‖(w : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (fun h => hw (Subtype.ext h))
  exact ⟨‖(w : E)‖⁻¹ • (w : E), by
    simp [norm_smul, hn],
    Kᗮ.smul_mem _ w.property⟩

/-- At most as many points as the ambient dimension lie in a closed hemisphere. -/
theorem exists_closed_hemisphere {ι : Type*} [Fintype ι] (q : ι → E)
    (hd : 0 < Module.finrank ℝ E) (hn : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ v : E, ‖v‖ = 1 ∧ ∀ i, 0 ≤ ⟪v, q i⟫_ℝ := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    obtain ⟨v, hv, _⟩ := exists_unit_normal (⊥ : Submodule ℝ E) (by simpa)
    exact ⟨v, hv, fun i => (h.false i).elim⟩
  | inr h =>
    let i₀ := h.some
    let K := vectorSpan ℝ (range q)
    have hK : Module.finrank ℝ K < Module.finrank ℝ E := by
      change Module.finrank ℝ (vectorSpan ℝ (range q)) < _
      have hdim := finrank_vectorSpan_range_add_one_le ℝ q
      omega
    obtain ⟨v, hv, hvK⟩ := exists_unit_normal K hK
    have heq (i : ι) : ⟪v, q i⟫_ℝ = ⟪v, q i₀⟫_ℝ := by
      have hmem : q i - q i₀ ∈ K :=
        vsub_mem_vectorSpan ℝ (mem_range_self i) (mem_range_self i₀)
      have hzero := (Submodule.mem_orthogonal K v).mp hvK _ hmem
      rw [real_inner_comm, inner_sub_right, sub_eq_zero] at hzero
      exact hzero
    by_cases hsign : 0 ≤ ⟪v, q i₀⟫_ℝ
    · exact ⟨v, hv, fun i => heq i ▸ hsign⟩
    · exact ⟨-v, by simpa, fun i => by rw [inner_neg_left, heq]; linarith⟩

omit [FiniteDimensional ℝ E] in
/-- The origin's nearest point in a finite convex hull and its supporting inequality. -/
theorem exists_min_norm_support {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → E) :
    ∃ z ∈ convexHull ℝ (range q), ∀ i, ‖z‖ ^ 2 ≤ ⟪z, q i⟫_ℝ := by
  let K := convexHull ℝ (range q)
  have hK : K.Nonempty := (range_nonempty q).mono (subset_convexHull ℝ _)
  have hcompact : IsCompact K := (finite_range q).isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨z, hz, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hK hcompact.isComplete (convex_convexHull ℝ _) 0
  have hsupport :=
    (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _) hz).mp hmin
  refine ⟨z, hz, fun i => ?_⟩
  have h := hsupport (q i) (subset_convexHull ℝ _ (mem_range_self i))
  simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
  linarith

omit [FiniteDimensional ℝ E] in
/-- A simplex with unit vertices and a common inner-product lower bound has
a corresponding lower bound on the norm of each of its convex combinations. -/
private theorem norm_sq_convex_sum {ι : Type*} [Fintype ι]
    (p : ι → E) (w : ι → ℝ) {c : ℝ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hp : ∀ i, ‖p i‖ = 1) (hc : ∀ i j, i ≠ j → c ≤ ⟪p i, p j⟫_ℝ) :
    c + (1 - c) * ∑ i, w i ^ 2 ≤ ‖∑ i, w i • p i‖ ^ 2 := by
  classical
  let lower (i j : ι) := c * (w i * w j) + if i = j then (1 - c) * w i ^ 2 else 0
  have hsum (i : ι) : ∑ j, lower i j = c * w i + (1 - c) * w i ^ 2 := by
    simp [lower, ← mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  calc
    c + (1 - c) * ∑ i, w i ^ 2 = ∑ i, ∑ j, lower i j := by
      simp [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
    _ ≤ ∑ i, ∑ j, w i * w j * ⟪p i, p j⟫_ℝ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      by_cases hij : i = j
      · subst j
        simp [lower, hp]
        nlinarith
      · simpa [lower, hij, mul_comm c] using
          mul_le_mul_of_nonneg_left (hc i j hij) (mul_nonneg (hw i) (hw j))
    _ = _ := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
        mul_assoc]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        rw [real_inner_comm (p i) (p j)]))

omit [FiniteDimensional ℝ E] in
/-- Positive-weight vertices in a convex representation of a nearest point
lie on its supporting hyperplane. -/
private theorem eq_of_support {ι : Type*} [Fintype ι] (p : ι → E) (w : ι → ℝ) (z : E)
    (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) (hz : ∑ i, w i • p i = z)
    (h : ∀ i, ‖z‖ ^ 2 ≤ ⟪z, p i⟫_ℝ) (i : ι) :
    ⟪z, p i⟫_ℝ = ‖z‖ ^ 2 := by
  classical
  have hsum : ∑ j, w j * (⟪z, p j⟫_ℝ - ‖z‖ ^ 2) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← real_inner_smul_right,
      ← inner_sum, hz, ← Finset.sum_mul, hs, one_mul, real_inner_self_eq_norm_sq, sub_self]
  have hi := Finset.single_le_sum (f := fun j => w j * (⟪z, p j⟫_ℝ - ‖z‖ ^ 2))
    (fun j _ => mul_nonneg (hw j).le (sub_nonneg.mpr (h j))) (Finset.mem_univ i)
  rw [hsum] at hi
  exact le_antisymm (sub_nonpos.mp (nonpos_of_mul_nonpos_right hi (hw i))) (h i)

/-- A finite family of unit vectors admits the spherical Jung cap with support
bounded by both its own cardinality and the ambient dimension. -/
theorem exists_cap {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → E)
    (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card ι ≤ n ∨ Module.finrank ℝ E ≤ n)
    (hq : ∀ i, ‖q i‖ = 1) {c : ℝ} (hc : c ≤ 1)
    (hpair : ∀ i j, i ≠ j → c ≤ ⟪q i, q j⟫_ℝ)
    (hzero : (0 : E) ∉ convexHull ℝ (range q)) :
    ∃ v : E, ‖v‖ = 1 ∧ ∀ i, Real.sqrt (c + (1 - c) / n) ≤ ⟪v, q i⟫_ℝ := by
  classical
  obtain ⟨z, hz, hsupport⟩ := exists_min_norm_support q
  have hzn : z ≠ 0 := fun he => hzero (he ▸ hz)
  obtain ⟨κ, _, p, w, hp, hlin, hw, hsum, hzw⟩ :=
    eq_pos_convex_span_of_mem_convexHull hz
  choose f hf using fun j => hp (mem_range_self j)
  have hnorm (j : κ) : ‖p j‖ = 1 := hf j ▸ hq (f j)
  have hinner (i j : κ) (hij : i ≠ j) : c ≤ ⟪p i, p j⟫_ℝ := by
    have hne : f i ≠ f j := fun he => hij (hlin.injective ((hf i).symm.trans (he ▸ hf j)))
    rw [← hf i, ← hf j]
    exact hpair _ _ hne
  have hcκ : Fintype.card κ ≤ n := by
    rcases hcard with hcard | hdim
    · refine (Fintype.card_le_of_injective f ?_).trans hcard
      intro i j he
      exact hlin.injective ((hf i).symm.trans (he ▸ hf j))
    · let L := (ℝ ∙ z : Submodule ℝ E)
      have hrank : Module.finrank ℝ L = 1 := finrank_span_singleton hzn
      have horth := L.finrank_add_finrank_orthogonal
      have hcontact (i : κ) : ⟪z, p i⟫_ℝ = ‖z‖ ^ 2 :=
        eq_of_support p w z hw hsum hzw (fun j => hf j ▸ hsupport (f j)) i
      have hsub : vectorSpan ℝ (range p) ≤ Lᗮ := by
        by_cases hκ : Nonempty κ
        · obtain ⟨k⟩ := hκ
          rw [vectorSpan_eq_span_vsub_set_right ℝ (mem_range_self k), Submodule.span_le]
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          change (p i - p k) ∈ (ℝ ∙ z : Submodule ℝ E)ᗮ
          rw [Submodule.mem_orthogonal_singleton_iff_inner_left,
            real_inner_comm z (p i - p k), inner_sub_right, hcontact, hcontact, sub_self]
        · let : IsEmpty κ := not_nonempty_iff.mp hκ
          simp at hsum
      have hv := Submodule.finrank_mono hsub
      have hi := hlin.card_le_finrank_succ
      omega
  have hsq : 1 ≤ (n : ℝ) * ∑ i, w i ^ 2 := by
    have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
    rw [hsum, one_pow, Finset.card_univ] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcκ)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hsn : (0 : ℝ) < n := by exact_mod_cast hn
  have hrecip : 1 / (n : ℝ) ≤ ∑ i, w i ^ 2 :=
    (div_le_iff₀ hsn).mpr (by rwa [mul_comm])
  have hbound := norm_sq_convex_sum p w (fun i => (hw i).le) hsum hnorm hinner
  rw [hzw] at hbound
  have hzbound : c + (1 - c) / n ≤ ‖z‖ ^ 2 := by
    calc
      c + (1 - c) / n = c + (1 - c) * (1 / n) := by ring
      _ ≤ c + (1 - c) * ∑ i, w i ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hrecip (sub_nonneg.mpr hc))
      _ ≤ _ := hbound
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hzn
  refine ⟨‖z‖⁻¹ • z, by simp [norm_smul, hznorm.ne'], ?_⟩
  intro i
  have hsqrt : Real.sqrt (c + (1 - c) / n) ≤ ‖z‖ :=
    Real.sqrt_le_iff.mpr ⟨hznorm.le, hzbound⟩
  rw [real_inner_smul_left, ← div_eq_inv_mul, le_div_iff₀ hznorm]
  exact (mul_le_mul_of_nonneg_right hsqrt hznorm.le).trans (by simpa [pow_two] using hsupport i)

omit [FiniteDimensional ℝ E] in
/-- Nonnegative pairwise inner products exclude the origin from the convex hull. -/
theorem zero_not_mem_convexHull_of_pairwise_nonneg {ι : Type*} [Fintype ι] (q : ι → E)
    (hq : ∀ i, ‖q i‖ = 1) (hpair : ∀ i j, 0 ≤ ⟪q i, q j⟫_ℝ) :
    (0 : E) ∉ convexHull ℝ (range q) := by
  intro hz
  obtain ⟨κ, _, p, w, hp, _, hw, hsum, hzw⟩ :=
    eq_pos_convex_span_of_mem_convexHull hz
  choose f hf using fun j => hp (mem_range_self j)
  have hnorm (j : κ) : ‖p j‖ = 1 := hf j ▸ hq (f j)
  have hinner (i j : κ) : 0 ≤ ⟪p i, p j⟫_ℝ := by
    rw [← hf i, ← hf j]
    exact hpair _ _
  have h := norm_sq_convex_sum p w (fun i => (hw i).le) hsum hnorm
    (fun i j _ => hinner i j)
  rw [hzw] at h
  simp only [zero_add, sub_zero, one_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
  rw [hsum, one_pow] at hcs
  have hm := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) (Finset.univ : Finset κ).card) h
  linarith

omit [FiniteDimensional ℝ E] in
/-- A finite family of at most `n` unit vectors with a positive simplex
cosine bound has a convex hull excluding the origin. -/
theorem zero_not_mem_convexHull_of_card_bound {ι : Type*} [Fintype ι]
    (q : ι → E) (n : ℕ) (hn : 0 < n) (hcard : Fintype.card ι ≤ n)
    (hq : ∀ i, ‖q i‖ = 1) {c : ℝ} (hc : c ≤ 1)
    (hpair : ∀ i j, i ≠ j → c ≤ ⟪q i, q j⟫_ℝ)
    (hpos : 0 < c + (1 - c) / n) : (0 : E) ∉ convexHull ℝ (range q) := by
  classical
  intro hz
  obtain ⟨κ, _, p, w, hp, hlin, hw, hsum, hzw⟩ :=
    eq_pos_convex_span_of_mem_convexHull hz
  choose f hf using fun j => hp (mem_range_self j)
  have hinj : Function.Injective f := by
    intro i j he
    exact hlin.injective ((hf i).symm.trans (he ▸ hf j))
  have hbound := norm_sq_convex_sum p w (fun i => (hw i).le) hsum
    (fun i => hf i ▸ hq (f i)) (fun i j hij => by
      rw [← hf i, ← hf j]
      exact hpair (f i) (f j) (fun he => hij (hinj he)))
  rw [hzw, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hbound
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
  rw [hsum, one_pow, Finset.card_univ] at hs
  have hle : (Fintype.card κ : ℝ) ≤ n := by
    exact_mod_cast (Fintype.card_le_of_injective f hinj).trans hcard
  have hsn : (0 : ℝ) < n := by exact_mod_cast hn
  have hrecip : 1 / (n : ℝ) ≤ ∑ i, w i ^ 2 := by
    apply (div_le_iff₀ hsn).mpr
    rw [mul_comm]
    exact hs.trans (mul_le_mul_of_nonneg_right hle
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have h := mul_le_mul_of_nonneg_left hrecip (sub_nonneg.mpr hc)
  rw [div_eq_mul_inv, one_mul] at h
  rw [div_eq_mul_inv] at hpos
  nlinarith only [h, hpos, hbound]


omit [FiniteDimensional ℝ E] in
/-- A convex combination of a finite family can use zero weights at all
unused indices, even if some family values coincide. -/
theorem exists_weights_of_mem_convexHull {ι : Type*} [Fintype ι] {q : ι → E} {z : E}
    (hz : z ∈ convexHull ℝ (range q)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∑ i, w i • q i) = z := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hz
  obtain ⟨s, w, hw, hs, hz⟩ := hz
  refine ⟨fun i => if i ∈ s then w i else 0, fun i => ?_, ?_, ?_⟩
  · change 0 ≤ if i ∈ s then w i else 0
    split_ifs with hi
    · exact hw i hi
    · exact le_rfl
  · rw [← Finset.sum_filter]
    simpa using hs
  · simp only [ite_smul, zero_smul, ← Finset.sum_filter]
    rw [Finset.affineCombination_eq_linear_combination s q w hs] at hz
    simpa using hz


/-- A nonzero nearest point of a finite convex hull admits a positive
convex representation on its supporting affine hyperplane. -/
theorem exists_contact_weights {ι : Type*} [Fintype ι] {q : ι → E} {z : E}
    (hz : z ∈ convexHull ℝ (range q)) (hzn : z ≠ 0)
    (hsupport : ∀ i, ‖z‖ ^ 2 ≤ ⟪z, q i⟫_ℝ) :
    ∃ (κ : Type u) (_ : Fintype κ) (f : κ → ι) (w : κ → ℝ),
      Fintype.card κ ≤ Module.finrank ℝ E ∧ (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • q (f i)) = z := by
  classical
  obtain ⟨κ, _, p, w, hp, hlin, hw, hsum, hzw⟩ :=
    eq_pos_convex_span_of_mem_convexHull hz
  choose f hf using fun i => hp (mem_range_self i)
  refine ⟨κ, inferInstance, f, w, ?_, hw, hsum, ?_⟩
  · let L := (ℝ ∙ z : Submodule ℝ E)
    have hrank : Module.finrank ℝ L = 1 := finrank_span_singleton hzn
    have horth := L.finrank_add_finrank_orthogonal
    have hcontact (i : κ) : ⟪z, p i⟫_ℝ = ‖z‖ ^ 2 :=
      eq_of_support p w z hw hsum hzw (fun j => hf j ▸ hsupport (f j)) i
    have hsub : vectorSpan ℝ (range p) ≤ Lᗮ := by
      cases isEmpty_or_nonempty κ with
      | inl h =>
        let : IsEmpty κ := h
        simp at hsum
      | inr h =>
        let k := h.some
        rw [vectorSpan_eq_span_vsub_set_right ℝ (mem_range_self k), Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        change (p i - p k) ∈ (ℝ ∙ z : Submodule ℝ E)ᗮ
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left, real_inner_comm z (p i - p k),
          inner_sub_right, hcontact, hcontact, sub_self]
    have hv := Submodule.finrank_mono hsub
    have hi := hlin.card_le_finrank_succ
    omega
  · simpa only [hf] using hzw

end Omega.Geometry.SphericalJung
