/- GID: D5/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/AffineDeterminantAntisymmetricForms
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Low-degree alternating polynomials in vector variables are affine determinants. -/

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-! Low-degree alternation in vector variables and the affine determinant. -/

noncomputable section

namespace D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms

open MvPolynomial Finset

/-- A permutation of vector variables preserves the coordinate within each vector. -/
def blockPerm {r d : ℕ} (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm (Fin r × Fin d) :=
  Equiv.prodCongr σ (Equiv.refl _)

/-- Alternation under permutations of the vector variables. -/
def IsAlternating {r d : ℕ} (f : MvPolynomial (Fin r × Fin d) ℂ) : Prop :=
  ∀ σ : Equiv.Perm (Fin r),
    rename (blockPerm σ) f = (((Equiv.Perm.sign σ : ℤ) : ℂ)) • f

/-- The determinant with columns the differences from the first point. -/
def affineDet (d : ℕ) : MvPolynomial (Fin (d + 1) × Fin d) ℂ :=
  Matrix.det (fun j k : Fin d => X (k.succ, j) - X (0, j))

/-- Vanishing for every first point forces affine dimension at most `d - 2`. -/
def IsNondegenerate (d : ℕ) (ω : (Fin (d + 1) → Fin d → ℂ) → ℂ) : Prop :=
  ∀ x : Fin d → (Fin d → ℂ),
    (∀ x₀, ω (Fin.cons x₀ x) = 0) →
      Module.finrank ℂ (affineSpan ℂ (Set.range x)).direction ≤ d - 2

private def canonical (d : ℕ) : (Fin (d + 1) × Fin d) →₀ ℕ :=
  ∑ k : Fin d, Finsupp.single (k.succ, k) 1

private lemma coeff_permuted {r d : ℕ} {f : MvPolynomial (Fin r × Fin d) ℂ}
    (ha : IsAlternating f) (σ : Equiv.Perm (Fin r)) (m : (Fin r × Fin d) →₀ ℕ) :
    f.coeff (m.mapDomain (blockPerm σ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * f.coeff m := by
  have h := coeff_rename_mapDomain (blockPerm σ) (blockPerm σ).injective f m
  rw [ha σ, coeff_smul] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using h
  · simp only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      smul_eq_mul] at h ⊢
    linear_combination -h

private lemma equal_rows_coeff_zero {r d : ℕ}
    {f : MvPolynomial (Fin r × Fin d) ℂ} (ha : IsAlternating f)
    (m : (Fin r × Fin d) →₀ ℕ) {a b : Fin r} (hab : a ≠ b)
    (he : ∀ j, m (a, j) = m (b, j)) : f.coeff m = 0 := by
  classical
  have hm : m.mapDomain (blockPerm (Equiv.swap a b)) = m := by
    ext ⟨i, j⟩
    rw [Finsupp.mapDomain_equiv_apply]
    change m (Equiv.swap a b i, j) = m (i, j)
    by_cases hpa : i = a
    · simpa [hpa] using (he j).symm
    by_cases hpb : i = b
    · simpa [hpb] using he j
    · simp [Equiv.swap_apply_of_ne_of_ne hpa hpb]
  have h := coeff_permuted ha (Equiv.swap a b) m
  rw [hm, Equiv.Perm.sign_swap hab] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  linear_combination h / 2

private lemma support_rows_distinct {r d : ℕ}
    {f : MvPolynomial (Fin r × Fin d) ℂ} (ha : IsAlternating f)
    {m : (Fin r × Fin d) →₀ ℕ} (hm : m ∈ f.support) :
    Function.Injective (fun i : Fin r => fun j : Fin d => m (i, j)) := by
  intro a b he
  by_contra hab
  exact (mem_support_iff.mp hm) (equal_rows_coeff_zero ha m hab (congrFun he))

private lemma exponent_sum {r d : ℕ} (m : (Fin r × Fin d) →₀ ℕ) :
    m.sum (fun _ n => n) = ∑ i : Fin r, ∑ j : Fin d, m (i, j) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]

private lemma row_count_bound {r d : ℕ} (m : (Fin r × Fin d) →₀ ℕ)
    (hi : Function.Injective (fun i : Fin r => fun j : Fin d => m (i, j))) :
    r ≤ m.sum (fun _ n => n) + 1 := by
  classical
  rw [exponent_sum]
  by_cases hz : ∃ z, ∀ j, m (z, j) = 0
  · obtain ⟨z, hz⟩ := hz
    have hp (i : Fin r) (hiz : i ≠ z) : 1 ≤ ∑ j : Fin d, m (i, j) := by
      by_contra h
      have hs : (∑ j : Fin d, m (i, j)) = 0 := by omega
      have he : (fun j : Fin d => m (i, j)) = fun j => m (z, j) := by
        funext j
        have hj := (Finset.sum_eq_zero_iff.mp hs) j (mem_univ j)
        exact hj.trans (hz j).symm
      exact hiz (hi he)
    have hl := Finset.sum_le_sum (s := univ.erase z) (f := fun _ => 1)
      (g := fun i => ∑ j : Fin d, m (i, j)) (fun i hi => hp i (mem_erase.mp hi).1)
    have hu := Finset.sum_le_sum_of_subset_of_nonneg (erase_subset z univ)
      (fun i _ _ => Nat.zero_le (∑ j : Fin d, m (i, j)))
    have hc : (univ.erase z).card = r - 1 := by simp
    simp only [sum_const, smul_eq_mul, mul_one] at hl
    have hr : 0 < r := Nat.zero_lt_of_lt z.isLt
    omega
  · push Not at hz
    have hp (i : Fin r) : 1 ≤ ∑ j : Fin d, m (i, j) := by
      obtain ⟨j, hj⟩ := hz i
      have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (m (i, j))) (mem_univ j)
      omega
    have h := Finset.sum_le_sum (s := univ) (f := fun _ : Fin r => 1)
      (g := fun i => ∑ j : Fin d, m (i, j)) (fun i _ => hp i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    omega

private lemma canonical_apply (d : ℕ) (i : Fin (d + 1)) (j : Fin d) :
    canonical d (i, j) = if i = j.succ then 1 else 0 := by
  classical
  unfold canonical
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · simp only [Finsupp.single_apply, Prod.mk.injEq, and_true, eq_comm]
  · intro k _ hkj
    simp only [Finsupp.single_apply, Prod.mk.injEq, hkj, and_false, ite_false]
  · simp

private lemma distinct_rows_orbit {d : ℕ}
    (m : (Fin (d + 1) × Fin d) →₀ ℕ)
    (hi : Function.Injective (fun i : Fin (d + 1) => fun j : Fin d => m (i, j)))
    (ht : m.sum (fun _ n => n) ≤ d) :
    ∃ σ : Equiv.Perm (Fin (d + 1)),
      (canonical d).mapDomain (blockPerm σ) = m := by
  classical
  let w : Fin (d + 1) → ℕ := fun i => ∑ j : Fin d, m (i, j)
  have ht : ∑ i, w i ≤ d := by simpa only [exponent_sum] using ht
  have hz : ∃ z, ∀ j, m (z, j) = 0 := by
    by_contra hn
    push Not at hn
    have hp (i : Fin (d + 1)) : 1 ≤ w i := by
      obtain ⟨j, hj⟩ := hn i
      have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (m (i, j))) (mem_univ j)
      dsimp only [w]
      omega
    have h := Finset.sum_le_sum (s := univ) (f := fun _ : Fin (d + 1) => 1)
      (g := w) (fun i _ => hp i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    omega
  obtain ⟨z, hz⟩ := hz
  have hwz : w z = 0 := by simp only [w, hz, sum_const_zero]
  have hp (i : Fin (d + 1)) (hiz : i ≠ z) : 1 ≤ w i := by
    by_contra hn
    have hs : (∑ j : Fin d, m (i, j)) = 0 := by change w i = 0; omega
    have he : (fun j : Fin d => m (i, j)) = fun j => m (z, j) := by
      funext j
      exact ((Finset.sum_eq_zero_iff.mp hs) j (mem_univ j)).trans (hz j).symm
    exact hiz (hi he)
  have hc : (univ.erase z).card = d := by simp
  have hl : (∑ i ∈ univ.erase z, 1) ≤ ∑ i ∈ univ.erase z, w i :=
    Finset.sum_le_sum (fun i hi => hp i (mem_erase.mp hi).1)
  have hu : (∑ i ∈ univ.erase z, w i) ≤ d := by
    have h := Finset.sum_erase_add univ w (mem_univ z)
    omega
  have heq : (∑ i ∈ univ.erase z, 1) = ∑ i ∈ univ.erase z, w i := by
    have hconst : (∑ i ∈ univ.erase z, 1) = d := by simp only [sum_const, hc,
      smul_eq_mul, mul_one]
    omega
  have hone (i : Fin (d + 1)) (hiz : i ≠ z) : w i = 1 :=
    ((Finset.sum_eq_sum_iff_of_le (fun i hi => hp i (mem_erase.mp hi).1)).mp heq
      i (mem_erase.mpr ⟨hiz, mem_univ i⟩)).symm
  have hrow (i : Fin (d + 1)) (hiz : i ≠ z) :
      ∃ k : Fin d, ∀ j, m (i, j) = if j = k then 1 else 0 := by
    let v : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => m (i, j))
    have hv : v.sum (fun _ n => n) = 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact hone i hiz
    obtain ⟨k, hk⟩ := (Finsupp.sum_eq_one_iff v).mp hv
    refine ⟨k, fun j => ?_⟩
    have h := congrArg (fun v : Fin d →₀ ℕ => v j) hk
    change m (i, j) = (Finsupp.single k 1 : Fin d →₀ ℕ) j at h
    simpa only [Finsupp.single_apply, eq_comm] using h
  let e : Fin (d + 1) → Fin (d + 1) :=
    fun i => if h : i = z then 0 else (Classical.choose (hrow i h)).succ
  have hrep (i : Fin (d + 1)) (j : Fin d) : m (i, j) = canonical d (e i, j) := by
    rw [canonical_apply]
    by_cases hiz : i = z
    · simp only [hiz, hz, e, dite_eq_left rfl, Ne.symm (Fin.succ_ne_zero j), ite_false]
    · simp only [e, dite_eq_right hiz, Fin.succ_inj]
      simpa only [eq_comm] using Classical.choose_spec (hrow i hiz) j
  have hei : Function.Injective e := by
    intro a b hab
    apply hi
    funext j
    change m (a, j) = m (b, j)
    rw [hrep a j, hrep b j, hab]
  let σ : Equiv.Perm (Fin (d + 1)) := Equiv.ofBijective e
    hei.bijective_of_finite
  refine ⟨σ.symm, ?_⟩
  ext ⟨i, j⟩
  rw [Finsupp.mapDomain_equiv_apply]
  exact (hrep i j).symm

private lemma support_orbit {d : ℕ}
    {f : MvPolynomial (Fin (d + 1) × Fin d) ℂ}
    (ha : IsAlternating f) (hd : f.totalDegree ≤ d)
    {m : (Fin (d + 1) × Fin d) →₀ ℕ} (hm : m ∈ f.support) :
    ∃ σ : Equiv.Perm (Fin (d + 1)),
      (canonical d).mapDomain (blockPerm σ) = m := by
  exact distinct_rows_orbit m (support_rows_distinct ha hm) ((le_totalDegree hm).trans hd)

private lemma too_many_rows {d r : ℕ} (hr : d + 2 ≤ r)
    (f : MvPolynomial (Fin r × Fin d) ℂ) (ha : IsAlternating f)
    (hd : f.totalDegree ≤ d) : f = 0 := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : m ∈ f.support
  · have h := row_count_bound m (support_rows_distinct ha hm)
    have ht := (le_totalDegree hm).trans hd
    have : False := by omega
    exact this.elim
  · change f.coeff m = 0
    exact notMem_support_iff.mp hm

private lemma affineDet_alternating (d : ℕ) : IsAlternating (affineDet d) := by
  sorry

private lemma affineDet_degree (d : ℕ) : (affineDet d).totalDegree ≤ d := by
  classical
  change (Matrix.of (fun j k : Fin d =>
    (X (k.succ, j) - X (0, j) : MvPolynomial (Fin (d + 1) × Fin d) ℂ))).det.totalDegree ≤ d
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ k : Fin d, 1 := Finset.sum_le_sum fun k _ =>
      (totalDegree_sub _ _).trans (by simp only [totalDegree_X, max_self, le_refl])
    _ = d := by simp

private lemma affineDet_coeff (d : ℕ) : (affineDet d).coeff (canonical d) = 1 := by
  sorry

private lemma zero_of_canonical_zero {d : ℕ}
    (f : MvPolynomial (Fin (d + 1) × Fin d) ℂ)
    (ha : IsAlternating f) (hd : f.totalDegree ≤ d)
    (hc : f.coeff (canonical d) = 0) : f = 0 := by
  apply MvPolynomial.ext
  intro m
  change f.coeff m = 0
  by_cases hm : m ∈ f.support
  · obtain ⟨σ, rfl⟩ := support_orbit ha hd hm
    rw [coeff_permuted ha, hc, mul_zero]
  · exact notMem_support_iff.mp hm

private lemma coefficient_determines {d : ℕ}
    (f : MvPolynomial (Fin (d + 1) × Fin d) ℂ)
    (ha : IsAlternating f) (hd : f.totalDegree ≤ d) :
    f = f.coeff (canonical d) • affineDet d := by
  apply sub_eq_zero.mp
  apply zero_of_canonical_zero
  · intro σ
    rw [map_sub, map_smul, ha σ, affineDet_alternating d σ, smul_sub,
      smul_smul, smul_smul, mul_comm]
  · exact (totalDegree_sub _ _).trans (max_le hd
      ((totalDegree_smul_le _ _).trans (affineDet_degree d)))
  · rw [coeff_sub, coeff_smul, affineDet_coeff, smul_eq_mul, mul_one, sub_self]

private lemma affineDet_nondegenerate (d : ℕ) (hd : 2 ≤ d) :
    IsNondegenerate d (fun y => eval (fun p => y p.1 p.2) (affineDet d)) := by
  sorry

/-- Low-degree alternation vanishes with too many vectors, and is otherwise the affine determinant. -/
theorem result :
    (∀ d r, d + 2 ≤ r → ∀ f : MvPolynomial (Fin r × Fin d) ℂ,
      IsAlternating f → f.totalDegree ≤ d → f = 0) ∧
    (∀ d, IsAlternating (affineDet d) ∧ (affineDet d).totalDegree ≤ d) ∧
    (∀ d (f : MvPolynomial (Fin (d + 1) × Fin d) ℂ),
      IsAlternating f → f.totalDegree ≤ d → ∃ c : ℂ, f = c • affineDet d) ∧
    (∀ d, 2 ≤ d →
      IsNondegenerate d (fun y => eval (fun p => y p.1 p.2) (affineDet d))) := by
  refine ⟨fun d r hr f ha hd => too_many_rows hr f ha hd,
    fun d => ⟨affineDet_alternating d, affineDet_degree d⟩,
    fun d f ha hd => ⟨f.coeff (canonical d), coefficient_determines f ha hd⟩,
    affineDet_nondegenerate⟩

end D5.S3.Quantum.Fermionic.AffineDeterminantAntisymmetricForms
