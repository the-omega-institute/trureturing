/- GID: D5/S3/Fourier/Concentration/CyclicDisjointOccupationCoefficient
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CyclicDisjointOccupationCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Character projection of disjoint occupation coefficients. -/

import D5.S3.Fourier.Concentration.DisjointSupportOccupationMass
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Fourier.ZMod

/-! Character projection of the disjoint occupation mass onto a cyclic band. -/

set_option autoImplicit false

open Finset

noncomputable section

open D5.S3.Fourier.Concentration.DisjointSupportOccupationMass (coordinateBox)
open D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass (weight_factorials)

namespace D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient

open Classical in
private theorem coefficient_expansion {J M A : Type*} [Fintype J] [AddCommMonoid M] [DecidableEq M]
    [CommSemiring A] (d : ℕ) (loc : J → ℕ × ℕ → M) (c : J → ℕ × ℕ → A) (target : M) :
    (∏ j, ∑ p ∈ coordinateBox d,
      AddMonoidAlgebra.single (loc j p) (c j p) : AddMonoidAlgebra A M).coeff target =
      ∑ f ∈ Fintype.piFinset (fun _ : J => coordinateBox d),
        if (∑ j, loc j (f j)) = target then ∏ j, c j (f j) else 0 := by
  rw [prod_univ_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine sum_congr rfl fun f _ => ?_
  rw [AddMonoidAlgebra.prod_single]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

open Classical in
private theorem prod_local_expansion {J K : Type*} [Fintype J] [AddCommGroup K]
    (d : ℕ) (a : J → K) (w : J → ℝ) (yield : ℕ × (ℕ × K)) :
    let loc := fun (j : J) (p : ℕ × ℕ) => (p.1, p.2, (p.1 : ℤ) • a j - (p.2 : ℤ) • a j)
    let c := fun (j : J) (p : ℕ × ℕ) =>
      w j ^ (p.1 + p.2) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))
    (∏ j, ∑ p ∈ coordinateBox d,
      AddMonoidAlgebra.single (loc j p) (c j p) : AddMonoidAlgebra ℝ (ℕ × (ℕ × K))).coeff yield =
      ∑ f ∈ Fintype.piFinset (fun _ : J => coordinateBox d),
        if (∑ j, loc j (f j)) = yield then ∏ j, c j (f j) else 0 := by
  intro loc c
  exact coefficient_expansion d loc c yield

open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)

open Classical in
private theorem occupational_fiber {J K : Type*} [Fintype J] [DecidableEq J] [AddCommGroup K]
    (a : J → K) (d : ℕ) (r : K) (m n : J → ℕ) :
    (∀ j, (m j, n j) ∈ coordinateBox d) ∧
      (∑ j, (m j, n j, (m j : ℤ) • a j - (n j : ℤ) • a j)) = (d, d, r) ↔
    m ∈ piAntidiag univ d ∧ n ∈ piAntidiag univ d ∧
      (∀ j, m j = 0 ∨ n j = 0) ∧ (∑ j, ((m j : ℤ) • a j - (n j : ℤ) • a j)) = r := by
  have hpair : ∑ j, (m j, n j, (m j : ℤ) • a j - (n j : ℤ) • a j) =
      (∑ j, m j, ∑ j, n j, ∑ j, ((m j : ℤ) • a j - (n j : ℤ) • a j)) := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [hpair]
  simp only [Prod.mk.injEq, mem_piAntidiag, mem_univ, implies_true, and_true]
  constructor
  · rintro ⟨hbox, hm, hn, hr⟩
    refine ⟨hm, hn, ?_, hr⟩
    intro j
    exact (mem_filter.mp (hbox j)).2
  · rintro ⟨hm, hn, hzero, hr⟩
    refine ⟨fun j => ?_, hm, hn, hr⟩
    have hsum (u : J → ℕ) (hu : ∑ k, u k = d) : u j ∈ range (d + 1) := by
      rw [mem_range, Nat.lt_succ_iff, ← hu]
      exact single_le_sum (fun k _ => Nat.zero_le (u k)) (mem_univ j)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hsum m hm, hsum n hn⟩, hzero j⟩

open Classical in
private theorem disjoint_coeff {J K : Type*} [Fintype J] [DecidableEq J] [AddCommGroup K]
    (d : ℕ) (a : J → K) (w : J → ℝ) (r : K) :
    let loc := fun (j : J) (p : ℕ × ℕ) => (p.1, p.2, (p.1 : ℤ) • a j - (p.2 : ℤ) • a j)
    let c := fun (j : J) (p : ℕ × ℕ) =>
      w j ^ (p.1 + p.2) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))
    (d.factorial : ℝ) ^ 2 *
      (∏ j, ∑ p ∈ coordinateBox d,
        AddMonoidAlgebra.single (loc j p) (c j p) : AddMonoidAlgebra ℝ (ℕ × (ℕ × K))).coeff
        (d, d, r) =
    ∑ p ∈ (piAntidiag univ d ×ˢ piAntidiag univ d).filter
      (fun p : (J → ℕ) × (J → ℕ) =>
        (∀ j, p.1 j = 0 ∨ p.2 j = 0) ∧
        (∑ j, ((p.1 j : ℤ) • a j - (p.2 j : ℤ) • a j)) = r),
      monomialWeight w p.1 * monomialWeight w p.2 := by
  intro loc c
  classical
  let e : ((J → ℕ) × (J → ℕ)) ≃ (J → ℕ × ℕ) :=
    (Equiv.arrowProdEquivProdArrow J (fun _ => ℕ) (fun _ => ℕ)).symm
  let P := (piAntidiag (univ : Finset J) d ×ˢ piAntidiag univ d).filter
    (fun p => (∀ j, p.1 j = 0 ∨ p.2 j = 0) ∧
      (∑ j, ((p.1 j : ℤ) • a j - (p.2 j : ℤ) • a j)) = r)
  let Q := (Fintype.piFinset (fun _ : J => coordinateBox d)).filter
    (fun f => (∑ j, loc j (f j)) = (d, d, r))
  have hmem (p : (J → ℕ) × (J → ℕ)) : e p ∈ Q ↔ p ∈ P := by
    simp only [Q, P, mem_filter, Fintype.mem_piFinset, mem_product, and_assoc]
    exact occupational_fiber a d r p.1 p.2
  have hmap : P.map e.toEmbedding = Q := by
    ext f
    obtain ⟨p, rfl⟩ := e.surjective f
    rw [hmem p]
    simp
  change _ = ∑ p ∈ P, monomialWeight w p.1 * monomialWeight w p.2
  rw [show _ = _ from prod_local_expansion d a w (d, d, r), ← sum_filter, mul_sum]
  have hsum : (∑ f ∈ Q, (d.factorial : ℝ) ^ 2 * ∏ j, c j (f j)) =
      ∑ p ∈ P, monomialWeight w p.1 * monomialWeight w p.2 := by
    rw [← hmap, sum_map]
    refine sum_congr rfl fun p hp => ?_
    have hdegree := mem_product.mp (mem_filter.mp hp).1
    rw [weight_factorials w d p.1 (mem_piAntidiag.mp hdegree.1).1,
      weight_factorials w d p.2 (mem_piAntidiag.mp hdegree.2).1]
    have hprod : (∏ j, c j (e.toEmbedding p j)) =
        (∏ j, w j ^ p.1 j / ((p.1 j).factorial : ℝ)) *
          ∏ j, w j ^ p.2 j / ((p.2 j).factorial : ℝ) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      change w j ^ (p.1 j + p.2 j) / (((p.1 j).factorial : ℝ) * ((p.2 j).factorial : ℝ)) = _
      rw [pow_add, div_mul_div_comm]
    rw [hprod, sq, mul_mul_mul_comm]
  convert hsum using 2
  ext f
  simp [Q, loc]

open Classical in
theorem band_via_dft {q : ℕ} [NeZero q] (F : ZMod q → ℂ) (R : Finset (ZMod q)) :
    (q : ℂ) * (∑ r ∈ R, F r) =
      ∑ k : ZMod q, ZMod.dft F k * ∑ r ∈ R, ZMod.stdAddChar (k * r) := by
  rw [mul_sum]
  calc
    _ = ∑ r ∈ R, ZMod.dft (ZMod.dft F) (-r) := by
      simp [ZMod.dft_dft, smul_eq_mul]
    _ = _ := by
      simp only [ZMod.dft_apply (ZMod.dft F), mul_neg, neg_neg, smul_eq_mul]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun r _ => mul_comm _ _

open Classical in
private theorem cyclic_disjoint_projection {J : Type*} [Fintype J] [DecidableEq J]
    {q : ℕ} [NeZero q] (d : ℕ) (a : J → ZMod q) (w : J → ℝ) (R : Finset (ZMod q)) :
    let P := ∏ j, ∑ p ∈ coordinateBox d,
      AddMonoidAlgebra.single (p.1, p.2, (p.1 : ℤ) • a j - (p.2 : ℤ) • a j)
        (w j ^ (p.1 + p.2) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)))
    let C : ZMod q → ℂ := fun r => ((d.factorial : ℝ) ^ 2 * P.coeff (d, d, r) : ℝ)
    (q : ℂ) * (∑ r ∈ R, (↑(∑ p ∈ (piAntidiag univ d ×ˢ piAntidiag univ d).filter
      (fun p : (J → ℕ) × (J → ℕ) =>
        (∀ j, p.1 j = 0 ∨ p.2 j = 0) ∧
        (∑ j, ((p.1 j : ℤ) • a j - (p.2 j : ℤ) • a j)) = r),
      monomialWeight w p.1 * monomialWeight w p.2) : ℂ)) =
      ∑ k : ZMod q, ZMod.dft C k * ∑ r ∈ R, ZMod.stdAddChar (k * r) := by
  intro P C
  rw [← band_via_dft C R]
  congr 1
  refine sum_congr rfl fun r _ => congrArg Complex.ofReal ?_
  convert (disjoint_coeff d a w r).symm using 2
  ext pair
  simp

open Classical in
private theorem dft_product {J : Type*} [Fintype J]
    {q : ℕ} [NeZero q] (d : ℕ) (a : J → ZMod q) (w : J → ℝ) (k : ZMod q) :
    let gap (j : J) (p : ℕ × ℕ) := (p.1 : ℤ) • a j - (p.2 : ℤ) • a j
    let c (j : J) (p : ℕ × ℕ) :=
      w j ^ (p.1 + p.2) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))
    let P : AddMonoidAlgebra ℝ (ℕ × ℕ × ZMod q) :=
      ∏ j, ∑ p ∈ coordinateBox d, AddMonoidAlgebra.single (p.1, p.2, gap j p) (c j p)
    let Q : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
      ∏ j, ∑ p ∈ coordinateBox d,
        AddMonoidAlgebra.single p ((c j p : ℂ) * ZMod.stdAddChar (-(gap j p * k)))
    ZMod.dft (fun r => (P.coeff (d, d, r) : ℂ)) k = Q.coeff (d, d) := by
  intro gap c P Q
  classical
  let T := Fintype.piFinset (fun _ : J => coordinateBox d)
  let loc (j : J) (p : ℕ × ℕ) := (p.1, p.2, gap j p)
  have hsum (f : J → ℕ × ℕ) :
      (∑ j, loc j (f j)) = ((∑ j, f j).1, (∑ j, f j).2, ∑ j, gap j (f j)) := by
    ext <;> simp [loc, Prod.fst_sum, Prod.snd_sum]
  have hP (r : ZMod q) : P.coeff (d, d, r) =
      ∑ f ∈ T, if (∑ j, loc j (f j)) = (d, d, r) then ∏ j, c j (f j) else 0 :=
    coefficient_expansion d loc c _
  have hQ : Q.coeff (d, d) = ∑ f ∈ T, if (∑ j, f j) = (d, d)
      then ∏ j, ((c j (f j) : ℂ) * ZMod.stdAddChar (-(gap j (f j) * k))) else 0 :=
    coefficient_expansion d (fun _ p => p) _ _
  rw [ZMod.dft_apply, hQ]
  simp only [hP, Complex.ofReal_sum, smul_eq_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  simp only [hsum, Prod.ext_iff, apply_ite Complex.ofReal, Complex.ofReal_zero, mul_ite, mul_zero, ← and_assoc]
  by_cases hd : (∑ j, f j).1 = d ∧ (∑ j, f j).2 = d
  · let u := ∑ j, gap j (f j)
    have hchar : (∏ j, ZMod.stdAddChar (-(gap j (f j) * k))) =
        ZMod.stdAddChar (-(u * k)) := by
      rw [show -(u * k) = ∑ j, -(gap j (f j) * k) by simp [u, sum_mul, sum_neg_distrib]]
      generalize (univ : Finset J) = S
      induction S using Finset.induction_on with
      | empty => simp
      | insert j S hj ih =>
        rw [sum_insert hj, prod_insert hj, AddChar.map_add_eq_mul, ih]
    have hchar' : (∏ j, ZMod.stdAddChar (-(k * gap j (f j)))) =
        ZMod.stdAddChar (-(k * ∑ j, gap j (f j))) := by
      simpa only [u, mul_comm] using hchar
    simp [hd.1, hd.2, prod_mul_distrib, hchar', mul_comm]
  · simp [hd]

open Classical in
/-- The cyclic band mass of disjoint occupations is recovered from the mixed
coefficient of the local character products. -/
theorem cyclic_disjoint_band_product {J : Type*} [Fintype J] [DecidableEq J]
    {q : ℕ} [NeZero q] (d : ℕ) (a : J → ZMod q) (w : J → ℝ) (R : Finset (ZMod q)) :
    let scale := fun n : ℕ => (n.factorial : ℂ) ^ 2
    let Q (k : ZMod q) : AddMonoidAlgebra ℂ (ℕ × ℕ) :=
      ∏ j, ∑ p ∈ coordinateBox d,
        AddMonoidAlgebra.single p
          ((w j ^ (p.1 + p.2) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) : ℝ) *
            ZMod.stdAddChar (-(((p.1 : ℤ) • a j - (p.2 : ℤ) • a j) * k)))
    (q : ℂ) * (∑ r ∈ R, (↑(∑ p ∈ (piAntidiag univ d ×ˢ piAntidiag univ d).filter
      (fun p : (J → ℕ) × (J → ℕ) =>
        (∀ j, p.1 j = 0 ∨ p.2 j = 0) ∧
        (∑ j, ((p.1 j : ℤ) • a j - (p.2 j : ℤ) • a j)) = r),
      monomialWeight w p.1 * monomialWeight w p.2) : ℂ)) =
       scale d *
        ∑ k : ZMod q, (Q k).coeff (d, d) * ∑ r ∈ R, ZMod.stdAddChar (k * r) := by
  intro scale Q
  have h := cyclic_disjoint_projection d a w R
  convert h using 1
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_assoc]
  congr 1
  have hDft := dft_product d a w k
  dsimp only at hDft
  rw [← hDft]
  dsimp [scale]
  push_cast
  exact (congrFun (ZMod.dft_const_mul ((d.factorial : ℂ) ^ 2) _) k).symm

end D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient
