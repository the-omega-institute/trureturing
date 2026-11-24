/- GID: D5/S3/Fourier/Concentration/CommonResidualOccupationCoefficient
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CommonResidualOccupationCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-degree slices of cyclic occupation coefficients. -/

import D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient

open Finset
open D5.S3.Fourier.Concentration.CyclicDisjointOccupationCoefficient (band_via_dft)
open D5.S3.Fourier.Concentration.FixedDifferenceOccupationMass (weight_factorials)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)

/-! Cyclic near-collision coefficients by degree of common occupations. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient

open Classical in
private theorem coefficient_fiber {J M A : Type*} [Fintype J] [AddCommMonoid M]
    [DecidableEq M] [CommSemiring A] (S : J → Finset (ℕ × ℕ))
    (index : J → ℕ × ℕ → M) (weight : J → ℕ × ℕ → A) (target : M) :
    (∏ j, ∑ p ∈ S j, AddMonoidAlgebra.single (index j p) (weight j p) :
        AddMonoidAlgebra A M).coeff target =
      ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∑ j, index j (f j)) = target),
        ∏ j, weight j (f j) := by
  rw [prod_univ_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, sum_filter]
  apply sum_congr rfl
  intro f _
  rw [AddMonoidAlgebra.prod_single]
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

private theorem degree_pair_fiber {J K : Type*} [Fintype J] [DecidableEq J] [AddCommGroup K]
    (p : ℕ) (h : ℕ) (a : J → K) (r : K) (m n : J → ℕ) :
    (∀ j, (m j, n j) ∈ range (p + 1) ×ˢ range (p + 1)) ∧
      (∑ j, ((m j, n j, min (m j) (n j)),
        (m j : ℤ) • a j - (n j : ℤ) • a j)) = ((p, p, h), r) ↔
    m ∈ piAntidiag univ p ∧ n ∈ piAntidiag univ p ∧
      (∑ j, min (m j) (n j)) = h ∧
      (∑ j, ((m j : ℤ) • a j - (n j : ℤ) • a j)) = r := by
  have hsum :
      (∑ j, ((m j, n j, min (m j) (n j)), (m j : ℤ) • a j - (n j : ℤ) • a j)) =
      (((∑ j, m j), (∑ j, n j), (∑ j, min (m j) (n j))),
        (∑ j, ((m j : ℤ) • a j - (n j : ℤ) • a j))) := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [hsum]
  simp only [Prod.mk.injEq, mem_piAntidiag, mem_univ, implies_true, and_true]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨hm, hn, hc⟩, hr⟩
    exact ⟨hm, hn, hc, hr⟩
  rintro ⟨hm, hn, hc, hr⟩
  refine ⟨fun j => ?_, ⟨hm, hn, hc⟩, hr⟩
  have hbound (u : J → ℕ) (hu : ∑ k, u k = p) : u j ∈ range (p + 1) := by
    rw [mem_range, Nat.lt_succ_iff, ← hu]
    exact single_le_sum (fun k _ => Nat.zero_le (u k)) (mem_univ j)
  exact mem_product.mpr ⟨hbound m hm, hbound n hn⟩

open Classical in
private theorem common_residual_coefficient {J K : Type*} [Fintype J] [DecidableEq J] [AddCommGroup K]
    (p h : ℕ) (a : J → K) (w : J → ℝ) (r : K) :
    let S := fun _ : J => range (p + 1) ×ˢ range (p + 1)
    let index := fun (j : J) (v : ℕ × ℕ) =>
      ((v.1, v.2, min v.1 v.2), (v.1 : ℤ) • a j - (v.2 : ℤ) • a j)
    let weight := fun (j : J) (v : ℕ × ℕ) =>
      w j ^ (v.1 + v.2) / ((v.1.factorial : ℝ) * (v.2.factorial : ℝ))
    (p.factorial : ℝ) ^ 2 * (∏ j, ∑ v ∈ S j,
      AddMonoidAlgebra.single (index j v) (weight j v) :
        AddMonoidAlgebra ℝ ((ℕ × ℕ × ℕ) × K)).coeff ((p, p, h), r) =
    ∑ u ∈ (piAntidiag univ p ×ˢ piAntidiag univ p).filter
      (fun u : (J → ℕ) × (J → ℕ) => (∑ j, min (u.1 j) (u.2 j)) = h ∧
        (∑ j, ((u.1 j : ℤ) • a j - (u.2 j : ℤ) • a j)) = r),
      monomialWeight w u.1 * monomialWeight w u.2 := by
  intro S index weight
  classical
  let e := (Equiv.arrowProdEquivProdArrow J (fun _ => ℕ) (fun _ => ℕ)).symm
  let left := (Fintype.piFinset S).filter (fun f => (∑ j, index j (f j)) = ((p, p, h), r))
  let right := (piAntidiag (univ : Finset J) p ×ˢ piAntidiag univ p).filter
    (fun u => (∑ j, min (u.1 j) (u.2 j)) = h ∧
      (∑ j, ((u.1 j : ℤ) • a j - (u.2 j : ℤ) • a j)) = r)
  have hmem (u : (J → ℕ) × (J → ℕ)) : e u ∈ left ↔ u ∈ right := by
    simp only [left, right, mem_filter, Fintype.mem_piFinset, mem_product, and_assoc]
    exact degree_pair_fiber p h a r u.1 u.2
  have hmap : right.map e.toEmbedding = left := by
    ext f
    obtain ⟨u, rfl⟩ := e.surjective f
    rw [hmem]
    simp
  have hsum : (∑ f ∈ left, (p.factorial : ℝ) ^ 2 * ∏ j, weight j (f j)) =
      ∑ u ∈ right, monomialWeight w u.1 * monomialWeight w u.2 := by
    rw [← hmap, sum_map]
    refine sum_congr rfl fun u hu => ?_
    have hu' := mem_product.mp (mem_filter.mp hu).1
    rw [weight_factorials w p u.1 (mem_piAntidiag.mp hu'.1).1,
      weight_factorials w p u.2 (mem_piAntidiag.mp hu'.2).1]
    have hw : (∏ j, weight j (e.toEmbedding u j)) =
        (∏ j, w j ^ u.1 j / ((u.1 j).factorial : ℝ)) *
          ∏ j, w j ^ u.2 j / ((u.2 j).factorial : ℝ) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun j _ => ?_
      change w j ^ (u.1 j + u.2 j) / (((u.1 j).factorial : ℝ) * ((u.2 j).factorial : ℝ)) = _
      rw [pow_add, div_mul_div_comm]
    rw [hw, sq, mul_mul_mul_comm]
  rw [show _ = _ from coefficient_fiber S index weight ((p, p, h), r), mul_sum]
  convert hsum using 2
  ext f
  simp [left]

open Classical in
private theorem dft_coefficient_fiber {J M : Type*} [Fintype J] [AddCommMonoid M]
    [DecidableEq M] {q : ℕ} [NeZero q] (S : J → Finset (ℕ × ℕ))
    (degree : J → ℕ × ℕ → M) (gap : J → ℕ × ℕ → ZMod q)
    (weight : J → ℕ × ℕ → ℝ) (target : M) (k : ZMod q) :
    let P : AddMonoidAlgebra ℝ (M × ZMod q) :=
      ∏ j, ∑ v ∈ S j, AddMonoidAlgebra.single (degree j v, gap j v) (weight j v)
    let Q : AddMonoidAlgebra ℂ M :=
      ∏ j, ∑ v ∈ S j, AddMonoidAlgebra.single (degree j v)
        ((weight j v : ℂ) * ZMod.stdAddChar (-(k * gap j v)))
    ZMod.dft (fun r => (P.coeff (target, r) : ℂ)) k = Q.coeff target := by
  intro P Q
  classical
  let T := Fintype.piFinset S
  let index (j : J) (v : ℕ × ℕ) := (degree j v, gap j v)
  let phase (j : J) (v : ℕ × ℕ) := ZMod.stdAddChar (-(k * gap j v))
  have hP (r : ZMod q) : P.coeff (target, r) =
      ∑ f ∈ T, if (∑ j, index j (f j)) = (target, r) then ∏ j, weight j (f j) else 0 := by
    rw [← sum_filter]
    exact coefficient_fiber S index weight _
  have hQ : Q.coeff target =
      ∑ f ∈ T, if (∑ j, degree j (f j)) = target
        then ∏ j, (weight j (f j) : ℂ) * phase j (f j) else 0 := by
    rw [← sum_filter]
    exact coefficient_fiber S degree (fun j v => (weight j v : ℂ) * phase j v) _
  rw [ZMod.dft_apply, hQ]
  simp only [hP, Complex.ofReal_sum, smul_eq_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  simp only [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, index, apply_ite Complex.ofReal,
    Complex.ofReal_zero, mul_ite, mul_zero]
  by_cases hd : (∑ j, degree j (f j)) = target
  · let u := ∑ j, gap j (f j)
    have hchar : (∏ j, phase j (f j)) = ZMod.stdAddChar (-(k * u)) := by
      rw [show -(k * u) = ∑ j, -(k * gap j (f j)) by simp [u, mul_sum, sum_neg_distrib]]
      generalize (univ : Finset J) = V
      induction V using Finset.induction_on with
      | empty => simp
      | insert j V hj ih =>
        rw [sum_insert hj, prod_insert hj, AddChar.map_add_eq_mul, ih]
    simp [hd, prod_mul_distrib, hchar, u, mul_comm]
  · simp [hd]

open Classical in
/-- The cyclic band mass by common occupation degree is a mixed coefficient
of the local character products. -/
theorem common_residual_band {J : Type*} [Fintype J] [DecidableEq J]
    {q : ℕ} [NeZero q] (p h : ℕ) (a : J → ZMod q) (w : J → ℝ) (R : Finset (ZMod q)) :
    let scale := fun n : ℕ => (n.factorial : ℂ) ^ 2
    let S := fun _ : J => range (p + 1) ×ˢ range (p + 1)
    let degree := fun (_ : J) (v : ℕ × ℕ) => (v.1, v.2, min v.1 v.2)
    let gap := fun (j : J) (v : ℕ × ℕ) => (v.1 : ℤ) • a j - (v.2 : ℤ) • a j
    let weight := fun (j : J) (v : ℕ × ℕ) =>
      w j ^ (v.1 + v.2) / ((v.1.factorial : ℝ) * (v.2.factorial : ℝ))
    let Q (k : ZMod q) : AddMonoidAlgebra ℂ (ℕ × ℕ × ℕ) :=
      ∏ j, ∑ v ∈ S j, AddMonoidAlgebra.single (degree j v)
        ((weight j v : ℂ) * ZMod.stdAddChar (-(k * gap j v)))
    (q : ℂ) * (∑ r ∈ R, (↑(∑ u ∈ (piAntidiag univ p ×ˢ piAntidiag univ p).filter
      (fun u : (J → ℕ) × (J → ℕ) => (∑ j, min (u.1 j) (u.2 j)) = h ∧
        (∑ j, ((u.1 j : ℤ) • a j - (u.2 j : ℤ) • a j)) = r),
      monomialWeight w u.1 * monomialWeight w u.2) : ℂ)) =
      scale p * ∑ k : ZMod q,
        (Q k).coeff (p, p, h) * ∑ r ∈ R, ZMod.stdAddChar (k * r) := by
  intro scale S degree gap weight Q
  classical
  let P : AddMonoidAlgebra ℝ ((ℕ × ℕ × ℕ) × ZMod q) :=
    ∏ j, ∑ v ∈ S j, AddMonoidAlgebra.single (degree j v, gap j v) (weight j v)
  let F : ZMod q → ℂ := fun r => (P.coeff ((p, p, h), r) : ℂ)
  have hQ (k : ZMod q) : ZMod.dft F k = (Q k).coeff (p, p, h) :=
    dft_coefficient_fiber S degree gap weight (p, p, h) k
  have hcast (r : ZMod q) :
      ((p.factorial : ℂ) ^ 2) * F r =
        (↑(∑ u ∈ (piAntidiag univ p ×ˢ piAntidiag univ p).filter
          (fun u : (J → ℕ) × (J → ℕ) => (∑ j, min (u.1 j) (u.2 j)) = h ∧
            (∑ j, ((u.1 j : ℤ) • a j - (u.2 j : ℤ) • a j)) = r),
          monomialWeight w u.1 * monomialWeight w u.2) : ℂ) := by
    dsimp only [F]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    convert common_residual_coefficient p h a w r using 2
    ext u
    simp
  simp_rw [← hcast]
  rw [← mul_sum, mul_left_comm (q : ℂ), band_via_dft]
  simp_rw [hQ]
  rfl

end D5.S3.Fourier.Concentration.CommonResidualOccupationCoefficient
