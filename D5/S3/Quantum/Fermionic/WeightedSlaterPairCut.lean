/- GID: D5/S3/Quantum/Fermionic/WeightedSlaterPairCut
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/WeightedSlaterPairCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted occupation amplitudes for disjoint pairs across an ordered Slater cut. -/

import D5.S3.Quantum.Fermionic.SlaterPairCutRank
import Mathlib.Analysis.Complex.Order

/-! Distinct endpoint choices preserve the binary interaction across the cut. -/

open scoped BigOperators ComplexOrder Matrix

namespace D5.S3.Quantum.Fermionic.WeightedSlaterPairCut

open OrderedSlaterCut SlaterPairCutRank

variable {ι : Type*} [LinearOrder ι]

private theorem amplitude_on_selected_pairs {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hp : ∀ i, (p (i, false) : ι) < p (i, true))
    (hq : ∀ j, (q (j, false) : ι) < q (j, true))
    (weight : Fin (m + n) → Bool → ℂ) :
    let A := alternationMatrix (fun i e => (p (i, e) : ι)) (fun j e => (q (j, e) : ι))
    ∃ left : (Fin m → ZMod 2) → ZMod 2, ∃ right : (Fin n → ZMod 2) → ZMod 2,
      ∀ (x : Fin m → ZMod 2) (y : Fin n → ZMod 2),
        orderedCut I (cutPairOrbitals p q weight) (pairBitOccupation p x)
          (pairBitOccupation q y) =
          (binarySign (left x) * ∏ i, weight (Fin.castAdd n i) (pickEndpoint (x i))) *
            binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y) *
            (binarySign (right y) * ∏ j, weight (Fin.natAdd m j) (pickEndpoint (y j))) := by
  intro A
  obtain ⟨left, right, hphase⟩ := orderedCut_pairs_character p q (1 : ℂ) hp hq
  refine ⟨left, right, fun x y => ?_⟩
  have hs := hphase x y
  rw [orderedCut_pairs_selected] at hs
  simp only [Finset.prod_const, one_pow, mul_one, one_mul] at hs
  have hw := orderedCut_pairs_selected p q weight
    (fun i => pickEndpoint (x i)) (fun j => pickEndpoint (y j))
  change orderedCut I (cutPairOrbitals p q weight) (pairBitOccupation p x)
    (pairBitOccupation q y) = _ at hw
  rw [hw, hs, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  dsimp [A]
  ring

private noncomputable def fiberColumns {X U : Type*} [DecidableEq U] (f : X → U)
    (amplitude : X → ℂ) (scale : U → ℂ) : Matrix X U ℂ :=
  fun x u => if f x = u then amplitude x / scale u else 0

omit [LinearOrder ι] in
private theorem fiberColumns_isometry {X U : Type*} [Fintype X] [DecidableEq U]
    (f : X → U) (amplitude : X → ℂ) (scale : U → ℂ)
    (hne : ∀ u, scale u ≠ 0)
    (hmass : ∀ u,
      (∑ x : X, if f x = u then star (amplitude x) * amplitude x else 0) =
        star (scale u) * scale u) :
    (fiberColumns f amplitude scale)ᴴ * fiberColumns f amplitude scale = 1 := by
  ext u v
  by_cases huv : u = v
  · subst v
    rw [Matrix.mul_apply, Matrix.one_apply_eq]
    calc
      _ = (∑ x : X, if f x = u then star (amplitude x) * amplitude x else 0) /
          (star (scale u) * scale u) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : f x = u
        · simp [Matrix.conjTranspose_apply, fiberColumns, hx, div_mul_div_comm]
        · simp [Matrix.conjTranspose_apply, fiberColumns, hx]
      _ = 1 := by
        rw [hmass, div_self]
        exact mul_ne_zero (star_ne_zero.mpr (hne u)) (hne u)
  · rw [Matrix.mul_apply, Matrix.one_apply_ne huv]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : f x = u
    · simp [Matrix.conjTranspose_apply, fiberColumns, hx, huv]
    · simp [Matrix.conjTranspose_apply, fiberColumns, hx]

private theorem factor_through_fibers {X Y U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (f : X → U) (g : Y → V)
    (a : X → ℂ) (b : Y → ℂ) (s : U → ℂ) (t : V → ℂ) (H : Matrix U V ℂ)
    (hs : ∀ u, s u ≠ 0) (ht : ∀ v, t v ≠ 0) :
    fiberColumns f a s * Matrix.of (fun u v => s u * H u v * star (t v)) *
        (fiberColumns g b t)ᴴ =
      Matrix.of (fun x y => a x * H (f x) (g y) * star (b y)) := by
  have hleft (x : X) (v : V) :
      (fiberColumns f a s * Matrix.of (fun u v => s u * H u v * star (t v))) x v =
        a x * H (f x) v * star (t v) := by
    rw [Matrix.mul_apply]
    simp only [fiberColumns, Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    simp only [← mul_assoc, div_mul_cancel₀ _ (hs _)]
  ext x y
  rw [Matrix.mul_apply]
  have hstar (v : V) :
      ((fiberColumns g b t)ᴴ) v y =
        if g y = v then star (b y) / star (t v) else 0 := by
    by_cases h : g y = v <;> simp [Matrix.conjTranspose_apply, fiberColumns, h]
  simp only [hleft, hstar, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ (star_ne_zero.mpr (ht _))]
  rfl

private abbrev LeftImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :=
  LinearMap.range Aᵀ.mulVecLin

private abbrev RightImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :=
  LinearMap.range A.mulVecLin

private def leftImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin m → ZMod 2) : LeftImage A :=
  ⟨Aᵀ *ᵥ x, ⟨x, rfl⟩⟩

private def rightImage {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) : RightImage A :=
  ⟨A *ᵥ y, ⟨y, rfl⟩⟩

private noncomputable def imageCharacter {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Matrix (LeftImage A) (RightImage A) ℂ :=
  fun u v => binarySign (u.val ⬝ᵥ Classical.choose v.property)

private theorem imageCharacter_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin m → ZMod 2) (y : Fin n → ZMod 2) :
    imageCharacter A (leftImage A x) (rightImage A y) = binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y) := by
  let v := rightImage A y
  have hrep : A *ᵥ Classical.choose v.property = A *ᵥ y := Classical.choose_spec v.property
  change binarySign ((Aᵀ *ᵥ x) ⬝ᵥ Classical.choose v.property) = _
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, hrep]

private noncomputable def imageRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (u : LeftImage A) : AddChar (RightImage A) ℂ :=
  binarySign.compAddMonoidHom {
    toFun := fun v => Classical.choose u.property ⬝ᵥ v.val
    map_zero' := dotProduct_zero _
    map_add' := fun _ _ => dotProduct_add _ _ _ }

private theorem imageCharacter_eq_row {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (u : LeftImage A) (v : RightImage A) : imageCharacter A u v = imageRow A u v := by
  let x := Classical.choose u.property
  let y := Classical.choose v.property
  have hx : Aᵀ *ᵥ x = u.val := Classical.choose_spec u.property
  have hy : A *ᵥ y = v.val := Classical.choose_spec v.property
  change binarySign (u.val ⬝ᵥ y) = binarySign (x ⬝ᵥ v.val)
  rw [← hx, ← hy, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

private theorem imageCharacter_eq_of_column {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (u : LeftImage A) (y : Fin n → ZMod 2) :
    imageCharacter A u (rightImage A y) = binarySign (u.val ⬝ᵥ y) := by
  obtain ⟨x, hx⟩ := u.property
  have hu : leftImage A x = u := Subtype.ext hx
  rw [← hu, imageCharacter_apply]
  rfl

open Classical in
private theorem imageCharacter_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    imageCharacter A * (imageCharacter A)ᴴ =
      (Fintype.card (RightImage A) : ℂ) • (1 : Matrix (LeftImage A) (LeftImage A) ℂ) := by
  ext u v
  rw [Matrix.mul_apply, Matrix.smul_apply]
  by_cases h : u = v
  · subst v
    simp [imageCharacter, Matrix.conjTranspose_apply, binarySign_star, binarySign_sq]
  · rw [Matrix.one_apply_ne h, smul_zero]
    let χ := imageRow A u + imageRow A v
    have hterm (w : RightImage A) :
        imageCharacter A u w * star (imageCharacter A v w) = χ w := by
      rw [show star (imageCharacter A v w) = imageCharacter A v w from binarySign_star _,
        imageCharacter_eq_row, imageCharacter_eq_row]
      rfl
    simp only [Matrix.conjTranspose_apply, hterm]
    apply AddChar.sum_eq_zero_iff_ne_zero.mpr
    apply AddChar.ne_zero_iff.mpr
    have hn : ∃ j, u.val j ≠ v.val j := by
      by_contra! he
      exact h (Subtype.ext (funext he))
    obtain ⟨j, hj⟩ := hn
    use rightImage A (Pi.single j 1)
    rw [← hterm, imageCharacter_eq_of_column, imageCharacter_eq_of_column,
      dotProduct_single_one, dotProduct_single_one, binarySign_star, ← AddChar.map_add_eq_mul]
    have hsum : u.val j + v.val j = 1 := by
      rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (u.val j) with hu | hu <;>
        rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (v.val j) with hv | hv <;>
        simp_all
    rw [hsum]
    have hone : (1 : ZMod 2).val = 1 := rfl
    norm_num [binarySign, AddChar.zmodChar_apply, hone]

open Classical in
private theorem weighted_image_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (s : LeftImage A → ℂ) (t : RightImage A → ℂ)
    (hs : ∀ u, s u ≠ 0) (ht : ∀ v, t v ≠ 0) :
    (Matrix.of fun u v => s u * imageCharacter A u v * star (t v)).rank = 2 ^ A.rank := by
  have hfactor : (Matrix.of fun u v => s u * imageCharacter A u v * star (t v)) =
      Matrix.diagonal s * imageCharacter A * Matrix.diagonal (fun v => star (t v)) := by
    ext u v
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hds : (Matrix.diagonal s).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun u _ => hs u)
  have hdt : (Matrix.diagonal (fun v => star (t v))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => star_ne_zero.mpr (ht v))
  have hcard : (Fintype.card (RightImage A) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hrank : (imageCharacter A).rank = Fintype.card (LeftImage A) := by
    refine le_antisymm (Matrix.rank_le_card_height _) ?_
    calc
      Fintype.card (LeftImage A) = (imageCharacter A * (imageCharacter A)ᴴ).rank := by
        rw [imageCharacter_gram,
          Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hcard),
          Matrix.rank_one]
      _ ≤ (imageCharacter A).rank := Matrix.rank_mul_le_left _ _
  rw [hfactor, Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdt,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hds, hrank,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [← Matrix.rank, Matrix.rank_transpose]

private theorem rank_isometric_factor {X Y U V : Type*}
    [Fintype X] [Fintype Y] [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (E : Matrix X U ℂ) (F : Matrix Y V ℂ) (K : Matrix U V ℂ)
    (hE : Eᴴ * E = 1) (hF : Fᴴ * F = 1) :
    (E * K * Fᴴ).rank = K.rank := by
  have hback : Eᴴ * (E * K * Fᴴ) * F = K := by
    simp only [← Matrix.mul_assoc, hE, Matrix.one_mul]
    rw [Matrix.mul_assoc, hF, Matrix.mul_one]
  refine le_antisymm ((Matrix.rank_mul_le_left _ _).trans
    (Matrix.rank_mul_le_right _ _)) ?_
  calc
    K.rank = (Eᴴ * (E * K * Fᴴ) * F).rank := congrArg Matrix.rank hback.symm
    _ ≤ (Eᴴ * (E * K * Fᴴ)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (E * K * Fᴴ).rank := Matrix.rank_mul_le_right _ _

private theorem nonzero_fiber_scales {X U : Type*} [Fintype X] [DecidableEq U]
    (f : X → U) (a : X → ℂ) (hf : Function.Surjective f) (ha : ∀ x, a x ≠ 0) :
    ∃ s : U → ℂ, (∀ u, s u ≠ 0) ∧ ∀ u,
      (∑ x : X, if f x = u then star (a x) * a x else 0) = star (s u) * s u := by
  let mass (u : U) : ℝ := ∑ x : X, if f x = u then Complex.normSq (a x) else 0
  have hpos (u : U) : 0 < mass u := by
    obtain ⟨x, hx⟩ := hf u
    refine Finset.sum_pos' (fun y _ => ?_) ⟨x, Finset.mem_univ x, ?_⟩
    · exact ite_nonneg (Complex.normSq_nonneg _) le_rfl
    · simpa [hx] using (Complex.normSq_pos.mpr (ha x))
  refine ⟨fun u => (Real.sqrt (mass u) : ℂ), fun u =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hpos u)).ne', ?_⟩
  intro u
  have hcast : (mass u : ℂ) = ∑ x : X, if f x = u then star (a x) * a x else 0 := by
    simp only [mass, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero,
      Complex.normSq_eq_conj_mul_self, Complex.star_def]
  rw [← hcast]
  simpa [Complex.star_def] using
    congrArg (fun r : ℝ => (r : ℂ)) (Real.mul_self_sqrt (hpos u).le).symm

open Classical in
private theorem weighted_selected_kernel_rank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (a : (Fin m → ZMod 2) → ℂ) (b : (Fin n → ZMod 2) → ℂ)
    (ha : ∀ x, a x ≠ 0) (hb : ∀ y, b y ≠ 0) :
    (Matrix.of fun x y => a x * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y) * star (b y)).rank =
      2 ^ A.rank := by
  have hl : Function.Surjective (leftImage A) := by
    rintro ⟨u, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hr : Function.Surjective (rightImage A) := by
    rintro ⟨v, y, hy⟩
    exact ⟨y, Subtype.ext hy⟩
  obtain ⟨s, hs, hsMass⟩ := nonzero_fiber_scales (leftImage A) a hl ha
  obtain ⟨t, ht, htMass⟩ := nonzero_fiber_scales (rightImage A) b hr hb
  have hf := factor_through_fibers (leftImage A) (rightImage A) a b s t
    (imageCharacter A) hs ht
  simp only [imageCharacter_apply] at hf
  rw [← hf, rank_isometric_factor _ _ _
    (fiberColumns_isometry (leftImage A) a s hs hsMass)
    (fiberColumns_isometry (rightImage A) b t ht htMass), weighted_image_rank A s t hs ht]

open Classical in
/-- When every endpoint amplitude is nonzero, the full ordinary marginal
has rank two to the binary rank of the pair alternation matrix. -/
theorem orderedMarginal_rank_of_nonzero [Fintype ι] {m n : ℕ} {I : Set ι}
    (p : (Fin m × Bool) ↪ I) (q : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hp : ∀ i, (p (i, false) : ι) < p (i, true))
    (hq : ∀ j, (q (j, false) : ι) < q (j, true))
    (weight : Fin (m + n) → Bool → ℂ) (hw : ∀ i b, weight i b ≠ 0) :
    let A := alternationMatrix (fun i e => (p (i, e) : ι)) (fun j e => (q (j, e) : ι))
    let B := orderedCut I (cutPairOrbitals p q weight)
    (B * Bᴴ).rank = 2 ^ A.rank := by
  intro A B
  rw [Matrix.rank_self_mul_conjTranspose]
  dsimp only [B]
  obtain ⟨left, right, hphase⟩ := amplitude_on_selected_pairs p q hp hq weight
  let a : (Fin m → ZMod 2) → ℂ :=
    fun x => binarySign (left x) * ∏ i, weight (Fin.castAdd n i) (pickEndpoint (x i))
  let b : (Fin n → ZMod 2) → ℂ :=
    fun y => star (binarySign (right y) * ∏ j, weight (Fin.natAdd m j) (pickEndpoint (y j)))
  have hsign (z : ZMod 2) : binarySign z ≠ 0 := by
    intro hz
    have h := binarySign_sq z
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have ha (x) : a x ≠ 0 :=
    mul_ne_zero (hsign _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hw _ _))
  have hb (y) : b y ≠ 0 :=
    star_ne_zero.mpr (mul_ne_zero (hsign _) (Finset.prod_ne_zero_iff.mpr (fun j _ => hw _ _)))
  let M := Matrix.of fun x y => a x * binarySign ((Aᵀ *ᵥ x) ⬝ᵥ y) * star (b y)
  have hpad := eq_padding (pairBitOccupation p) (pairBitOccupation q)
    (orderedCut I (cutPairOrbitals p q weight)) M
    (fun x y => by simpa only [M, Matrix.of_apply, a, b, star_star] using hphase x y)
    (fun u v h => orderedCut_pairs_zero p q weight u v
      (Or.inl (not_pairOccupation_of_not_bit p h)))
    (fun u v h => orderedCut_pairs_zero p q weight u v
      (Or.inr (not_pairOccupation_of_not_bit q h)))
  rw [hpad, rank_isometric_factor _ _ _ (embed_adjoint_mul _) (embed_adjoint_mul _)]
  exact weighted_selected_kernel_rank A a b ha hb

end D5.S3.Quantum.Fermionic.WeightedSlaterPairCut
