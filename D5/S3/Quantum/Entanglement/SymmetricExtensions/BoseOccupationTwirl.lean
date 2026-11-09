/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Diagonal tensor actions and occupation twirling of Bose extensions. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Diagonal tensor conjugation acts on the original computational basis.
The diagonal twirl is due to Gulati--Nechita--Park, Corollary 8.18,
and Gulati--Nechita--Pellegrini, Lemma 5.8. -/

open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

/-- The diagonal entry of the genuine repeated local tensor operator. -/
def tensorPhase (u : L → ℂ) (x : I → L) : ℂ := ∏ i, u (x i)

/-- Conjugation by the diagonal tensor operator in the computational basis. -/
def diagonalAction (u : L → ℂ) (E : Matrix (I → L) (I → L) ℂ) :
    Matrix (I → L) (I → L) ℂ :=
  diagonal (tensorPhase u) * E * (diagonal (tensorPhase u))ᴴ

private lemma diagonalAction_apply (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (x y : I → L) :
    diagonalAction u E x y = tensorPhase u x * E x y * star (tensorPhase u y) := by
  simp [diagonalAction, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal]

/-- Positivity is preserved by the actual tensor conjugation. -/
theorem diagonalAction_posSemidef (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef) :
    (diagonalAction u E).PosSemidef :=
  hE.mul_mul_conjTranspose_same _

/-- The local diagonal at a transposed site is complex conjugated. -/
def cutPhase (S : Finset I) (u : L → ℂ) (x : I → L) : ℂ :=
  ∏ i, if i ∈ S then star (u (x i)) else u (x i)

private lemma transposed_phase (S : Finset I) (u : L → ℂ) (x y : I → L) :
    tensorPhase u (S.piecewise y x) * star (tensorPhase u (S.piecewise x y)) =
      cutPhase S u x * star (cutPhase S u y) := by
  simp only [tensorPhase, cutPhase, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : i ∈ S <;> simp [Finset.piecewise, h, mul_comm]

/-- Every partial transpose of a summand is a conjugation of the same cut of E.
The formula includes the empty and full cuts. -/
theorem partialTranspose_diagonalAction (S : Finset I) (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn S (diagonalAction u E) =
      diagonal (cutPhase S u) * partialTransposeOn S E *
        (diagonal (cutPhase S u))ᴴ := by
  ext x y
  simp only [partialTransposeOn, diagonalAction_apply, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply]
  calc
    _ = (tensorPhase u (S.piecewise y x) *
        star (tensorPhase u (S.piecewise x y))) *
          E (S.piecewise y x) (S.piecewise x y) := by ring
    _ = _ := by rw [transposed_phase]; ring

private lemma phase_unit (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1) (x : I → L) :
    tensorPhase u x * star (tensorPhase u x) = 1 := by
  have hn : ‖tensorPhase u x‖ = 1 := by simp [tensorPhase, norm_prod, hu]
  simpa only [Complex.star_def, hn, one_pow, Complex.ofReal_one] using
    Complex.mul_conj' (tensorPhase u x)

private lemma split_phase_product (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1)
    (a b : I) (hab : a ≠ b) (v w : L × L)
    (c : {i : I // i ≠ a ∧ i ≠ b} → L) :
    tensorPhase u ((edgeSplit a b hab).symm (v,c)) *
      star (tensorPhase u ((edgeSplit a b hab).symm (w,c))) =
        (u v.1 * u v.2) * star (u w.1 * u w.2) := by
  simp only [tensorPhase, star_prod, ← Finset.prod_mul_distrib]
  have h (i : I) :
      u ((edgeSplit a b hab).symm (v,c) i) *
        star (u ((edgeSplit a b hab).symm (w,c) i)) =
      (if i = a then u v.1 * star (u w.1) else 1) *
        (if i = b then u v.2 * star (u w.2) else 1) := by
    by_cases ha : i = a
    · subst i
      simp [edgeSplit, hab]
    by_cases hb : i = b
    · subst i
      simp [edgeSplit, hab.symm]
    · have hm : u (c ⟨i,ha,hb⟩) * star (u (c ⟨i,ha,hb⟩)) = 1 := by
        simpa only [Complex.star_def, hu, one_pow, Complex.ofReal_one] using
          Complex.mul_conj' (u (c ⟨i,ha,hb⟩))
      simpa [edgeSplit, ha, hb] using hm
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, star_mul]
  ring

/-- Every ordered two-register marginal transforms by the corresponding local diagonal.
All complement phases cancel, so the unnormalized partial trace has no dimension factor. -/
theorem edgeMarginal_diagonalAction (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1)
    (E : Matrix (I → L) (I → L) ℂ) (a b : I) (hab : a ≠ b) :
    edgeMarginal a b hab (diagonalAction u E) =
      diagonal (fun v : L × L => u v.1 * u v.2) * edgeMarginal a b hab E *
        (diagonal (fun v : L × L => u v.1 * u v.2))ᴴ := by
  ext v w
  simp only [edgeMarginal,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.submatrix_apply, diagonalAction_apply, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    _ = (tensorPhase u ((edgeSplit a b hab).symm (v,c)) *
          star (tensorPhase u ((edgeSplit a b hab).symm (w,c)))) *
            E ((edgeSplit a b hab).symm (v,c)) ((edgeSplit a b hab).symm (w,c)) := by ring
    _ = _ := by rw [split_phase_product u hu]; ring


open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open private support_of_columns dicke_pair_supported from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

private lemma tensorPhase_perm (u : L → ℂ) (x : I → L) (σ : Equiv.Perm I) :
    tensorPhase u (x ∘ σ) = tensorPhase u x := by
  exact Equiv.prod_comp σ (fun i => u (x i))

/-- Diagonal tensor conjugation preserves genuine Bose support, rather than merely
permutation conjugation invariance. -/
theorem diagonalAction_bose (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hs : P I L * E * P I L = E) :
    P I L * diagonalAction u E * P I L = diagonalAction u E := by
  have hl : P I L * E = E := by
    calc
      P I L * E = P I L * (P I L * E * P I L) :=
        congrArg (fun M => P I L * M) hs.symm
      _ = (P I L * P I L) * E * P I L := by simp only [Matrix.mul_assoc]
      _ = E := by rw [P_idempotent, hs]
  have hc : ∀ y, IsSymmetricVector (fun x => E x y) := by
    intro y
    have h := P_mulVec_symmetric (fun x => E x y)
    have he : P I L *ᵥ (fun x => E x y) = (fun x => E x y) := by
      funext x
      exact congrArg (fun M => M x y) hl
    rwa [he] at h
  apply support_of_columns _ (diagonalAction_posSemidef u E hE).isHermitian
  intro y σ x
  simp only [diagonalAction_apply, tensorPhase_perm, hc y σ x]

/-- A finite average of actual repeated local diagonal conjugations.
The averaging type is required to be nonempty; no trace normalization is imposed. -/
def diagonalAverage {T : Type*} [Fintype T] (u : T → L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) : Matrix (I → L) (I → L) ℂ :=
  (Fintype.card T : ℝ)⁻¹ • ∑ t, diagonalAction (u t) E

open D5.S3.Quantum.Entanglement.OccupancyWordSectors

section Occupation

variable {r : ℕ}

/-- Local phases sampled independently from the `(r+1)`-st roots of unity.
There is no aliasing between occupation counts of words of length `r`. -/
def occupationPhase (t : L → ZMod (r + 1)) (a : L) : ℂ := ZMod.stdAddChar (t a)

private lemma occupationPhase_norm (t : L → ZMod (r + 1)) (a : L) :
    ‖occupationPhase t a‖ = 1 := by
  simp only [occupationPhase, ZMod.stdAddChar_apply, Circle.norm_coe]

private def wordCharacter (x : Fin r → L) : AddChar (L → ZMod (r + 1)) ℂ where
  toFun t := tensorPhase (occupationPhase t) x
  map_zero_eq_one' := by simp [tensorPhase, occupationPhase]
  map_add_eq_mul' t s := by
    simp [tensorPhase, occupationPhase, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

private lemma phase_occupation (u : L → ℂ) (x : Fin r → L) :
    tensorPhase u x = ((occupation x).map u).prod := by
  simp [tensorPhase, occupation, List.map_ofFn, List.prod_ofFn]

private lemma wordCharacter_single (x : Fin r → L) (a : L) :
    wordCharacter x (fun b => if b = a then 1 else 0) =
      ZMod.stdAddChar ((occupation x).count a : ZMod (r + 1)) := by
  change tensorPhase _ x = _
  rw [phase_occupation, Multiset.prod_map_eq_pow_single a]
  · simp [occupationPhase, ← AddChar.map_nsmul_eq_pow]
  · intro b hba hb
    simp [occupationPhase, hba]

private lemma wordCharacter_eq_iff (x y : Fin r → L) :
    wordCharacter x = wordCharacter y ↔ occupation x = occupation y := by
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro a
    have he := congrArg (fun χ : AddChar (L → ZMod (r + 1)) ℂ =>
      χ (fun b => if b = a then 1 else 0)) h
    rw [wordCharacter_single, wordCharacter_single] at he
    have hz := ZMod.injective_stdAddChar he
    have hx : (occupation x).count a < r + 1 := by
      have := Multiset.count_le_card a (occupation x)
      rw [occupation_card] at this
      omega
    have hy : (occupation y).count a < r + 1 := by
      have := Multiset.count_le_card a (occupation y)
      rw [occupation_card] at this
      omega
    simpa only [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using
      congrArg ZMod.val hz
  · intro h
    ext t
    change tensorPhase _ x = tensorPhase _ y
    rw [phase_occupation, phase_occupation, h]

private lemma character_difference (x y : Fin r → L) (t : L → ZMod (r + 1)) :
    (wordCharacter x - wordCharacter y) t =
      tensorPhase (occupationPhase t) x * star (tensorPhase (occupationPhase t) y) := by
  rw [AddChar.sub_apply', div_eq_mul_inv]
  change _ * (tensorPhase (occupationPhase t) y)⁻¹ = _
  congr 1
  apply inv_eq_of_mul_eq_one_right
  exact phase_unit _ (occupationPhase_norm t) y

/-- Distinct occupation characters cancel exactly in the finite unitary average. -/
theorem occupation_character_orthogonality (x y : Fin r → L) :
    (∑ t : L → ZMod (r + 1), tensorPhase (occupationPhase t) x *
      star (tensorPhase (occupationPhase t) y)) =
      if occupation x = occupation y then (Fintype.card (L → ZMod (r + 1)) : ℂ)
        else 0 := by
  simp_rw [← character_difference]
  rw [AddChar.sum_eq_ite]
  simp only [sub_eq_zero, wordCharacter_eq_iff]

/-- The actual unitary twirl on the original tensor registers. -/
def occupationTwirl (E : Matrix (Fin r → L) (Fin r → L) ℂ) :
    Matrix (Fin r → L) (Fin r → L) ℂ := diagonalAverage (occupationPhase (r := r)) E

/-- The unitary average deletes precisely the entries between different occupations. -/
theorem occupationTwirl_apply (E : Matrix (Fin r → L) (Fin r → L) ℂ)
    (x y : Fin r → L) :
    occupationTwirl E x y = if occupation x = occupation y then E x y else 0 := by
  simp only [occupationTwirl, diagonalAverage, Matrix.smul_apply, Matrix.sum_apply,
    diagonalAction_apply]
  have he : (∑ t : L → ZMod (r + 1),
      tensorPhase (occupationPhase t) x * E x y *
        star (tensorPhase (occupationPhase t) y)) =
      (∑ t : L → ZMod (r + 1), tensorPhase (occupationPhase t) x *
        star (tensorPhase (occupationPhase t) y)) * E x y := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [he, occupation_character_orthogonality]
  split_ifs
  · have hc : (Fintype.card (L → ZMod (r + 1)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    change (((Fintype.card (L → ZMod (r + 1)) : ℝ)⁻¹ : ℝ) : ℂ) *
      ((Fintype.card (L → ZMod (r + 1)) : ℂ) * E x y) = E x y
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]
  · simp only [zero_mul, smul_zero]

#print axioms occupation_character_orthogonality
#print axioms occupationTwirl_apply

end Occupation

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
