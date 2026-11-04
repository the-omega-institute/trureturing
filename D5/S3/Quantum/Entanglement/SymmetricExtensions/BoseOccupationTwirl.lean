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

/-- The same proper-cut PPT inequalities survive each diagonal tensor summand. -/
theorem diagonalAction_fullyPPT (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (hE : FullyPPT E) :
    FullyPPT (diagonalAction u E) := by
  intro S hS hp
  rw [partialTranspose_diagonalAction]
  exact (hE S hS hp).mul_mul_conjTranspose_same _

private lemma phase_unit (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1) (x : I → L) :
    tensorPhase u x * star (tensorPhase u x) = 1 := by
  have hn : ‖tensorPhase u x‖ = 1 := by simp [tensorPhase, norm_prod, hu]
  simpa only [Complex.star_def, hn, one_pow, Complex.ofReal_one] using
    Complex.mul_conj' (tensorPhase u x)

/-- The repeated local diagonal is an actual unitary matrix when its local entries are phases. -/
theorem tensor_diagonal_unitary (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1) :
    diagonal (tensorPhase (I := I) u) ∈ Matrix.unitaryGroup (I → L) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Pi.mul_def, Pi.star_apply, phase_unit u hu,
    Matrix.diagonal_one]

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

/-- Positivity of the average follows from the actual positive conjugated summands. -/
theorem diagonalAverage_posSemidef {T : Type*} [Fintype T]
    (u : T → L → ℂ) (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef) :
    (diagonalAverage u E).PosSemidef := by
  exact (Matrix.posSemidef_sum Finset.univ (fun t _ =>
    diagonalAction_posSemidef (u t) E hE)).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Each original PPT cut is retained by the finite average. -/
theorem diagonalAverage_fullyPPT {T : Type*} [Fintype T]
    (u : T → L → ℂ) (E : Matrix (I → L) (I → L) ℂ) (hE : FullyPPT E) :
    FullyPPT (diagonalAverage u E) := by
  intro S hS hp
  have he : partialTransposeOn S (diagonalAverage u E) =
      (Fintype.card T : ℝ)⁻¹ • ∑ t, partialTransposeOn S (diagonalAction (u t) E) := by
    ext x y
    simp only [diagonalAverage, partialTransposeOn, Matrix.smul_apply, Matrix.sum_apply]
  rw [he]
  exact (Matrix.posSemidef_sum Finset.univ (fun t _ =>
    diagonalAction_fullyPPT (u t) E hE S hS hp)).smul
      (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The average remains supported on the full symmetric subspace. -/
theorem diagonalAverage_bose {T : Type*} [Fintype T]
    (u : T → L → ℂ) (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hs : P I L * E * P I L = E) :
    P I L * diagonalAverage u E * P I L = diagonalAverage u E := by
  simp only [diagonalAverage, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum,
    Matrix.sum_mul, diagonalAction_bose _ E hE hs]

/-- Every prescribed ordered marginal fixed by the local diagonal action is
preserved by the average, with the original unnormalized trace. -/
theorem edgeMarginal_diagonalAverage {T : Type*} [Fintype T] [Nonempty T]
    (u : T → L → ℂ) (hu : ∀ t a, ‖u t a‖ = 1)
    (E : Matrix (I → L) (I → L) ℂ) (a b : I) (hab : a ≠ b)
    (ρ : Matrix (L × L) (L × L) ℂ) (hm : edgeMarginal a b hab E = ρ)
    (hfix : ∀ t, diagonal (fun v : L × L => u t v.1 * u t v.2) * ρ *
      (diagonal (fun v : L × L => u t v.1 * u t v.2))ᴴ = ρ) :
    edgeMarginal a b hab (diagonalAverage u E) = ρ := by
  have hlin : edgeMarginal a b hab (diagonalAverage u E) =
      (Fintype.card T : ℝ)⁻¹ • ∑ t, edgeMarginal a b hab (diagonalAction (u t) E) := by
    ext x y
    simp only [diagonalAverage, edgeMarginal,
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
      Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply,
      Finset.smul_sum]
    rw [Finset.sum_comm]
  rw [hlin]
  simp_rw [edgeMarginal_diagonalAction _ (hu _) E a b hab, hm, hfix]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

#print axioms diagonalAction_bose
#print axioms diagonalAverage_posSemidef
#print axioms diagonalAverage_fullyPPT
#print axioms diagonalAverage_bose
#print axioms edgeMarginal_diagonalAverage

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

/-- The occupation matrix of the averaged operator has no off-diagonal entries.
These are the repository's normalized uniform Dicke occupation vectors. -/
theorem occupationTwirl_occupation_offdiag
    (E : Matrix (Fin r → L) (Fin r → L) ℂ) (a b : Sym L r) (hab : a ≠ b) :
    star (sectorVector r a.val) ⬝ᵥ (occupationTwirl E *ᵥ sectorVector r b.val) = 0 := by
  have hval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hxa : occupation x = a.val
  · by_cases hyb : occupation y = b.val
    · have hxy : occupation x ≠ occupation y := fun h =>
        hval (hxa.symm.trans (h.trans hyb))
      simp [occupationTwirl_apply, hxy]
    · have hz : sectorVector r b.val y = 0 := by
        unfold sectorVector
        apply if_neg
        exact fun h => hyb (Finset.mem_filter.mp h).2
      simp only [hz, mul_zero]
  · have hz : sectorVector r a.val x = 0 := by
      unfold sectorVector
      apply if_neg
      exact fun h => hxa (Finset.mem_filter.mp h).2
    simp only [Pi.star_apply, hz, star_zero, zero_mul]

private lemma dickeVector_phase {n : ℕ} (u : Fin n → ℂ) (i j : Fin n)
    (x : Fin n × Fin n) :
    (u x.1 * u x.2) * dickeVector i j x = (u i * u j) * dickeVector i j x := by
  by_cases hij : i = j
  · subst j
    by_cases hx : x = (i,i)
    · subst x
      rfl
    · simp [dickeVector, hx]
  · by_cases hx : x = (i,j)
    · subst x
      rfl
    by_cases hy : x = (j,i)
    · subst x
      simp only [Prod.fst, Prod.snd, mul_comm (u j) (u i)]
    · simp [dickeVector, hij, hx, hy]

private lemma dicke_diagonal_fixed {n : ℕ} (u : Fin n → ℂ)
    (hu : ∀ a, ‖u a‖ = 1) (Y : Fin n → Fin n → ℝ) :
    diagonal (fun v : Fin n × Fin n => u v.1 * u v.2) * dickeOperator Y *
      (diagonal (fun v : Fin n × Fin n => u v.1 * u v.2))ᴴ = dickeOperator Y := by
  let D := diagonal (fun v : Fin n × Fin n => u v.1 * u v.2)
  have ht (i j : Fin n) :
      D * Matrix.vecMulVec (dickeVector i j) (star (dickeVector i j)) * Dᴴ =
        Matrix.vecMulVec (dickeVector i j) (star (dickeVector i j)) := by
    have hm : (u i * u j) * star (u i * u j) = 1 := by
      have hn : ‖u i * u j‖ = 1 := by simp [norm_mul, hu]
      simpa only [Complex.star_def, hn, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (u i * u j)
    ext x y
    simp only [D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.vecMulVec_apply, Pi.star_apply]
    calc
      _ = ((u x.1 * u x.2) * dickeVector i j x) *
          star ((u y.1 * u y.2) * dickeVector i j y) := by simp only [star_mul]; ring
      _ = ((u i * u j) * dickeVector i j x) *
          star ((u i * u j) * dickeVector i j y) := by
        rw [dickeVector_phase, dickeVector_phase]
      _ = _ := by
        rw [star_mul]
        calc
          _ = ((u i * u j) * star (u i * u j)) *
              (dickeVector i j x * star (dickeVector i j y)) := by ring
          _ = _ := by rw [hm, one_mul]
  change D * dickeOperator Y * Dᴴ = _
  simp only [dickeOperator, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i ≤ j <;> simp [hij, Matrix.mul_smul, Matrix.smul_mul, ht]

/-- A genuine no-PPT Dicke star witness has an occupation-diagonal complete
Bose witness obtained by the explicit average, with every ordered marginal retained. -/
theorem twirl_star_core {n : ℕ} (root : Fin r) (Y : Fin n → Fin n → ℝ)
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ)
    (hE : StarExtensionCore root (dickeOperator Y) E) :
    CompleteExtensionCore (dickeOperator Y) (occupationTwirl E) ∧
      ∀ a b : Sym (Fin n) r, a ≠ b →
        star (sectorVector r a.val) ⬝ᵥ (occupationTwirl E *ᵥ sectorVector r b.val) = 0 := by
  obtain ⟨hpos, hsym, hm⟩ :=
    (same_matrix_core root _ (dicke_pair_supported Y) E).mp hE
  refine ⟨⟨diagonalAverage_posSemidef _ E hpos,
    diagonalAverage_bose _ E hpos hsym, ?_⟩, occupationTwirl_occupation_offdiag E⟩
  intro a b hab
  exact edgeMarginal_diagonalAverage _ occupationPhase_norm E a b hab _ (hm a b hab)
    (fun t => dicke_diagonal_fixed _ (occupationPhase_norm t) Y)

/-- The same explicit Dicke twirl retains all original PPT cuts. -/
theorem twirl_star {n : ℕ} (root : Fin r) (Y : Fin n → Fin n → ℝ)
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ)
    (hE : StarExtension root (dickeOperator Y) E) :
    CompleteExtension (dickeOperator Y) (occupationTwirl E) ∧
      ∀ a b : Sym (Fin n) r, a ≠ b →
        star (sectorVector r a.val) ⬝ᵥ (occupationTwirl E *ᵥ sectorVector r b.val) = 0 := by
  have hc := twirl_star_core root Y E ⟨hE.1,hE.2.1,hE.2.2.1⟩
  exact ⟨⟨hc.1.1,hc.1.2.1,hc.1.2.2,diagonalAverage_fullyPPT _ E hE.2.2.2⟩,hc.2⟩

#print axioms twirl_star_core
#print axioms twirl_star

end Occupation

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
