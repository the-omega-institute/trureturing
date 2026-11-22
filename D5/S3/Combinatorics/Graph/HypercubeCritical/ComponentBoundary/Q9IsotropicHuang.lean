/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A supported weighted Huang eigenvector gives a prime-field word on one cube parity. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicSupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-! An integer presentation of the actual signed coordinate actions gives
a modular necessary condition for supports in Hong–Wu–Xia Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip flip_adj gamma gamma_apply)
open private huangMatrix cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_zero matrix_flip_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private intCoeff intCoeff_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap

abbrev parity : Q 9 → Bool := cubeParity

/-- The signed coefficient of a coordinate flip. A false prefix bit contributes `-1`. -/
def flipSign : {n : ℕ} → Fin n → Q n → ℤ
  | 0, i, _ => Fin.elim0 i
  | _n + 1, i, x => Fin.cases 1
      (fun j => (if x 0 then 1 else -1) * flipSign j (Sensitivity.π x)) i

private theorem flipSign_cast {n : ℕ} (i : Fin n) (x : Q n) :
    (flipSign i x : ℝ) = huangMatrix n x (flip x i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          rw [matrix_flip_zero]
          change ((1 : ℤ) : ℝ) = 1
          exact Int.cast_one
      | succ i =>
          rw [matrix_flip_succ]
          change ((↑((if x 0 then 1 else -1) * flipSign i (Sensitivity.π x)) : ℝ)) = _
          rw [Int.cast_mul, ih]
          cases x 0 <;> simp

/-- The nine-coordinate weighted integer Huang matrix on the actual vertices. -/
def weightedMatrix (t : Fin 9 → ℤ) : Matrix (Q 9) (Q 9) ℤ :=
  fun x y => ∑ i, if flip x i = y then t i * flipSign i x else 0

/-- Evaluate a weighted signed row by summing its nine coordinate contributions. -/
def weightedAction {R : Type*} [Ring R] (w : Fin 9 → R) (f : Q 9 → R) : Q 9 → R :=
  fun x => ∑ i, w i * (flipSign i x : R) * f (flip x i)

theorem weightedMatrix_cast_mulVec {R : Type*} [Ring R]
    (t : Fin 9 → ℤ) (f : Q 9 → R) :
    ((weightedMatrix t).map (Int.castRingHom R)).mulVec f =
      weightedAction (fun i => (t i : R)) f := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, weightedMatrix, weightedAction,
    map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (flip x i)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

private theorem flipSign_eq_intCoeff (i : Fin 9) (x : Q 9) :
    flipSign i x = intCoeff x (flip x i) := by
  apply Int.cast_injective (α := ℝ)
  rw [flipSign_cast, intCoeff_cast]

theorem weightedAction_real (t : Fin 9 → ℤ) (f : Q 9 → ℝ) :
    weightedAction (fun i => (t i : ℝ)) f =
      (∑ i : Fin 9, (t i : ℝ) • gamma i) f := by
  funext x
  simp only [weightedAction, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, gamma_apply, flipSign_eq_intCoeff, intCoeff_cast, mul_assoc]

theorem weightedMatrix_same_parity (t : Fin 9 → ℤ) (x y : Q 9)
    (h : parity x = parity y) : weightedMatrix t x y = 0 := by
  unfold weightedMatrix
  apply Finset.sum_eq_zero
  intro i _
  have hflip : flip x i ≠ y := by
    rintro rfl
    exact cubeParity_ne_of_adj (flip_adj x i) h
  exact ite_eq_right hflip

/-- A supported real eigenvector with an integral eigenvalue divisible by the prime
yields a nonzero modular word supported in the same set on one cube parity. -/
theorem exists_one_parity_word (t : Fin 9 → ℤ) (K : Finset (Q 9))
    {p : ℕ} [Fact p.Prime] {s : ℤ} (hs : (p : ℤ) ∣ s)
    {f : Q 9 → ℝ} (hf : f ≠ 0) (hK : ∀ x ∉ K, f x = 0)
    (heigen : (∑ i : Fin 9, (t i : ℝ) • gamma i) f = (s : ℝ) • f) :
    ∃ (b : Bool) (g : Q 9 → ZMod p), g ≠ 0 ∧ (∀ x ∉ K, g x = 0) ∧
      (∀ x, parity x ≠ b → g x = 0) ∧
      weightedAction (fun i => (t i : ZMod p)) g = 0 := by
  have hcast : ((weightedMatrix t).map (Int.castRingHom ℝ)).mulVec f = (s : ℝ) • f := by
    rw [weightedMatrix_cast_mulVec, weightedAction_real, heigen]
  obtain ⟨b, g, hg, hgK, hparity, hkernel⟩ :=
    Q9IsotropicSupport.exists_zmod_kernel_supported_on_one_parity_of_real_eigenvector
      (weightedMatrix t) K parity (weightedMatrix_same_parity t)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd s p).2 hs) hf hK hcast
  exact ⟨b, g, hg, hgK, hparity, (weightedMatrix_cast_mulVec t g).symm.trans hkernel⟩

private def direction {R : Type*} [CommRing R] (i : Fin 9) : Module.End R (Q 9 → R) :=
  LinearMap.pi fun x => (flipSign i x : R) • LinearMap.proj (flip x i)

private theorem direction_apply {R : Type*} [CommRing R]
    (i : Fin 9) (f : Q 9 → R) (x : Q 9) :
    direction i f x = (flipSign i x : R) * f (flip x i) := rfl

private theorem direction_square {R : Type*} [CommRing R] (i : Fin 9) :
    direction (R := R) i * direction i = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  have hsign : flipSign i x * flipSign i (flip x i) = 1 := by
    apply Int.cast_injective (α := ℝ)
    simpa only [Int.cast_mul, Int.cast_one, flipSign_cast, gamma_apply, mul_one] using
      congrFun (TwentyPointEightWord.gamma_square i (fun _ => (1 : ℝ))) x
  have hcast : (flipSign i x : R) * (flipSign i (flip x i) : R) = 1 := by
    simpa only [Int.cast_mul, Int.cast_one] using congrArg (fun z : ℤ => (z : R)) hsign
  change direction i (direction i f) x = f x
  simp only [direction_apply, BalancedCriticalSpectrum.flip_flip, ← mul_assoc, hcast, one_mul]

private theorem direction_anticommute {R : Type*} [CommRing R] {i j : Fin 9} (hij : i ≠ j) :
    direction (R := R) i * direction j + direction j * direction i = 0 := by
  apply LinearMap.ext
  intro f
  funext x
  have hsign : flipSign i x * flipSign j (flip x i) =
      -(flipSign j x * flipSign i (flip x j)) := by
    apply Int.cast_injective (α := ℝ)
    simpa only [Int.cast_mul, Int.cast_neg, flipSign_cast, gamma_apply, mul_one, Pi.neg_apply]
      using congrFun (BalancedCubeGirth.gamma_anticommute hij (fun _ => (1 : ℝ))) x
  have hcast : (flipSign i x : R) * (flipSign j (flip x i) : R) =
      -((flipSign j x : R) * (flipSign i (flip x j) : R)) := by
    simpa only [Int.cast_mul, Int.cast_neg] using congrArg (fun z : ℤ => (z : R)) hsign
  change direction i (direction j f) x + direction j (direction i f) x = 0
  simp only [direction_apply, ← mul_assoc, hcast, BalancedCubeGirth.flip_comm x i j,
    neg_mul, neg_add_cancel]

/-- The weighted signed Huang operator as a linear endomorphism. -/
def weightedLinear {R : Type*} [CommRing R] (w : Fin 9 → R) :
    Module.End R (Q 9 → R) :=
  ∑ i, w i • direction i

private theorem weightedLinear_apply {R : Type*} [CommRing R]
    (w : Fin 9 → R) (f : Q 9 → R) : weightedLinear w f = weightedAction w f := by
  funext x
  simp only [weightedLinear, weightedAction, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, direction_apply, mul_assoc]

private def coordProjection {R : Type*} [CommRing R] (i : Fin 9) :
    Module.End R (Q 9 → R) :=
  LinearMap.pi fun x => if x i then LinearMap.proj x else 0

private theorem coordProjection_apply {R : Type*} [CommRing R]
    (i : Fin 9) (f : Q 9 → R) (x : Q 9) :
    coordProjection i f x = if x i then f x else 0 := by
  change (if x i then LinearMap.proj x else 0) f = _
  split <;> rfl

/-- Project onto vertices with bit `i` set, then apply the signed flip in direction `i`. -/
def halfFlip {R : Type*} [CommRing R] (i : Fin 9) : Module.End R (Q 9 → R) :=
  direction i * coordProjection i

private theorem direction_halfFlip_anticommutator {R : Type*} [CommRing R] (j i : Fin 9) :
    direction (R := R) j * halfFlip i + halfFlip i * direction j =
      if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    rw [ite_eq_left rfl, halfFlip, ← mul_assoc, direction_square, one_mul]
    apply LinearMap.ext
    intro f
    funext x
    change coordProjection i f x + direction i (coordProjection i (direction i f)) x = f x
    have hs := congrFun
      (congrArg (fun A : Module.End R (Q 9 → R) => A f) (direction_square i)) x
    change direction i (direction i f) x = f x at hs
    rw [coordProjection_apply, direction_apply, coordProjection_apply,
      BalancedCriticalSpectrum.flip_apply_same]
    cases hx : x i
    · simpa [hx, direction_apply] using hs
    · simp [hx]
  · have hcomm : coordProjection (R := R) i * direction j = direction j * coordProjection i := by
      apply LinearMap.ext
      intro f
      funext x
      change coordProjection i (direction j f) x = direction j (coordProjection i f) x
      have hbit : flip x j i = x i := by
        simp [BalancedCriticalSpectrum.flip, Ne.symm hji]
      simp only [coordProjection_apply, direction_apply, hbit]
      cases x i <;> simp
    rw [ite_eq_right hji]
    calc
      _ = (direction j * direction i + direction i * direction j) * coordProjection i := by
        simp only [halfFlip, add_mul, mul_assoc, hcomm]
      _ = 0 := by rw [direction_anticommute hji, zero_mul]

/-- The signed half-flip anticommutator has coefficient `w i` in every characteristic. -/
theorem weighted_halfFlip_anticommutator {R : Type*} [CommRing R]
    (w : Fin 9 → R) (i : Fin 9) :
    weightedLinear w * halfFlip i + halfFlip i * weightedLinear w = w i • 1 := by
  rw [weightedLinear, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [smul_mul_assoc, mul_smul_comm, ← smul_add, direction_halfFlip_anticommutator,
    smul_ite, smul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact ite_eq_right hji
  · simp

private theorem weightedLinear_square {R : Type*} [CommRing R] (w : Fin 9 → R) :
    weightedLinear w * weightedLinear w = (∑ i, w i ^ 2) • 1 := by
  let G (i : Fin 9) : Module.End R (Q 9 → R) := w i • direction i
  change (∑ i, G i) * (∑ i, G i) = (∑ i, w i ^ 2) • 1
  generalize (Finset.univ : Finset (Fin 9)) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, add_smul]
    have hcross : G i * (∑ j ∈ s, G j) + (∑ j ∈ s, G j) * G i = 0 := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro j hj
      have hij : i ≠ j := fun e => hi (e ▸ hj)
      dsimp [G]
      rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
        smul_smul, smul_smul, mul_comm (w j) (w i), ← smul_add, direction_anticommute hij,
        smul_zero]
    have hdiag : G i * G i = (w i ^ 2) • (1 : Module.End R (Q 9 → R)) := by
      simp only [G, smul_mul_assoc, mul_smul_comm, smul_smul, direction_square, pow_two]
    calc
      _ = G i * G i + (G i * (∑ j ∈ s, G j) + (∑ j ∈ s, G j) * G i) +
          (∑ j ∈ s, G j) * (∑ j ∈ s, G j) := by
        rw [add_mul, mul_add, mul_add]
        abel
      _ = _ := by rw [hcross, add_zero, hdiag, ih]

private theorem weightedAction_halfFlip_preimage {F : Type*} [Field F]
    (w : Fin 9 → F) (i : Fin 9) (hi : w i ≠ 0) (f : Q 9 → F)
    (hf : weightedAction w f = 0) : weightedAction w ((w i)⁻¹ • halfFlip i f) = f := by
  have h := congrArg (fun A : Module.End F (Q 9 → F) => A f)
    (weighted_halfFlip_anticommutator w i)
  change weightedLinear w (halfFlip i f) + halfFlip i (weightedLinear w f) = w i • f at h
  rw [weightedLinear_apply w f, hf, map_zero, add_zero] at h
  rw [← weightedLinear_apply, map_smul, h, smul_smul, inv_mul_cancel₀ hi, one_smul]

/-- An isotropic signed action with a nonzero coordinate has image equal to kernel.
The signed half-flip supplies a preimage in every field characteristic. -/
theorem weightedAction_image_eq_kernel {F : Type*} [Field F]
    (w : Fin 9 → F) (hw : ∑ i, w i ^ 2 = 0) (i : Fin 9) (hi : w i ≠ 0) :
    Set.range (weightedAction w) = {f | weightedAction w f = 0} := by
  ext f
  change (∃ g, weightedAction w g = f) ↔ weightedAction w f = 0
  constructor
  · rintro ⟨g, rfl⟩
    have hsq : weightedLinear w * weightedLinear w = 0 := by
      rw [weightedLinear_square, hw, zero_smul]
    simp only [← weightedLinear_apply]
    exact congrArg (fun A : Module.End F (Q 9 → F) => A g) hsq
  · intro hf
    exact ⟨_, weightedAction_halfFlip_preimage w i hi f hf⟩

private theorem flip_off_parity {b : Bool} {x : Q 9} (j : Fin 9) (hx : parity x ≠ !b) :
    parity (flip x j) ≠ b := by
  have hflip : (!parity x) = parity (flip x j) :=
    Bool.not_eq_iff.mpr (cubeParity_ne_of_adj (flip_adj x j))
  intro h
  exact hx (by simpa using congrArg Bool.not (hflip.trans h))

/-- On the opposite parity, the image from parity `b` equals the kernel
of the block going back to parity `b`. -/
theorem weightedAction_parity_image_eq_kernel {F : Type*} [Field F]
    (w : Fin 9 → F) (hw : ∑ i, w i ^ 2 = 0) (i : Fin 9) (hi : w i ≠ 0) (b : Bool) :
    weightedAction w '' {g | ∀ x, parity x ≠ b → g x = 0} =
      {f | weightedAction w f = 0 ∧ ∀ x, parity x ≠ !b → f x = 0} := by
  ext f
  change (∃ g, (∀ x, parity x ≠ b → g x = 0) ∧ weightedAction w g = f) ↔
    weightedAction w f = 0 ∧ ∀ x, parity x ≠ !b → f x = 0
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, ?_⟩
    · have him : weightedAction w g ∈ Set.range (weightedAction w) := ⟨g, rfl⟩
      rwa [weightedAction_image_eq_kernel w hw i hi] at him
    · intro x hx
      apply Finset.sum_eq_zero
      intro j _
      rw [hg _ (flip_off_parity j hx), mul_zero]
  · rintro ⟨hf, hparity⟩
    refine ⟨(w i)⁻¹ • halfFlip i f, ?_, weightedAction_halfFlip_preimage w i hi f hf⟩
    intro x hx
    have hfx : f (flip x i) = 0 :=
      hparity _ (flip_off_parity (b := !b) i (by simpa using hx))
    change (w i)⁻¹ • direction i (coordProjection i f) x = 0
    simp only [direction_apply, coordProjection_apply, hfx, ite_self, mul_zero, smul_zero]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
