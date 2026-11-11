/- GID: D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeDualCosetFusionRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ground-evaluation rigidity for full rational Hahn lattice-dual intertwiners. -/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetIntertwiner

/-!
Charged mixed Jacobi propagates ground normalizations between old-charge
pairs. Positive-current scalarity and oscillator reconstruction then give
an upper bound without assuming existence of a canonical intertwiner.
This is classical lattice-fusion mathematics in the conventions of
Bakalov--Kac, math/0402315v1, section 4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualConformalState LatticeDualCosetModule LatticeDualCosetConformal
open LatticePositiveEnergy LatticeDualCosetEnergy MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator Matrix
noncomputable section

variable (D : LatticeData) (a b : Charge D)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (I : Fields D) (hI : Lawful D a b H I)

variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (μ ν : Fin D.rank → ℚ)
variable (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
variable (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ))

include hI hHG hGH ha hb in
private theorem mode_leading (n l : Charge D) :
    mode I (ground D n) (-groundPower D μ ν n l-1) (ground D l) =
      groundScalar D I μ ν n l • ground D (n+l) := by
  simpa only [mode, show -(-groundPower D μ ν n l-1)-1 = groundPower D μ ν n l by ring]
    using ground_leading D a b H I hI hHG hGH μ ν ha hb n l

include hI hHG hGH ha hb in
private theorem mode_below (n l : Charge D) (τ : ℚ)
    (ht : -τ-1 < groundPower D μ ν n l) : mode I (ground D n) τ (ground D l) = 0 :=
  ground_below D a b H I hI hHG hGH μ ν ha hb n l (-τ-1) ht

include hI hHG hGH ha hb in
theorem charged_source_recurrence (m n l : Charge D) :
    epsilon D m n * groundScalar D I μ ν (m+n) l =
      epsilon D m (n+l) * groundScalar D I μ ν n l := by
  let A := chargedPower D a m n
  let C := chargedPower D b m l
  let Q := groundPower D μ ν n l
  have hJ := (hI.jacobi (ground D m) (ground D n) (ground D l)
    (-C) (-A-1) (-Q-1)).2.2.2
  have hl : (∑ᶠ j : ℕ, leftTerm D a I (ground D m) (ground D n)
      (ground D l) (-C) (-A-1) (-Q-1) j) =
      (epsilon D m n * groundScalar D I μ ν (m+n) l) • ground D (m+n+l) := by
    rw [finsum_eq_single _ 0]
    · simp only [leftTerm, integerBinomial, Ring.choose_zero_right, Int.cast_one,
        one_smul, Nat.cast_zero, add_zero, sub_zero]
      rw [charged_ground_leading]
      have ht : ((-C : ℤ) : ℚ) + (-Q-1) = -groundPower D μ ν (m+n) l-1 := by
        rw [groundPower_source_shift D b μ ν hb]
        dsimp [C, Q]
        push_cast
        ring
      rw [ht]
      rw [mode_smul_source, mode_leading D a b H I hI hHG hGH μ ν ha hb, smul_smul]
    · intro j hj
      have hz : ((action D a (ground D m))[[-A-1+j]]) (ground D n) = 0 :=
        charged_ground_above D a m n _ (by dsimp [A]; omega)
      simp [leftTerm, hz, mode]
  have hf : (∑ᶠ j : ℕ, firstTerm D a b I (ground D m) (ground D n)
      (ground D l) (-C) (-A-1) (-Q-1) j) =
      (epsilon D m (n+l) * groundScalar D I μ ν n l) • ground D (m+n+l) := by
    rw [finsum_eq_single _ 0]
    · simp only [firstTerm, pow_zero, integerBinomial, Ring.choose_zero_right,
        Int.cast_one, mul_one, one_smul, Nat.cast_zero, add_zero, sub_zero]
      rw [mode_leading D a b H I hI hHG hGH μ ν ha hb]
      have ht : -C+(-A-1) = -chargedPower D (a+b) m (n+l)-1 := by
        rw [chargedPower_add]
        dsimp [A, C]
        ring
      rw [ht, map_smul, charged_ground_leading, smul_smul]
      simp only [add_assoc, mul_comm]
    · intro j hj
      have hz := mode_below D a b H I hI hHG hGH μ ν ha hb n l
        (-Q-1+j) (by
          dsimp [Q]
          have hjq : (0 : ℚ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
          linarith)
      simp only [firstTerm, hz, map_zero, smul_zero]
  have hs : (∑ᶠ j : ℕ, secondTerm D b I (ground D m) (ground D n)
      (ground D l) (-C) (-A-1) (-Q-1) j) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hz := charged_ground_above D b m l (-C+j) (by dsimp [C]; omega)
    simp [secondTerm, hz]
  rw [hl, hf, hs, sub_zero] at hJ
  have hc := congrArg (fun v : Carrier D => constantCoeff (v (m+n+l))) hJ
  simpa [ground, constantCoeff_smul] using hc

include hI hHG hGH ha hb in
theorem charged_input_recurrence (m n l : Charge D) :
    epsilon D m (n+l) * groundScalar D I μ ν n l =
      StateFieldResidueReconstruction.epsilon (-chargedPower D a m n) *
        epsilon D m l * groundScalar D I μ ν n (m+l) := by
  let A := chargedPower D a m n
  let C := chargedPower D b m l
  let Q := groundPower D μ ν n l
  have hJ := (hI.jacobi (ground D m) (ground D n) (ground D l)
    (-C-1) (-A) (-Q-1)).2.2.2
  have hl : (∑ᶠ j : ℕ, leftTerm D a I (ground D m) (ground D n)
      (ground D l) (-C-1) (-A) (-Q-1) j) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hz := charged_ground_above D a m n (-A+j) (by dsimp [A]; omega)
    simp [leftTerm, hz, mode]
  have hf : (∑ᶠ j : ℕ, firstTerm D a b I (ground D m) (ground D n)
      (ground D l) (-C-1) (-A) (-Q-1) j) =
      (epsilon D m (n+l) * groundScalar D I μ ν n l) • ground D (m+n+l) := by
    rw [finsum_eq_single _ 0]
    · simp only [firstTerm, pow_zero, integerBinomial, Ring.choose_zero_right,
        Int.cast_one, mul_one, one_smul, Nat.cast_zero, add_zero, sub_zero]
      rw [mode_leading D a b H I hI hHG hGH μ ν ha hb]
      have ht : -C-1 + -A = -chargedPower D (a+b) m (n+l)-1 := by
        rw [chargedPower_add]
        dsimp [A, C]
        ring
      rw [ht, map_smul, charged_ground_leading, smul_smul]
      simp only [add_assoc, mul_comm]
    · intro j hj
      have hz := mode_below D a b H I hI hHG hGH μ ν ha hb n l
        (-Q-1+j) (by
          dsimp [Q]
          have hjq : (0 : ℚ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
          linarith)
      simp only [firstTerm, hz, map_zero, smul_zero]
  have hs : (∑ᶠ j : ℕ, secondTerm D b I (ground D m) (ground D n)
      (ground D l) (-C-1) (-A) (-Q-1) j) =
      (StateFieldResidueReconstruction.epsilon (-A) * epsilon D m l *
        groundScalar D I μ ν n (m+l)) • ground D (m+n+l) := by
    rw [finsum_eq_single _ 0]
    · simp only [secondTerm, pow_zero, integerBinomial, Ring.choose_zero_right,
        Int.cast_one, mul_one, one_smul, Nat.cast_zero, add_zero, sub_zero]
      rw [charged_ground_leading, map_smul]
      have ht : (-Q-1) + ((-A : ℤ) : ℚ) = -groundPower D μ ν n (m+l)-1 := by
        rw [groundPower_input_shift D a μ ν ha]
        dsimp [A, Q]
        push_cast
        ring
      rw [ht, mode_leading D a b H I hI hHG hGH μ ν ha hb]
      simp only [smul_smul, add_comm, add_left_comm, add_assoc, mul_assoc]
    · intro j hj
      have hz := charged_ground_above D b m l (-C-1+j) (by dsimp [C]; omega)
      simp [secondTerm, hz]
  rw [hl, hf, hs] at hJ
  have he := sub_eq_zero.mp hJ.symm
  have hc := congrArg (fun v : Carrier D => constantCoeff (v (m+n+l))) he
  simpa [ground, constantCoeff_smul, A] using hc

include hI hHG hGH ha hb in
theorem ground_normalization_character (n l : Charge D) :
    groundScalar D I μ ν n l = epsilon D n l * paritySign (∑ i, l i * a i) *
      groundScalar D I μ ν 0 0 := by
  have hin := charged_input_recurrence D a b H I hI hHG hGH μ ν ha hb l 0 0
  simp [epsilon, lowerCocycleExponent, paritySign, chargedPower, bilinear,
    StateFieldResidueReconstruction.epsilon, neg_one_zpow_eq_ite, even_neg] at hin
  have hbase : groundScalar D I μ ν 0 l =
      paritySign (∑ i, l i * a i) * groundScalar D I μ ν 0 0 := by
    by_cases heven : Even (∑ i, l i*a i)
    · simpa [paritySign, heven] using hin.symm
    · simpa [paritySign, heven] using congrArg (fun z : ℂ => -z) hin.symm
  have hout := charged_source_recurrence D a b H I hI hHG hGH μ ν ha hb n 0 l
  have he : epsilon D n 0 = 1 := by simp [epsilon, lowerCocycleExponent, paritySign]
  simpa only [he, one_mul, zero_add, add_zero, hbase, mul_assoc] using hout

include hI hHG hGH ha hb in
theorem pair_ground_detects_zero (n l : Charge D)
    (hc : groundScalar D I μ ν n l = 0) :
    ∀ s : ℚ, (I (ground D n)).coeff s (ground D l) = 0 := by
  let f : ℚ → Carrier D := fun s => (I (ground D n)).coeff s (ground D l)
  have hp : (Function.support f).IsPWO :=
    (I (ground D n)).isPWO_support_coeff (ground D l)
  intro s
  by_cases hs : s ∈ Function.support f
  · change f s = 0
    apply hp.isWF.induction hs
    intro t ht ih
    have lower (z : ℚ) (hz : z < t) : f z = 0 := by
      by_cases hmem : z ∈ Function.support f
      · exact ih z hmem hz
      · exact Function.notMem_support.mp hmem
    have pos (i : Fin D.rank) (r : ℕ) :
        neutralPolynomialMode D i 0 ((r : ℤ)+1) (f t (n+l)) = 0 := by
      have hw := ground_current_ward D a b H I hI n (ground D l) i ((r : ℤ)+1) (-t-1)
      have hv : ((action D b (currentState D i))[[(r : ℤ)+1]]) (ground D l) = 0 := by
        simpa only [Nat.cast_add, Nat.cast_one, show r+1 ≠ 0 by omega, ite_false]
          using current_ground D b l i (r+1)
      have hm : mode I (ground D n) (((r : ℤ)+1 : ℤ)+(-t-1)) (ground D l) = 0 := by
        have he : -(((r : ℤ)+1 : ℤ)+(-t-1) : ℚ)-1 = t-(r+1) := by push_cast; ring
        simpa only [mode, he] using lower (t-(r+1)) (by have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg _; linarith)
      rw [hv, map_zero, hm, smul_zero, sub_zero] at hw
      have hh := congrArg (fun v : Carrier D => v (n+l)) hw
      rw [current_component] at hh
      simpa only [f, mode, show -(-t-1)-1 = t by ring, Finsupp.zero_apply,
        shiftedCurrentPolynomial, neutralPolynomialMode,
        show ¬ (r : ℤ)+1 < 0 by omega, show (r : ℤ)+1 ≠ 0 by omega,
        ite_false] using hh
    have hscalar := LatticeSectorIntertwiner.scalar_of_positive_currents D H hHG 0 (f t (n+l)) pos
    have hproj : f t = Finsupp.single (n+l) (f t (n+l)) := by
      simpa only [mode, show -(-t-1)-1 = t by ring] using
        ground_charge_projection D a b H I hI hHG n l (-t-1)
    have hcc : constantCoeff (f t (n+l)) ≠ 0 := by
      intro hz
      have he : f t = 0 := by rw [hproj, hscalar, hz, zero_smul, Finsupp.single_zero]
      exact ht he
    have spec := (ground_spectrum D a b H I hI hHG hGH μ ν ha hb n l (n+l) 0 t
      (by change (f t (n+l)).coeff 0 ≠ 0; exact hcc)).2
    have he : t = groundPower D μ ν n l := by simpa [oscillatorEnergy] using spec
    rw [he] at hcc
    exact False.elim (hcc hc)
  · exact Function.notMem_support.mp hs

private theorem reconstruct_input (n : Charge D)
    (hground : ∀ l τ, mode I (ground D n) τ (ground D l) = 0)
    (hI : Lawful D a b H I) (l : Charge D) (v : Oscillator D) :
    ∀ τ, mode I (ground D n) τ (Finsupp.single l v) = 0 := by
  induction v using MvPolynomial.induction_on with
  | C c =>
    intro τ
    rw [show (C c : Oscillator D) = c • 1 by simp [smul_eq_C_mul],
      ← Finsupp.smul_single, map_smul, hground, smul_zero]
  | add p q hp hq =>
    intro τ
    rw [Finsupp.single_add, map_add, hp, hq, add_zero]
  | mul_X p x hp =>
    intro τ
    have h := ground_current_ward D a b H I hI n (Finsupp.single l p) x.1
      (-(x.2 : ℤ)-1) τ
    rw [hp τ, hp ((-(x.2 : ℤ)-1 : ℤ)+τ), map_zero, smul_zero, zero_sub,
      neg_eq_zero] at h
    rw [currentState, action_current_coefficients] at h
    simpa only [shiftedCurrentPolynomial, show -(x.2 : ℤ)-1 < 0 by omega,
      ite_true, LinearMap.mulLeft_apply, show (-(-(x.2 : ℤ)-1)-1).toNat = x.2 by omega,
      Prod.eta, mul_comm] using h

private theorem reconstruct_source (hI : Lawful D a b H I)
    (hground : ∀ n τ v, mode I (ground D n) τ v = 0)
    (n : Charge D) (u : Oscillator D) :
    ∀ τ v, mode I (Finsupp.single n u) τ v = 0 := by
  induction u using MvPolynomial.induction_on with
  | C c =>
    intro τ v
    rw [show (C c : Oscillator D) = c • 1 by simp [smul_eq_C_mul], ← Finsupp.smul_single]
    rw [mode_smul_source, hground, smul_zero]
  | add p q hp hq =>
    intro τ v
    simp only [Finsupp.single_add, mode_add_source, hp, hq, add_zero]
  | mul_X p x hp =>
    intro τ v
    let r : ℤ := -(x.2 : ℤ)-1
    have h := (hI.jacobi (currentState D x.1) (Finsupp.single n p) v 0 r τ).2.2.2
    have hl : (∑ᶠ j : ℕ, leftTerm D a I (currentState D x.1)
        (Finsupp.single n p) v 0 r τ j) =
        mode I (((action D a (currentState D x.1))[[r]]) (Finsupp.single n p)) τ v := by
      rw [finsum_eq_single _ 0]
      · simp [leftTerm, integerBinomial]
      · intro j hj
        simp [leftTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
    rw [hl] at h
    simp only [firstTerm, secondTerm, hp, map_zero, smul_zero, finsum_zero, sub_zero] at h
    rw [currentState, action_current_coefficients] at h
    simpa only [r, shiftedCurrentPolynomial, show -(x.2 : ℤ)-1 < 0 by omega,
      ite_true, LinearMap.mulLeft_apply, show (-(-(x.2 : ℤ)-1)-1).toNat = x.2 by omega,
      Prod.eta, mul_comm] using h

include hI in
theorem ground_sequence_detects_zero
    (hground : ∀ n l τ, mode I (ground D n) τ (ground D l) = 0) : I = 0 := by
  have hi (n : Charge D) (τ : ℚ) (v : Carrier D) : mode I (ground D n) τ v = 0 := by
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp [hv, hw]
    | single l p => exact reconstruct_input D a b H I n (hground n) hI l p τ
  have hall (u v : Carrier D) (τ : ℚ) : mode I u τ v = 0 := by
    induction u using Finsupp.induction_linear with
    | zero => simp [mode]
    | add u w hu hw => simp only [mode_add_source, hu, hw, add_zero]
    | single n p => exact reconstruct_source D a b H I hI hi n p τ v
  apply LinearMap.ext
  intro u
  apply HVertexOperator.coeff_inj
  funext s
  apply LinearMap.ext
  intro v
  simpa only [mode, show -(-s-1)-1 = s by ring, LinearMap.zero_apply,
    map_zero, Pi.zero_apply] using hall u v (-s-1)

include hI hHG hGH ha hb in
/-- One specified ground scalar detects zero in the genuine full-law space.
No nonzero or canonical field is assumed. -/
theorem normalized_ground_detects_zero
    (heval : groundScalar D I μ ν 0 0 = 0) : I = 0 := by
  apply ground_sequence_detects_zero D a b H I hI
  intro n l τ
  have hc : groundScalar D I μ ν n l = 0 := by
    rw [ground_normalization_character D a b H I hI hHG hGH μ ν ha hb, heval, mul_zero]
  exact pair_ground_detects_zero D a b H I hI hHG hGH μ ν ha hb n l hc (-τ-1)

/-- Evaluation at old charge zero and raw power pairing(mu,nu). -/
def groundEvaluation : operatorSpace D a b H →ₗ[ℂ] ℂ where
  toFun J := groundScalar D J.val μ ν 0 0
  map_add' J K := by simp [groundScalar]
  map_smul' c J := by simp [groundScalar]

include hHG hGH ha hb in
/-- Fusion multiplicity is at most one, without an existence assumption. -/
theorem groundEvaluation_injective : Function.Injective (groundEvaluation D a b H μ ν) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro J hJ
  apply Subtype.ext
  exact normalized_ground_detects_zero D a b H J.val J.property hHG hGH μ ν ha hb hJ

end
end D5.S3.VertexAlgebra.LatticeDualCosetIntertwiner
