/- GID: D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddFixedModeIrreducibility
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddFixedModeIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native fixed-sector modes act irreducibly on the actual odd half-Fock module. -/

/- proof_shape: fixedParitySlice_odd_irreducible: content
admission_basis: escape-witness
escape_witness: Pairs of negative currents generate every odd oscillator monomial
from a one-oscillator seed for the same ground vector. The live induction pairs
the letters of the monomial's occurrence list down to the final letter.
Literature status: classical twisted lattice orbifold theory, no novelty claim.
-/
import D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddCyclicExtraction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Irreducibility of the actual negative-parity twisted module under fixed-sector modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddFixedModeIrreducibility

open LatticeGeneratingFieldLocality
open LatticeAllStateField (occurrences occurrences_product)
open LatticeFiniteNegativeGeneration (bilinear_neg_left)
open LatticeHalfFock (tensorCurrent tensorEnd current_negative)
open LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedMonodromy (ground_neg norm_neg norm_even)
open LatticeHalfFockCorrectedField
open LatticeHalfFockParityField (fixedParitySlice paritySpace)
open LatticeHalfFockOddCyclicExtraction
open ActualFieldIrreducible (groundSubrepresentation)
open ActualTensorGroundIntersection (coordinates partialEnd)
open LatticeInvolution (FixedCarrier mem_fixedSpace thetaLinear theta_single)
open LatticeTwistedGroundRealization (Half actual_twisted_ground_representation)
open MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

private theorem halfCreationCoeff_zero (D : LatticeData) (charge : Charge D) :
    halfCreationCoeff D charge 0 = 1 := by
  simpa [halfCreationCoeff] using LatticeHalfFockChargedCoefficients.exponential_constant D charge

/-- The creator correction for a single frequency factors through the Gram pairing. -/
private theorem oscillatorCoefficient_X_sum (D : LatticeData) (charge : Charge D)
    (e : ℤ) (j : ℕ) (c : Fin D.rank → ℂ) :
    oscillatorCoefficient D charge e (∑ i, c i • (X (i, j) : Oscillator D)) =
      (∑ i, c i • (X (i, j) : Oscillator D)) * oscillatorCoefficient D charge e 1 -
        (∑ i, c i * (bilinear D charge (unitCharge D i) : ℂ)) •
          oscillatorCoefficient D charge (e + ((2 * j + 1 : ℕ) : ℤ)) 1 := by
  have on_X (i : Fin D.rank) :
      oscillatorCoefficient D charge e (X (i, j)) =
        X (i, j) * oscillatorCoefficient D charge e 1 -
          (bilinear D charge (unitCharge D i) : ℂ) •
            oscillatorCoefficient D charge (e + ((2 * j + 1 : ℕ) : ℤ)) 1 := by
    simpa only [mul_one, LatticeHalfFockChargedCoefficients.omega] using
      oscillator_coefficient_X_mul D charge e (i, j) (1 : Oscillator D)
  simp only [map_sum, map_smul, on_X, smul_sub, ← smul_mul_assoc, smul_smul,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_smul]

private theorem chargedCoefficient_orthogonal_one_oscillator (D : LatticeData)
    (hu : IsUnit D.G.det) (charge : Charge D) (j : ℕ) (c : Fin D.rank → ℂ)
    (hc : (∑ i, c i * (bilinear D charge (unitCharge D i) : ℂ)) = 0)
    (g : ActualGround D hu) :
    chargedCoefficient D hu charge (-chargeNorm D charge)
        ((∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] g) =
      chargeScalar D charge •
        ((∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] groundAction D hu charge g) := by
  let P : Oscillator D := ∑ i, c i • (X (i, j) : Oscillator D)
  let multiply : Module.End ℂ (ActualTensor D hu) :=
    TensorProduct.map (LinearMap.mulLeft ℂ P) LinearMap.id
  have on_P : oscillatorCoefficient D charge (-chargeNorm D charge) P =
      P * oscillatorCoefficient D charge (-chargeNorm D charge) 1 := by
    dsimp only [P]
    rw [oscillatorCoefficient_X_sum, hc, zero_smul, sub_zero]
  change chargedCoefficient D hu charge (-chargeNorm D charge) (P ⊗ₜ[ℂ] g) =
    chargeScalar D charge • (P ⊗ₜ[ℂ] groundAction D hu charge g)
  calc
    _ = multiply (chargedCoefficient D hu charge (-chargeNorm D charge)
        ((1 : Oscillator D) ⊗ₜ[ℂ] g)) := by
      simp only [multiply, chargedCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
        map_smul, LinearMap.mulLeft_apply, LinearMap.id_apply, on_P]
    _ = _ := by
      rw [charged_vacuum_coefficient, neg_add_cancel, halfCreationCoeff_zero]
      simp only [multiply, map_smul, TensorProduct.map_tmul, LinearMap.mulLeft_apply,
        LinearMap.id_apply, mul_one]

/-- The literal corrected charge pair acts by the lifted ground action on a
one-oscillator polarization orthogonal to the charge in the Gram form. -/
private theorem correctedField_charge_pair_orthogonal_one_oscillator (D : LatticeData)
    (hu : IsUnit D.G.det) (charge : Charge D) (j : ℕ) (c : Fin D.rank → ℂ)
    (hc : (∑ i, c i * (bilinear D charge (unitCharge D i) : ℂ)) = 0)
    (g : ActualGround D hu) :
    (correctedField D hu (Finsupp.single charge (1 : Oscillator D) +
      Finsupp.single (-charge) 1)).coeff (-chargeNorm D charge)
        ((∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] g) =
      (2 * chargeScalar D charge) •
        ((∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] groundAction D hu charge g) := by
  have horth_neg : (∑ i, c i * (bilinear D (-charge) (unitCharge D i) : ℂ)) = 0 := by
    simp only [bilinear_neg_left, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, hc, neg_zero]
  have hpos := chargedCoefficient_orthogonal_one_oscillator D hu charge j c hc g
  have hneg := chargedCoefficient_orthogonal_one_oscillator D hu (-charge) j c horth_neg g
  have hscalar_neg : chargeScalar D (-charge) = chargeScalar D charge := by
    simp only [chargeScalar, norm_neg]
  rw [norm_neg, hscalar_neg, ground_neg] at hneg
  -- Additivity also counts both terms when charge = 0.
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, corrected_singleton_coeff_charged,
    chargedField, HVertexOperator.coeff_of_coeff]
  rw [hpos, hneg, two_mul, add_smul]

/-- Stability under the fixed parity modes transports ground vectors along a
charge whenever the chosen one-oscillator polarization is orthogonal to it. -/
private theorem groundAction_mem_of_fixedParitySlice_stable (D : LatticeData)
    (hu : IsUnit D.G.det) (S : Submodule ℂ (paritySpace D hu (-1)))
    (stable : ∀ (a : FixedCarrier D) (n : ℤ) (x : paritySpace D hu (-1)),
      x ∈ S → ((fixedParitySlice D hu (-1) a)[[n]]) x ∈ S)
    (charge : Charge D) (j : ℕ) (c : Fin D.rank → ℂ)
    (hc : (∑ i, c i * (bilinear D charge (unitCharge D i) : ℂ)) = 0)
    (g : ActualGround D hu) (x : paritySpace D hu (-1)) (hx : x ∈ S)
    (hval : x.val = (∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] g) :
    ((∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] groundAction D hu charge g) ∈
      S.map (paritySpace D hu (-1)).subtype := by
  let a : FixedCarrier D := ⟨Finsupp.single charge 1 + Finsupp.single (-charge) 1, by
    rw [mem_fixedSpace, map_add]
    change thetaLinear D (Finsupp.single charge (1 : Oscillator D)) +
      thetaLinear D (Finsupp.single (-charge) 1) = _
    simpa only [theta_single, map_one, neg_neg] using
      (add_comm (Finsupp.single (-charge) (1 : Oscillator D)) (Finsupp.single charge 1))⟩
  obtain ⟨halfNorm, hhalfNorm⟩ := norm_even D charge
  let n : ℤ := halfNorm - 1
  have exponent : 2 * (-n - 1) = -chargeNorm D charge := by
    dsimp only [n]
    omega
  let y := ((fixedParitySlice D hu (-1) a)[[n]]) x
  have hread : y.val = (2 * chargeScalar D charge) •
      ((∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] groundAction D hu charge g) := by
    change (correctedField D hu a.val).coeff (2 * (-n - 1)) x.val = _
    rw [exponent, hval]
    exact correctedField_charge_pair_orthogonal_one_oscillator D hu charge j c hc g
  let T := S.map (paritySpace D hu (-1)).subtype
  have hscaled : (2 * chargeScalar D charge) •
      ((∑ i, c i • (X (i, j) : Oscillator D)) ⊗ₜ[ℂ] groundAction D hu charge g) ∈ T :=
    Submodule.mem_map.mpr ⟨y, stable a n x hx, hread⟩
  have hcharge : chargeScalar D charge ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hscalar : (2 : ℂ) * chargeScalar D charge ≠ 0 := mul_ne_zero (by norm_num) hcharge
  simpa only [smul_smul, inv_mul_cancel₀ hscalar, one_smul] using
    T.smul_mem (((2 : ℂ) * chargeScalar D charge)⁻¹) hscaled


private def create (D : LatticeData) (hu : IsUnit D.G.det) (a : Index D) :
    Module.End ℂ (ActualTensor D hu) :=
  tensorEnd D (ActualGround D hu) (LinearMap.mulLeft ℂ (X a))

private theorem create_eq_current (D : LatticeData) (hu : IsUnit D.G.det) (a : Index D) :
    create D hu a = tensorCurrent D (ActualGround D hu) a.1 (-(a.2 : ℤ) - 1) := by
  rcases a with ⟨i, j⟩
  simp only [create, tensorCurrent, current_negative]

private theorem create_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Index D) (p : Oscillator D) (g : ActualGround D hu) :
    create D hu a (p ⊗ₜ[ℂ] g) = ((X a : Oscillator D) * p) ⊗ₜ[ℂ] g := by
  simp only [create, tensorEnd, TensorProduct.map_tmul, LinearMap.mulLeft_apply,
    LinearMap.id_apply]

private theorem partialEnd_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Index D) (p : Oscillator D) (g : ActualGround D hu) :
    partialEnd D hu a (p ⊗ₜ[ℂ] g) = (pderiv a p) ⊗ₜ[ℂ] g := by
  simp only [partialEnd, tensorEnd, TensorProduct.map_tmul, Derivation.coeFn_coe,
    LinearMap.id_apply]

/-- One Gram pairing leaves a nonzero complex polarization in rank at least two. -/
private theorem exists_orthogonal_color (D : LatticeData) (hrank : 2 ≤ D.rank)
    (charge : Charge D) :
    ∃ c : Fin D.rank → ℂ,
      (∑ i, c i * (bilinear D charge (unitCharge D i) : ℂ)) = 0 ∧
        ∃ i, c i ≠ 0 := by
  classical
  let pair : (Fin D.rank → ℂ) →ₗ[ℂ] ℂ :=
    (dotProductBilin ℂ ℂ).flip (fun i => (bilinear D charge (unitCharge D i) : ℂ))
  have hdim : Module.finrank ℂ ℂ < Module.finrank ℂ (Fin D.rank → ℂ) := by
    rw [Module.finrank_self, Module.finrank_pi, Fintype.card_fin]
    omega
  have hker : LinearMap.ker pair ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hc, hc₀⟩ := (LinearMap.ker pair).ne_bot_iff.mp hker
  refine ⟨c, ?_, ?_⟩
  · change pair c = 0 at hc
    exact hc
  · by_contra! hz
    exact hc₀ (funext hz)

/-- The partial at one color reads its coefficient in the one-oscillator sum. -/
private theorem pderiv_color_sum (D : LatticeData) (j : ℕ) (c : Fin D.rank → ℂ)
    (i : Fin D.rank) :
    pderiv (i, j) (∑ k, c k • (X (k, j) : Oscillator D)) =
      c i • (1 : Oscillator D) := by
  classical
  change (pderiv (i, j)).toLinearMap (∑ k, c k • (X (k, j) : Oscillator D)) = _
  rw [map_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp only [map_smul, Derivation.coeFn_coe, pderiv_X_self]
  · intro k _ hk
    have hindex : (k, j) ≠ (i, j) := fun h => hk (congrArg Prod.fst h)
    simp only [map_smul, Derivation.coeFn_coe, pderiv_X_of_ne hindex, smul_zero]

/-- Pair the letters of the occurrence list until the last variable supplies
the one-oscillator seed. -/
private theorem odd_monomial_tmul_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (T : Submodule ℂ (ActualTensor D hu))
    (hpair : ∀ a b : Index D, ∀ t ∈ T, create D hu a (create D hu b t) ∈ T)
    (g : ActualGround D hu) (hvariable : ∀ a : Index D, (X a ⊗ₜ[ℂ] g) ∈ T)
    (d : Index D →₀ ℕ) (hd : Odd d.degree) :
    ((monomial d 1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ T := by
  have hword (w : List (Index D)) (hw : Odd w.length) :
      ((w.map (fun a => (X a : Oscillator D))).prod ⊗ₜ[ℂ] g) ∈ T := by
    induction w using List.twoStepInduction with
    | nil =>
      simp only [List.length_nil, Nat.odd_iff] at hw
      omega
    | singleton a =>
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        using hvariable a
    | cons_cons a b w ih _ =>
      have hw' : Odd w.length := by
        rw [List.length_cons, List.length_cons, Nat.odd_iff] at hw
        rw [Nat.odd_iff]
        omega
      simpa only [create_tmul, List.map_cons, List.prod_cons] using hpair a b _ (ih hw')
  rw [← occurrences_product D d]
  exact hword _ (by rwa [occurrences_length])

set_option maxHeartbeats 1000000 in
-- Elaborating the tensor-coordinate and polynomial expansions needs a larger local budget.
/-- For rank at least two the native fixed-sector integer modes act
irreducibly on the actual negative-parity twisted module. -/
theorem fixedParitySlice_odd_irreducible (D : LatticeData) (hu : IsUnit D.G.det)
    (hrank : 2 ≤ D.rank)
    (S : Submodule ℂ (paritySpace D hu (-1)))
    (stable : ∀ (a : FixedCarrier D) (n : ℤ), ∀ x ∈ S,
      ((fixedParitySlice D hu (-1) a)[[n]]) x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let T := S.map (paritySpace D hu (-1)).subtype
  obtain ⟨a₀, g₀, x₀, hg₀, _, hx₀, hval₀⟩ :=
    nonzero_fixedParitySlice_stable_submodule_contains_one_oscillator ⟨D, hu⟩ S hS stable
  let U : Submodule ℂ (ActualGround D hu) :=
    T.comap (TensorProduct.mk ℂ (Oscillator D) (ActualGround D hu) (X a₀))
  have hseed : g₀ ∈ U := by
    change ((X a₀ : Oscillator D) ⊗ₜ[ℂ] g₀) ∈ T
    exact Submodule.mem_map.mpr ⟨x₀, hx₀, hval₀⟩
  have htransfer (b a : Index D) (t : ActualTensor D hu) (ht : t ∈ T) :
      create D hu b (partialEnd D hu a t) ∈ T := by
    rw [create_eq_current]
    exact fixedParitySlice_stable_current_partial_mem D hu S stable b.1 (-(b.2 : ℤ) - 1)
      a t ht
  have hcreations (a b : Index D) (t : ActualTensor D hu) (ht : t ∈ T) :
      create D hu a (create D hu b t) ∈ T := by
    rw [create_eq_current D hu a, create_eq_current D hu b]
    exact fixedParitySlice_stable_current_pair_mem D hu S stable a.1 b.1
      (-(a.2 : ℤ) - 1) (-(b.2 : ℤ) - 1) t ht
  have hvariable (g : ActualGround D hu) (hg : g ∈ U) (b : Index D) :
      ((X b : Oscillator D) ⊗ₜ[ℂ] g) ∈ T := by
    change ((X a₀ : Oscillator D) ⊗ₜ[ℂ] g) ∈ T at hg
    simpa only [partialEnd_tmul, pderiv_X_self, create_tmul, mul_one] using
      htransfer b a₀ _ hg
  have hground (charge : Charge D) (g : ActualGround D hu) (hg : g ∈ U) :
      groundAction D hu charge g ∈ U := by
    obtain ⟨c, hc, i, hi⟩ := exists_orthogonal_color D hrank charge
    let j := a₀.2
    let P : Oscillator D := ∑ k, c k • (X (k, j) : Oscillator D)
    have hP : (P ⊗ₜ[ℂ] g) ∈ T := by
      dsimp only [P]
      rw [TensorProduct.sum_tmul]
      apply T.sum_mem
      intro k _
      simpa only [TensorProduct.smul_tmul'] using T.smul_mem (c k) (hvariable g hg (k, j))
    obtain ⟨x, hx, hval⟩ := Submodule.mem_map.mp hP
    have hcharge : (P ⊗ₜ[ℂ] groundAction D hu charge g) ∈ T :=
      groundAction_mem_of_fixedParitySlice_stable D hu S stable charge j c hc g x hx hval
    have hscaled := htransfer a₀ (i, j) _ hcharge
    change ((X a₀ : Oscillator D) ⊗ₜ[ℂ] groundAction D hu charge g) ∈ T
    have hread :
        create D hu a₀ (partialEnd D hu (i, j) (P ⊗ₜ[ℂ] groundAction D hu charge g)) =
          c i • ((X a₀ : Oscillator D) ⊗ₜ[ℂ] groundAction D hu charge g) := by
      have hdP : pderiv (i, j) P = c i • (1 : Oscillator D) := pderiv_color_sum D j c i
      rw [partialEnd_tmul, hdP, create_tmul, mul_smul_comm, mul_one, ← TensorProduct.smul_tmul']
    rw [hread] at hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hi, one_smul] using T.smul_mem (c i)⁻¹ hscaled
  have hU : U = ⊤ := by
    let V := groundSubrepresentation D hu U hground
    let : (groundRepresentation D hu).IsIrreducible :=
      (Classical.choose_spec
        (Classical.choose_spec (actual_twisted_ground_representation D hu))).2.1
    rcases eq_bot_or_eq_top V with bottom | top
    · have member : g₀ ∈ V := hseed
      rw [bottom] at member
      exact (hg₀ member).elim
    · exact congrArg (fun W : Subrepresentation (groundRepresentation D hu) => W.toSubmodule) top
  have hall (g : ActualGround D hu) : g ∈ U := by
    rw [hU]
    exact Submodule.mem_top
  have hmonomial (g : ActualGround D hu) (d : Index D →₀ ℕ) (hd : Odd d.degree) :
      ((monomial d 1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ T :=
    odd_monomial_tmul_mem D hu T hcreations g (hvariable g (hall g)) d hd
  apply top_unique
  intro x _
  let t : ActualTensor D hu := x.val
  have ht : t ∈ paritySpace D hu (-1) := x.property
  have hdecompose :
      t = ∑ b : Half (groundRank D hu),
        coordinates D hu t b ⊗ₜ[ℂ] (Pi.single b (1 : ℂ) : ActualGround D hu) := by
    let q := coordinates D hu t
    calc
      t = (coordinates D hu).symm q := ((coordinates D hu).symm_apply_apply t).symm
      _ = (coordinates D hu).symm (∑ b, Pi.single b (q b)) :=
        congrArg (fun f => (coordinates D hu).symm f)
          (LinearMap.sum_single_apply (fun _ : Half (groundRank D hu) => Oscillator D) q).symm
      _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun b _ =>
          TensorProduct.piScalarRight_symm_single ℂ ℂ (Oscillator D)
            (Half (groundRank D hu)) (q b) b
  have hm : t ∈ T := by
    rw [hdecompose]
    apply T.sum_mem
    intro b _
    rw [MvPolynomial.as_sum (coordinates D hu t b), TensorProduct.sum_tmul]
    apply T.sum_mem
    intro d hd
    have hodd := odd_of_mem_coordinate_support D hu t ht b d hd
    have hterm := hmonomial (Pi.single b (1 : ℂ)) d hodd
    simpa only [TensorProduct.smul_tmul', smul_monomial, smul_eq_mul, mul_one] using
      T.smul_mem ((coordinates D hu t b).coeff d) hterm
  obtain ⟨y, hy, hyval⟩ := Submodule.mem_map.mp hm
  have hyx : y = x := Subtype.ext hyval
  exact hyx ▸ hy

end
end D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockOddFixedModeIrreducibility
