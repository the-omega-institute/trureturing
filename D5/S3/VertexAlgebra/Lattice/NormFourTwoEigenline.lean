/- GID: D5/S3/VertexAlgebra/Lattice/NormFourTwoEigenline
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourTwoEigenline
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The nonzero actual norm-four vector is the complete fixed-energy-two eigenline at two. -/

import D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
import Batteries.Tactic.OpenPrivate

/-!
The production norm-four vector and its self-products retain the
Dong--Mason--Zhu attribution recorded by Shimakura, arXiv:1202.6107, (1.3).
The actual lattice construction and contractions retain the Bakalov--Kac
and Frenkel--Lepowsky--Meurman attribution of the imported suppliers.
The rank-one image calculation uses every vector of the complete actual
fixed-energy-two basis, including repeated neutral colours.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourTwoEigenline
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction LatticeActualVertexAlgebra
open LatticeActualProductKernel LatticeActualGeneratorLocality
open LatticeSugawaraCurrents LatticeSugawaraConformal LatticePositiveEnergy
open LatticeInvolution NormFourVirasoroVector RootlessLowGrades
open InvolutionRootlessLowGrades MvPolynomial
open scoped BigOperators VertexOperator Classical
noncomputable section

open private Q ground E E_neg Gi R quadratic_sum zero_mode_Q zero_mode_R
  zero_mode_A zero_mode_E zero_mode_orbit_middle zero_mode_orbit_add
  zero_mode_orbit_sub phase_square epsilon_norm_four norm_four_inner_bounds
  actual_basis_neutral_coe from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private pairOccupation_pair from D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
open private canonicalFixedEnergy_eq_fixedGrade gradeTwoBasis_charge_coe
  from D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

private def projector (D : LatticeData) (a : Charge D) (s : ℂ) :
    Module.End ℂ (Carrier D) :=
  let L := mode D a s 0
  (16 / 93 : ℂ) • (L * (L - (1 / 16 : ℂ) • 1) * (L - (1 / 2 : ℂ) • 1))

private theorem projector_Q (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (i j : Fin D.rank) :
    projector D a s (Q D i j) = (Gi D i a * Gi D j a / 2) • vector D a s := by
  simp only [projector, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub, map_smul]
  simp only [zero_mode_Q, map_add, map_smul,
    zero_mode_R D a ha, zero_mode_A D a ha, zero_mode_E D a ha]
  change _ = _ • ((1 / 16 : ℂ) • quadraticState D a + (s / 4) • E D a)
  have hs3 : s ^ 3 = s := by calc
    s ^ 3 = s ^ 2 * s := by ring
    _ = s := by rw [hs, one_mul]
  match_scalars <;> ring_nf <;> simp only [hs, hs3] <;> ring

private theorem projector_matching (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    projector D a s (E D a) = (2 * s) • vector D a s := by
  simp only [projector, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub, map_smul]
  simp only [zero_mode_E D a ha, zero_mode_A D a ha, map_add, map_smul]
  change _ = _ • ((1 / 16 : ℂ) • quadraticState D a + (s / 4) • E D a)
  have hs3 : s ^ 3 = s := by calc
    s ^ 3 = s ^ 2 * s := by ring
    _ = s := by rw [hs, one_mul]
  match_scalars <;> ring_nf <;> simp only [hs, hs3] <;> ring

private theorem projector_of_half_square (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D) (h : mode D a s 0 (mode D a s 0 v) =
      (1 / 2 : ℂ) • mode D a s 0 v) : projector D a s v = 0 := by
  simp only [projector, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub, map_smul]
  rw [h, map_smul, h]
  module

private theorem projector_two_block (D : LatticeData) (a : Charge D) (s c : ℂ)
    (u w : Carrier D) (hc : c * c = (1 / 16 : ℂ))
    (hu : mode D a s 0 u = (1 / 4 : ℂ) • u + c • w)
    (hw : mode D a s 0 w = (1 / 4 : ℂ) • w + c • u) :
    projector D a s u = 0 := by
  apply projector_of_half_square
  calc
    mode D a s 0 (mode D a s 0 u) =
        (1 / 16 + c * c : ℂ) • u + (c / 2) • w := by
      rw [hu, map_add, map_smul, map_smul, hu, hw]
      module
    _ = (1 / 2 : ℂ) • mode D a s 0 u := by rw [hc, hu]; module

private theorem projector_neg_two (D : LatticeData) (a b : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (hp : bilinear D a b = -2) : projector D a s (E D b) = 0 := by
  have hab : bilinear D a (a+b) = 2 := by rw [bilinear_add_right, ha, hp]; norm_num
  have he : epsilon D a (a+b) = epsilon D a b := by
    rw [epsilon_add_right, epsilon_norm_four D a ha, one_mul]
  have hret : mode D a s 0 (E D (a+b)) = (1 / 4 : ℂ) • E D (a+b) +
      (s * epsilon D a b / 4) • E D b := by
    rw [zero_mode_orbit_sub D a (a+b) s hab, he,
      show a-(a+b) = -b by abel, E_neg]
  exact projector_two_block D a s (s * epsilon D a b / 4) (E D b) (E D (a+b))
    (phase_square D a b s hs) (zero_mode_orbit_add D a b s hp) hret

private theorem projector_distinct (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a b : Charge D) (ha : bilinear D a a = 4) (hb : bilinear D b b = 4)
    (s : ℂ) (hs : s ^ 2 = 1) (he : b ≠ a) (ho : b ≠ -a) :
    projector D a s (E D b) = 0 := by
  have hbnd := norm_four_inner_bounds D hD hroot a b ha hb he ho
  by_cases hm : bilinear D a b = -2
  · exact projector_neg_two D a b ha s hs hm
  by_cases hp : bilinear D a b = 2
  · have hpneg : bilinear D a (-b) = -2 := by rw [bilinear_neg_right, hp]
    simpa only [E_neg] using projector_neg_two D a (-b) ha s hs hpneg
  have hmid := zero_mode_orbit_middle D a b s (by omega) (by omega)
  have hc : bilinear D a b = -1 ∨ bilinear D a b = 0 ∨ bilinear D a b = 1 := by omega
  rcases hc with hc | hc | hc
  all_goals
    rw [hc] at hmid
    norm_num at hmid
    simp only [projector, LinearMap.smul_apply, Module.End.mul_apply,
      LinearMap.sub_apply, Module.End.one_apply, map_sub, map_smul, hmid, map_zero]
    module

private theorem projector_orbit_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a b : Charge D) (ha : bilinear D a a = 4) (hb : bilinear D b b = 4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    projector D a s (E D b) ∈ Submodule.span ℂ {vector D a s} := by
  by_cases he : b = a
  · subst b
    rw [projector_matching D a ha s hs]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  by_cases ho : b = -a
  · subst b
    rw [E_neg, projector_matching D a ha s hs]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rw [projector_distinct D hD hroot a b ha hb s hs he ho]
  exact Submodule.zero_mem _

private theorem projector_image (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (v : ↥(fixedSpace D ⊓
      (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ))) :
    projector D a s (v : Carrier D) ∈ Submodule.span ℂ {vector D a s} := by
  let S := fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)
  let W := Submodule.span ℂ {vector D a s}
  let F : S →ₗ[ℂ] (Carrier D ⧸ W) :=
    W.mkQ.comp ((projector D a s).comp S.subtype)
  have he : F = 0 := by
    apply (actualFixedEnergyTwoBasis D hD hroot).ext
    intro j
    change W.mkQ (projector D a s (actualFixedEnergyTwoBasis D hD hroot j : Carrier D)) = 0
    apply (Submodule.Quotient.mk_eq_zero W).mpr
    rcases j with p | q
    · rw [actual_basis_neutral_coe]
      rcases p with ⟨p, hp⟩
      obtain ⟨i, j, rfl⟩ := Multiset.card_eq_two.mp hp
      rw [pairOccupation_pair]
      have h : projector D a s (Q D i j) ∈ W := by
        rw [projector_Q D a ha s hs i j]
        exact W.smul_mem _ (Submodule.mem_span_singleton_self _)
      simpa only [Q, monomial_add_single, ← X_pow_eq_monomial, pow_one] using h
    · rw [actualFixedEnergyTwoBasis_charge_coe]
      exact projector_orbit_mem D hD hroot a (normFourOrbitRep D q).1 ha
        (normFourOrbitRep D q).2 s hs
  exact (Submodule.Quotient.mk_eq_zero W).mp (LinearMap.congr_fun he v)

private theorem Q_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2) (i j : Fin D.rank) :
    Q D i j ∈ fixedSpace D ⊓
      (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ) := by
  let p : Sym (Fin D.rank) 2 := ⟨{i, j}, by simp⟩
  have h := (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p)).2
  rw [actual_basis_neutral_coe] at h
  simpa only [p, pairOccupation_pair, Q, monomial_add_single,
    ← X_pow_eq_monomial, pow_one] using h

private theorem vector_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) :
    vector D a s ∈ fixedSpace D ⊓
      (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ) := by
  let S := fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)
  have hA : quadraticState D a ∈ S := by
    rw [quadratic_sum]
    apply S.sum_mem
    intro i hi
    apply S.smul_mem
    unfold R
    apply S.sum_mem
    intro j hj
    exact S.smul_mem _ (Q_mem D hD hroot j i)
  have hE : E D a ∈ S := by
    change E D a ∈ fixedSpace D ⊓
      (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)
    have hcanon := canonicalFixedEnergy_eq_fixedGrade D hD 2
    norm_num only [Int.cast_ofNat] at hcanon
    rw [hcanon]
    constructor
    · apply (mem_fixedSpace D _).mpr
      change thetaLinear D (E D a) = E D a
      simp [E, ground, add_comm]
    · have hb (b : Charge D) (hb : bilinear D b b = 4) : ground D b ∈ grade D 2 := by
        have h := (gradeTwoBasis D hD hroot (Sum.inr ⟨b, hb⟩)).2
        rw [gradeTwoBasis_charge_coe] at h
        exact h
      exact (grade D 2).add_mem (hb a ha) (hb (-a) (by rw [bilinear_neg_neg, ha]))
  exact S.add_mem (S.smul_mem _ hA) (S.smul_mem _ hE)

private theorem vector_ne_zero (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) : vector D a s ≠ 0 := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h, bilinear] at ha
  have haneg : a ≠ -a := by
    intro h
    apply ha0
    funext i
    change a i = 0
    have hi := congrArg (fun b : Charge D => b i) h
    change a i = -a i at hi
    omega
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  intro h
  have hc := congrArg (fun v : Carrier D => MvPolynomial.constantCoeff (v a)) h
  have hcoef : MvPolynomial.constantCoeff (vector D a s a) = s / 4 := by
    simp [vector, quadraticState, chargedState, ha0, haneg, Ne.symm ha0, Ne.symm haneg,
      Finsupp.single_apply]
  rw [hcoef] at hc
  exact (div_ne_zero hs0 (by norm_num : (4 : ℂ) ≠ 0)) (by simpa using hc)

/-- The actual norm-four vector is nonzero and spans the entire eigenvalue-two
intersection inside the literal theta-fixed canonical Sugawara energy-two space. -/
theorem actual_fixed_energy_two_eigenline (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    vector D a s ≠ 0 ∧
      (fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)) ⊓
        (mode D a s 0).eigenspace (2 : ℂ) = Submodule.span ℂ {vector D a s} := by
  refine ⟨vector_ne_zero D a ha s hs, le_antisymm ?_ ?_⟩
  · intro v hv
    have hL := Module.End.mem_eigenspace_iff.mp hv.2
    have hp : projector D a s v = v := by
      simp only [projector, LinearMap.smul_apply, Module.End.mul_apply,
        LinearMap.sub_apply, Module.End.one_apply, map_sub, map_smul, hL]
      module
    rw [← hp]
    exact projector_image D hD hroot a ha s hs ⟨v, hv.1⟩
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    refine ⟨vector_mem D hD hroot a ha s, Module.End.mem_eigenspace_iff.mpr ?_⟩
    exact (self_products D a ha s hs).2.1

#print axioms actual_fixed_energy_two_eigenline

end
end D5.S3.VertexAlgebra.Lattice.NormFourTwoEigenline
