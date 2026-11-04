/- GID: D5/S3/VertexAlgebra/Lattice/LeechLowSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechLowSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Golay Leech charge geometry and canonical Sugawara low spectrum. -/

import D5.S3.Arith.Lattices.Golay.RealLeech
import D5.S3.Arith.Lattices.Golay.LeechMinimalCount
import D5.S3.VertexAlgebra.Lattice.RootlessLowGrades

/-!
The classical Golay integer construction is used with its original admissibility
predicate and the real dot-over-eight pairing. Mathlib's injective submodule-image
equivalence supplies the actual integer coordinates, not a cardinality bijection.
The Leech shell classification and count are those of LeechMinimalCount; the
lattice Fock and Sugawara interpretation is as in Bakalov--Kac, section 4.1.
No orbifold, Monster action, or string-theoretic identification is asserted.
-/

set_option autoImplicit false

noncomputable section
namespace D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum

open D5.S3.Arith.Lattices.Golay
open GolayEncoder IntegerLeech
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents RootlessLowGrades

private theorem cast_injective : Function.Injective RealLeech.castLinear := by
  intro x y h
  funext i
  have hi : (x i : ℝ) = (y i : ℝ) := congrFun h i
  exact_mod_cast hi

private def integerRealEquiv :
    (integerLattice code all_ones_mem).toIntSubmodule ≃ₗ[ℤ] RealLeech.lattice :=
  Submodule.equivMapOfInjective RealLeech.castLinear cast_injective _

private def coordinates {D : LatticeData}
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) := e.trans integerRealEquiv.symm

private theorem coordinates_real {D : LatticeData}
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) (a : Charge D) :
    RealLeech.castLinear (coordinates e a) = (e a : RealLeech.Space) :=
  Submodule.map_equivMapOfInjective_symm_apply RealLeech.castLinear cast_injective _ (e a)

private theorem charge_square {D : LatticeData}
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice)
    (hpair : ∀ a c : Charge D, (bilinear D a c : ℝ) =
      RealLeech.pairing (e a : RealLeech.Space) (e c : RealLeech.Space))
    (a : Charge D) :
    (bilinear D a a : ℝ) = (squareSum (coordinates e a) : ℝ) / 8 := by
  rw [hpair, ← coordinates_real e a]
  simp [RealLeech.pairing, DirectLeechDuality.B, RealLeech.castLinear,
    squareSum, pow_two, dotProduct]
  ring

/-- The actual integral coordinates identify the literal charge shell with
all admissible norm-thirty-two integer vectors, without coordinate bounds. -/
def normFourEquiv (D : LatticeData)
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice)
    (hpair : ∀ a c : Charge D, (bilinear D a c : ℝ) =
      RealLeech.pairing (e a : RealLeech.Space) (e c : RealLeech.Space)) :
    NormFour D ≃ {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32} where
  toFun a := ⟨coordinates e a.1, (coordinates e a.1).property, by
    have h := charge_square e hpair a.1
    rw [a.property] at h
    have hs : (squareSum (coordinates e a.1) : ℝ) = 32 := by linarith
    exact_mod_cast hs⟩
  invFun x := ⟨(coordinates e).symm ⟨x.1, x.property.1⟩, by
    have h := charge_square e hpair ((coordinates e).symm ⟨x.1, x.property.1⟩)
    simp only [LinearEquiv.apply_symm_apply] at h
    have hn : (squareSum x.1 : ℝ) / 8 = 4 := by rw [x.property.2]; norm_num
    exact_mod_cast h.trans hn⟩
  left_inv a := Subtype.ext ((coordinates e).symm_apply_apply a.1)
  right_inv x := Subtype.ext
    (congrArg (fun z : (integerLattice code all_ones_mem).toIntSubmodule => (z : IntVector))
      ((coordinates e).apply_symm_apply ⟨x.1, x.property.1⟩))

private theorem no_roots {D : LatticeData}
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice)
    (hpair : ∀ a c : Charge D, (bilinear D a c : ℝ) =
      RealLeech.pairing (e a : RealLeech.Space) (e c : RealLeech.Space)) :
    ∀ a : Charge D, bilinear D a a ≠ 2 := by
  intro a ha
  have h := charge_square e hpair a
  rw [ha] at h
  have hx : (coordinates e a : IntVector) ≠ 0 := by
    intro hz
    norm_num [hz, squareSum] at h
  have hb := construction_lower_bound code doubly_even minimum_weight
    (coordinates e a).property hx
  have hb' : (32 : ℝ) ≤ (squareSum (coordinates e a) : ℝ) := by exact_mod_cast hb
  linarith

/-- The actual Golay real lattice supplies the even unimodular positive
rank-twenty-four charge data, the geometric shell equivalence and the literal
inverse-Gram Sugawara spectrum. No geometric or dimension premise is assumed. -/
theorem actual_leech_low_spectrum :
    ∃ (D : LatticeData) (e : Charge D ≃ₗ[ℤ] RealLeech.lattice),
      D.rank = 24 ∧ IsUnit D.G.det ∧
      (D.G.map (Int.castRingHom ℝ)).PosDef ∧
      (∀ a c : Charge D, (bilinear D a c : ℝ) =
        RealLeech.pairing (e a : RealLeech.Space) (e c : RealLeech.Space)) ∧
      (∀ a : Charge D, bilinear D a a ≠ 2) ∧
      ∃ s : NormFour D ≃
          {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32},
        (∀ a : NormFour D,
          RealLeech.castLinear (s a).1 = (e a.1 : RealLeech.Space)) ∧
        Finite (NormFour D) ∧ Nat.card (NormFour D) = 196560 ∧
        (∀ n : ℤ, FiniteDimensional ℂ
          ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (n : ℂ))) ∧
        Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 0) = 1 ∧
        Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 1) = 24 ∧
        Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 2) = 196884 := by
  obtain ⟨D, e, hrank, hunit, hpos, hpair⟩ :=
    RealLeech.exists_positive_even_unimodular_gram
  have hroot := no_roots e hpair
  let s := normFourEquiv D e hpair
  letI : Finite LeechMinimalCount.Sphere := LeechMinimalCount.shortest_vectors_finite
  have hf : Finite (NormFour D) := Finite.of_injective s s.injective
  have hc : Nat.card (NormFour D) = 196560 :=
    (Nat.card_congr s).trans LeechMinimalCount.shortest_vectors_card
  obtain ⟨hall, hzero, hone, htwo⟩ := actual_rootless_low_spectrum D hpos hroot
  refine ⟨D, e, hrank, hunit, hpos, hpair, hroot, s, ?_, hf, hc,
    hall, hzero, ?_, ?_⟩
  · exact fun a => coordinates_real e a.1
  · simpa only [hrank] using hone
  · norm_num [hrank, hc] at htwo ⊢
    exact htwo

#print axioms normFourEquiv
#print axioms actual_leech_low_spectrum

end D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
