/- GID: D5/S3/VertexAlgebra/Lattice/LeechPeirceDimension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechPeirceDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole ordinary fixed-energy-two one-sixteenth multiplicity for an actual Leech axis. -/

import D5.S3.VertexAlgebra.Lattice.NormFourPeirceInvolution
import D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
import D5.S3.Arith.Lattices.Golay.LeechAxisDistribution
import Batteries.Tactic.OpenPrivate

/-!
The complete ordinary fixed-energy-two basis and the actual charge character
identify the one-sixteenth eigenspace with the odd charge-orbit span. Each odd
orbit has exactly one representative pairing to one with the norm-four axis.
The actual Golay axis distribution then gives its dimension. The lattice and
norm-four Virasoro constructions retain the attributions of the imported
sources to Bakalov--Kac, Frenkel--Lepowsky--Meurman and Dong--Mason--Zhu.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeInvolution NormFourVirasoroVector RootlessLowGrades
open InvolutionRootlessLowGrades NormFourPeirceInvolution
open D5.S3.Arith.Lattices.Golay
open GolayEncoder IntegerLeech
open scoped BigOperators
attribute [local instance] Classical.propDecidable

open private E ground norm_four_inner_bounds zero_mode_orbit_middle actual_basis_neutral_coe
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private normFourNeg normFourOrbitSetoid normFourOrbitMk normFourOrbitMk_neg
  normFourOrbitMk_rep normFourOrbit_rep_cases normFourOrbit_finite
  from D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
open private chi_E from D5.S3.VertexAlgebra.Lattice.NormFourPeirceInvolution

private abbrev OrdinaryTwo (D : LatticeData) :=
  fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)

private abbrev OddOrbit (D : LatticeData) (a : Charge D) :=
  {q : NormFourOrbit D // Odd (bilinear D a (normFourOrbitRep D q).1)}

private theorem odd_pairing (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (b : NormFour D)
    (ho : Odd (bilinear D a b.1)) :
    bilinear D a b.1 = 1 ∨ bilinear D a b.1 = -1 := by
  have hn : b.1 ≠ a := by
    intro h
    rw [h, ha] at ho
    norm_num at ho
  have hm : b.1 ≠ -a := by
    intro h
    rw [h, bilinear_neg_right, ha] at ho
    norm_num at ho
  have hb := norm_four_inner_bounds D hD hroot a b.1 ha b.2 hn hm
  rcases ho with ⟨k, hk⟩
  omega

private def positiveOrbitMap (D : LatticeData) (a : Charge D)
    (b : {b : NormFour D // bilinear D a b.1 = 1}) : OddOrbit D a :=
  ⟨normFourOrbitMk D b.1, by
    rcases normFourOrbit_rep_cases D b.1 with h | h
    · rw [h, b.2]; norm_num
    · have hp := congrArg (fun c : NormFour D => bilinear D a c.1) h
      change bilinear D a (-(normFourOrbitRep D (normFourOrbitMk D b.1)).1) = bilinear D a b.1.1 at hp
      rw [bilinear_neg_right, b.2] at hp
      have : bilinear D a (normFourOrbitRep D (normFourOrbitMk D b.1)).1 = -1 := by omega
      rw [this]; norm_num⟩

private def positiveOrbitEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) :
    {b : NormFour D // bilinear D a b.1 = 1} ≃ OddOrbit D a :=
  Equiv.ofBijective (positiveOrbitMap D a) (by
    constructor
    · intro b c h
      have hq : normFourOrbitMk D b.1 = normFourOrbitMk D c.1 := congrArg Subtype.val h
      have hr : b.1 = c.1 ∨ normFourNeg D b.1 = c.1 := Quotient.exact hq
      rcases hr with hr | hr
      · exact Subtype.ext hr
      · have hp := congrArg (fun x : NormFour D => bilinear D a x.1) hr
        change bilinear D a (-b.1.1) = bilinear D a c.1.1 at hp
        rw [bilinear_neg_right, b.2, c.2] at hp
        norm_num at hp
    · intro q
      rcases odd_pairing D hD hroot a ha (normFourOrbitRep D q.1) q.2 with hp | hp
      · refine ⟨⟨normFourOrbitRep D q.1, hp⟩, ?_⟩
        apply Subtype.ext
        exact normFourOrbitMk_rep D q.1
      · refine ⟨⟨normFourNeg D (normFourOrbitRep D q.1), ?_⟩, ?_⟩
        · change bilinear D a (-(normFourOrbitRep D q.1).1) = 1
          rw [bilinear_neg_right, hp]; norm_num
        · apply Subtype.ext
          exact (normFourOrbitMk_neg D _).trans (normFourOrbitMk_rep D q.1))

private def oddVector (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (q : OddOrbit D a) : Carrier D :=
  actualFixedEnergyTwoBasis D hD hroot (Sum.inr q.1)

private theorem oddVector_eigen (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (q : OddOrbit D a) :
    mode D a 1 0 (oddVector D hD hroot a q) =
      (1 / 16 : ℂ) • oddVector D hD hroot a q := by
  change mode D a 1 0 (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q.1) : Carrier D) = _
  simp only [oddVector, actualFixedEnergyTwoBasis_charge_coe]
  change mode D a 1 0 (E D (normFourOrbitRep D q.1).1) =
    (1 / 16 : ℂ) • E D (normFourOrbitRep D q.1).1
  rcases odd_pairing D hD hroot a ha (normFourOrbitRep D q.1) q.2 with hp | hp
  all_goals
    have h := zero_mode_orbit_middle D a (normFourOrbitRep D q.1).1 1
      (by omega) (by omega)
    rw [hp] at h
    norm_num at h
    exact h

private theorem oddSpan_eq (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) :
    Submodule.span ℂ (Set.range (oddVector D hD hroot a)) =
      OrdinaryTwo D ⊓ (mode D a 1 0).eigenspace (1 / 16 : ℂ) := by
  let b := actualFixedEnergyTwoBasis D hD hroot
  let W := Submodule.span ℂ (Set.range (oddVector D hD hroot a))
  let P : OrdinaryTwo D →ₗ[ℂ] Carrier D :=
    (1 / 2 : ℂ) • ((OrdinaryTwo D).subtype -
      (chiLinear D a).comp (OrdinaryTwo D).subtype)
  have hb (j : FixedTwoIndex D) : P (b j) ∈ W := by
    rcases j with p | q
    · have he : chiLinear D a (b (Sum.inl p) : Carrier D) = (b (Sum.inl p) : Carrier D) := by
        change chiLinear D a (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p) : Carrier D) = _
        rw [actual_basis_neutral_coe]
        simp [chi_single, phase, paritySign, bilinear]
      change (1 / 2 : ℂ) • ((b (Sum.inl p) : Carrier D) - chiLinear D a (b (Sum.inl p))) ∈ W
      rw [he, sub_self, smul_zero]
      exact W.zero_mem
    · have he : chiLinear D a (b (Sum.inr q) : Carrier D) =
          phase D a (normFourOrbitRep D q).1 • (b (Sum.inr q) : Carrier D) := by
        change chiLinear D a (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q) : Carrier D) = _
        rw [actualFixedEnergyTwoBasis_charge_coe]
        exact chi_E D a (normFourOrbitRep D q).1
      change (1 / 2 : ℂ) • ((b (Sum.inr q) : Carrier D) - chiLinear D a (b (Sum.inr q))) ∈ W
      rw [he]
      by_cases ho : Odd (bilinear D a (normFourOrbitRep D q).1)
      · have hp : phase D a (normFourOrbitRep D q).1 = -1 := by
          simp [phase, paritySign, Int.not_even_iff_odd.mpr ho]
        rw [hp]
        have hv : (1 / 2 : ℂ) • ((b (Sum.inr q) : Carrier D) - (-1 : ℂ) • b (Sum.inr q)) =
            (b (Sum.inr q) : Carrier D) := by module
        rw [hv]
        exact Submodule.subset_span (Set.mem_range_self (⟨q, ho⟩ : OddOrbit D a))
      · have hp : phase D a (normFourOrbitRep D q).1 = 1 := by
          simp [phase, paritySign, Int.not_odd_iff_even.mp ho]
        rw [hp, one_smul, sub_self, smul_zero]
        exact W.zero_mem
  have hP (v : OrdinaryTwo D) : P v ∈ W := by
    haveI : Finite (NormFourOrbit D) := normFourOrbit_finite D hD
    haveI : Fintype (FixedTwoIndex D) := Fintype.ofFinite _
    rw [← b.sum_repr v, map_sum]
    exact W.sum_mem (fun j _ => by rw [map_smul]; exact W.smul_mem _ (hb j))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact ⟨(b (Sum.inr q.1)).property,
      Module.End.mem_eigenspace_iff.mpr (oddVector_eigen D hD hroot a ha q)⟩
  · intro v hv
    have hL := Module.End.mem_eigenspace_iff.mp hv.2
    have hs := actual_fixed_energy_two_spectral_sign D hD hroot a ha 1 (by norm_num)
      (⟨v, hv.1⟩ : OrdinaryTwo D)
    have hc : chiLinear D a v = -v := by
      change chiLinear D a v = _ at hs
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, map_smul, hL] at hs
      convert hs using 1; module
    have he : P ⟨v, hv.1⟩ = v := by
      change (1 / 2 : ℂ) • (v - chiLinear D a v) = v
      rw [hc]; module
    rw [← he]
    exact hP ⟨v, hv.1⟩

/-- On the complete literal ordinary fixed energy-two space, the dimension of
its actual norm-four one-sixteenth eigenspace equals the positive pairing-one
shell fiber. Completeness follows from the actual spectral-sign identity. -/
theorem actual_one_sixteenth_finrank (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) :
    Module.finrank ℂ ↥((fixedSpace D ⊓
      (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)) ⊓
      (mode D a 1 0).eigenspace (1 / 16 : ℂ)) =
      Nat.card {b : NormFour D // bilinear D a b.1 = 1} := by
  let b := actualFixedEnergyTwoBasis D hD hroot
  have hli : LinearIndependent ℂ (oddVector D hD hroot a) := by
    exact (b.linearIndependent.map' (OrdinaryTwo D).subtype
      (Submodule.ker_subtype _)).comp (fun q : OddOrbit D a => Sum.inr q.1)
        (fun x y h => Subtype.ext (Sum.inr.inj h))
  rw [← oddSpan_eq D hD hroot a ha]
  exact (Module.finrank_eq_nat_card_basis (Module.Basis.span hli)).trans
    (Nat.card_congr (positiveOrbitEquiv D hD hroot a ha).symm)

private def axisPoint : LeechMinimalCount.Sphere :=
  LeechMinimalCount.sphereEquiv (.inl
    ⟨⟨{0, 1}, by decide +kernel⟩, fun _ => 0⟩)

private theorem axisPoint_raw : axisPoint.1 =
    Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4 := by
  funext i
  change LeechMinimalCount.zeroVector
    ⟨⟨{0, 1}, by decide +kernel⟩, fun _ => 0⟩ i = _
  by_cases hi : i = 0
  · subst i; simp [LeechMinimalCount.zeroVector, LeechSignedSupport.signed]
  by_cases hj : i = 1
  · subst i; simp [LeechMinimalCount.zeroVector, LeechSignedSupport.signed]
  simp [LeechMinimalCount.zeroVector, LeechSignedSupport.signed, hi, hj]

private theorem shell_pairing (D : LatticeData)
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice)
    (hp : ∀ b c : Charge D, (bilinear D b c : ℝ) =
      RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space))
    (s : NormFour D ≃ LeechMinimalCount.Sphere)
    (hs : ∀ b : NormFour D, RealLeech.castLinear (s b).1 = (e b.1 : RealLeech.Space))
    (b c : NormFour D) :
    8 * bilinear D b.1 c.1 = dotProduct (s b).1 (s c).1 := by
  have h := hp b.1 c.1
  rw [← hs b, ← hs c] at h
  have he : (bilinear D b.1 c.1 : ℝ) =
      ((dotProduct (s b).1 (s c).1 : ℤ) : ℝ) / 8 := by
    simpa [RealLeech.pairing, DirectLeechDuality.B, RealLeech.castLinear,
      dotProduct, Int.cast_sum, Int.cast_mul, div_eq_mul_inv, mul_comm] using h
  have hh : (8 : ℝ) * (bilinear D b.1 c.1 : ℝ) =
      ((dotProduct (s b).1 (s c).1 : ℤ) : ℝ) := by linarith
  exact_mod_cast hh

private def axisFiberEquiv (D : LatticeData)
    (e : Charge D ≃ₗ[ℤ] RealLeech.lattice)
    (hp : ∀ b c : Charge D, (bilinear D b c : ℝ) =
      RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space))
    (s : NormFour D ≃ LeechMinimalCount.Sphere)
    (hs : ∀ b : NormFour D, RealLeech.castLinear (s b).1 = (e b.1 : RealLeech.Space)) :
    {b : NormFour D // bilinear D (s.symm axisPoint).1 b.1 = 1} ≃
    {x : Fin 24 → ℤ // Admissible code x ∧ squareSum x = 32 ∧
      dotProduct (Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4) x = 8*(1 : ℤ)} where
  toFun b := ⟨(s b.1).1, (s b.1).2.1, (s b.1).2.2, by
    have h := shell_pairing D e hp s hs (s.symm axisPoint) b.1
    rw [s.apply_symm_apply, axisPoint_raw, b.2] at h
    exact h.symm⟩
  invFun x := ⟨s.symm ⟨x.1, x.2.1, x.2.2.1⟩, by
    have h := shell_pairing D e hp s hs (s.symm axisPoint)
      (s.symm ⟨x.1, x.2.1, x.2.2.1⟩)
    rw [s.apply_symm_apply, s.apply_symm_apply, axisPoint_raw] at h
    have hx := x.2.2.2
    dsimp only at h
    omega⟩
  left_inv b := Subtype.ext (s.symm_apply_apply b.1)
  right_inv x := by
    apply Subtype.ext
    change (s (s.symm ⟨x.1, x.2.1, x.2.2.1⟩)).1 = x.1
    exact congrArg (fun z : LeechMinimalCount.Sphere => z.1)
      (s.apply_symm_apply ⟨x.1, x.2.1, x.2.2.1⟩)

/-- One actual Golay Leech norm-four axis, with raw coordinates (4,4,0^22)
and the literal dot-over-eight real pairing, has a 47104-dimensional
one-sixteenth eigenspace on the complete ordinary theta-fixed canonical
Sugawara energy-two space. -/
theorem actual_leech_one_sixteenth_dimension :
    ∃ (D : LatticeData) (e : Charge D ≃ₗ[ℤ] RealLeech.lattice) (a : Charge D),
      D.rank = 24 ∧ IsUnit D.G.det ∧
      (D.G.map (Int.castRingHom ℝ)).PosDef ∧
      (∀ b c : Charge D, (bilinear D b c : ℝ) =
        RealLeech.pairing (e b : RealLeech.Space) (e c : RealLeech.Space)) ∧
      (∀ b : Charge D, bilinear D b b ≠ 2) ∧
      (e a : RealLeech.Space) = RealLeech.castLinear
        (Pi.single (0 : Fin 24) 4 + Pi.single (1 : Fin 24) 4) ∧
      bilinear D a a = 4 ∧
      Module.finrank ℂ ↥((fixedSpace D ⊓
        (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)) ⊓
        (mode D a 1 0).eigenspace (1 / 16 : ℂ)) = 47104 := by
  obtain ⟨D, e, hrank, hunit, hpos, hpair, hroot, s, hs, _⟩ :=
    LeechLowSpectrum.actual_leech_low_spectrum
  let a : NormFour D := s.symm axisPoint
  refine ⟨D, e, a.1, hrank, hunit, hpos, hpair, hroot, ?_, a.2, ?_⟩
  · rw [← hs a]
    change RealLeech.castLinear (s (s.symm axisPoint)).1 = _
    rw [s.apply_symm_apply, axisPoint_raw]
  · rw [actual_one_sixteenth_finrank D hpos hroot a.1 a.2,
      Nat.card_congr (axisFiberEquiv D e hpair s hs)]
    have hc := (LeechAxisDistribution.axis_distribution 0 1 (by decide +kernel) 1).2
    convert hc using 1 <;> norm_num

#print axioms actual_one_sixteenth_finrank
#print axioms actual_leech_one_sixteenth_dimension

end D5.S3.VertexAlgebra.Lattice.LeechPeirceDimension
