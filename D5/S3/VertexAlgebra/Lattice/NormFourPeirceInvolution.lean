/- GID: D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual charge-character involution and full fixed-energy-two spectral sign. -/

import D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import Batteries.Tactic.OpenPrivate

/-!
The charge character acts on the production finite-support carrier and leaves
oscillator polynomials unchanged. All-mode covariance reuses the actual
charge_homogeneity theorem, rather than postulating a graded vertex algebra.
The spectral polynomial uses the complete actual fixed-energy-two basis and
the actual norm-four actions. The lattice construction and norm-four vector
retain Bakalov--Kac, Frenkel--Lepowsky--Meurman and Dong--Mason--Zhu attribution
as recorded in the imported sources; imported proofs retain their licenses.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourPeirceInvolution
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction LatticeActualVertexAlgebra
open LatticeActualProductKernel LatticeActualGeneratorLocality
open LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeSugawaraVirasoro LatticeInvolution NormFourVirasoroVector
open RootlessLowGrades InvolutionRootlessLowGrades MvPolynomial
open scoped BigOperators VertexOperator Classical
noncomputable section

open private Q ground E E_neg Gi R zero_mode_Q zero_mode_R zero_mode_A zero_mode_E
  zero_mode_orbit_middle zero_mode_orbit_add zero_mode_orbit_sub
  phase_square epsilon_norm_four norm_four_inner_bounds actual_basis_neutral_coe
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private pairOccupation_pair from D5.S3.VertexAlgebra.Lattice.RootlessLowGrades

/-- The integral pairing character, independent of oscillator coordinates. -/
def phase (D : LatticeData) (a b : Charge D) : ℂ := paritySign (bilinear D a b)

private theorem phase_add (D : LatticeData) (a b c : Charge D) :
    phase D a (b+c) = phase D a b * phase D a c := by
  simp only [phase, bilinear_add_right, paritySign_add]

@[simp] private theorem phase_neg (D : LatticeData) (a b : Charge D) :
    phase D a (-b) = phase D a b := by
  simp [phase, bilinear_neg_right, paritySign, even_neg]

@[simp] private theorem phase_zero (D : LatticeData) (a : Charge D) :
    phase D a 0 = 1 := by simp [phase, bilinear, paritySign]

/-- Scalar multiplication on each actual charge sector. -/
def chiLinear (D : LatticeData) (a : Charge D) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun b => phase D a b • Finsupp.lsingle b)

@[simp] theorem chi_single (D : LatticeData) (a b : Charge D) (p : Oscillator D) :
    chiLinear D a (Finsupp.single b p) = phase D a b • Finsupp.single b p := by
  simp [chiLinear, Finsupp.lsum_single]

/-- Involutive includes the identity character and rank zero. -/
theorem chi_involutive (D : LatticeData) (a : Charge D) :
    Function.Involutive (chiLinear D a) := by
  have h : (chiLinear D a).comp (chiLinear D a) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro b p
    simp [LinearMap.comp_apply, smul_smul, phase, paritySign_square]
  intro v
  exact LinearMap.congr_fun h v

/-- The explicit linear equivalence on the full production carrier. -/
def chi (D : LatticeData) (a : Charge D) : Carrier D ≃ₗ[ℂ] Carrier D :=
  LinearEquiv.ofInvolutive (chiLinear D a) (chi_involutive D a)

@[simp] theorem chi_vacuum (D : LatticeData) (a : Charge D) :
    chi D a (vacuum D) = vacuum D := by simp [chi, vacuum]

/-- Every production mode is preserved, for arbitrary states and integer modes.
The only charge-covariance input is the existing actual charge_homogeneity. -/
theorem stateField_chi (D : LatticeData) (a : Charge D)
    (u v : Carrier D) (n : ℤ) :
    chi D a (((Y D u)[[n]]) v) = ((Y D (chi D a u))[[n]]) (chi D a v) := by
  let left : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun u => chiLinear D a (((Y D u)[[n]]) v)
      map_add' := by intro u w; simp
      map_smul' := by intro c u; simp }
  let right : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun u => ((Y D (chiLinear D a u))[[n]]) (chiLinear D a v)
      map_add' := by intro u w; simp
      map_smul' := by intro c u; simp }
  have h : left = right := by
    apply Finsupp.lhom_ext
    intro b p
    let l : Carrier D →ₗ[ℂ] Carrier D :=
      (chiLinear D a).comp ((Y D (Finsupp.single b p))[[n]])
    let r : Carrier D →ₗ[ℂ] Carrier D :=
      ((Y D (chiLinear D a (Finsupp.single b p)))[[n]]).comp (chiLinear D a)
    have he : l = r := by
      apply Finsupp.lhom_ext
      intro c q
      change chiLinear D a (((Y D (Finsupp.single b p))[[n]]) (Finsupp.single c q)) = _
      have hh := LatticeSectorIntertwiner.charge_homogeneity D b c p q n
      rw [hh, chi_single]
      change _ = ((Y D (chiLinear D a (Finsupp.single b p)))[[n]])
        (chiLinear D a (Finsupp.single c q))
      rw [chi_single, chi_single, map_smul]
      simp only [VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply, map_smul]
      rw [smul_smul, ← phase_add]
      simpa only [VertexOperator.ncoeff, LinearMap.smul_apply, add_comm] using
        congrArg (fun w : Carrier D => phase D a (b+c) • w) hh.symm
    exact LinearMap.congr_fun he v
  exact LinearMap.congr_fun h u

/-- The sign polynomial in the actual norm-four Virasoro zero mode. -/
def spectralSign (D : LatticeData) (a : Charge D) (s : ℂ) :
    Module.End ℂ (Carrier D) :=
  let L := mode D a s 0
  1 - (8192 / 217 : ℂ) • (L * (L - (1 / 2 : ℂ) • 1) * (L - (2 : ℂ) • 1))

private def cubic (D : LatticeData) (a : Charge D) (s : ℂ) :
    Module.End ℂ (Carrier D) :=
  let L := mode D a s 0
  L * (L - (1 / 2 : ℂ) • 1) * (L - (2 : ℂ) • 1)

private theorem sign_of_cubic (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D) (h : cubic D a s v = 0) : spectralSign D a s v = v := by
  change v - (8192 / 217 : ℂ) • cubic D a s v = v
  rw [h, smul_zero, sub_zero]

private theorem cubic_Q (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (i j : Fin D.rank) :
    cubic D a s (Q D i j) = 0 := by
  simp only [cubic, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  simp only [zero_mode_Q, map_add, map_smul,
    zero_mode_R D a ha, zero_mode_A D a ha, zero_mode_E D a ha]
  have hs3 : s ^ 3 = s := by calc
    s ^ 3 = s ^ 2 * s := by ring
    _ = s := by rw [hs, one_mul]
  match_scalars <;> ring_nf <;> simp only [hs, hs3] <;> ring

private theorem cubic_matching (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    cubic D a s (E D a) = 0 := by
  simp only [cubic, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  simp only [zero_mode_E D a ha, zero_mode_A D a ha, map_add, map_smul]
  have hs3 : s ^ 3 = s := by calc
    s ^ 3 = s ^ 2 * s := by ring
    _ = s := by rw [hs, one_mul]
  match_scalars <;> ring_nf <;> simp only [hs, hs3] <;> ring

private theorem cubic_of_half_square (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D) (h : mode D a s 0 (mode D a s 0 v) =
      (1 / 2 : ℂ) • mode D a s 0 v) : cubic D a s v = 0 := by
  simp only [cubic, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  rw [h, map_smul, h]
  module

private theorem cubic_two_block (D : LatticeData) (a : Charge D) (s c : ℂ)
    (u w : Carrier D) (hc : c * c = (1 / 16 : ℂ))
    (hu : mode D a s 0 u = (1 / 4 : ℂ) • u + c • w)
    (hw : mode D a s 0 w = (1 / 4 : ℂ) • w + c • u) : cubic D a s u = 0 := by
  apply cubic_of_half_square
  calc
    mode D a s 0 (mode D a s 0 u) =
        (1 / 16 + c * c : ℂ) • u + (c / 2) • w := by
      rw [hu, map_add, map_smul, map_smul, hu, hw]
      module
    _ = (1 / 2 : ℂ) • mode D a s 0 u := by rw [hc, hu]; module

private theorem cubic_neg_two (D : LatticeData) (a b : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (hp : bilinear D a b = -2) : cubic D a s (E D b) = 0 := by
  have hab : bilinear D a (a+b) = 2 := by rw [bilinear_add_right, ha, hp]; norm_num
  have he : epsilon D a (a+b) = epsilon D a b := by
    rw [epsilon_add_right, epsilon_norm_four D a ha, one_mul]
  have hret : mode D a s 0 (E D (a+b)) = (1 / 4 : ℂ) • E D (a+b) +
      (s * epsilon D a b / 4) • E D b := by
    rw [zero_mode_orbit_sub D a (a+b) s hab, he,
      show a-(a+b) = -b by abel, E_neg]
  exact cubic_two_block D a s (s * epsilon D a b / 4) (E D b) (E D (a+b))
    (phase_square D a b s hs) (zero_mode_orbit_add D a b s hp) hret

private theorem chi_E (D : LatticeData) (a b : Charge D) :
    chiLinear D a (E D b) = phase D a b • E D b := by
  simp only [E, ground, map_add, chi_single, phase_neg, smul_add]

private theorem sign_Q (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (i j : Fin D.rank) :
    chiLinear D a (Q D i j) = spectralSign D a s (Q D i j) := by
  rw [sign_of_cubic D a s _ (cubic_Q D a ha s hs i j)]
  simp [Q]

private theorem sign_matching (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    chiLinear D a (E D a) = spectralSign D a s (E D a) := by
  rw [sign_of_cubic D a s _ (cubic_matching D a ha s hs), chi_E]
  norm_num [phase, ha, paritySign]

private theorem sign_neg_two (D : LatticeData) (a b : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (hp : bilinear D a b = -2) :
    chiLinear D a (E D b) = spectralSign D a s (E D b) := by
  rw [sign_of_cubic D a s _ (cubic_neg_two D a b ha s hs hp), chi_E]
  norm_num [phase, hp, paritySign]

private theorem sign_middle (D : LatticeData) (a b : Charge D) (s : ℂ)
    (hlo : -2 < bilinear D a b) (hhi : bilinear D a b < 2) :
    chiLinear D a (E D b) = spectralSign D a s (E D b) := by
  have hmid := zero_mode_orbit_middle D a b s hlo hhi
  have hp : bilinear D a b = -1 ∨ bilinear D a b = 0 ∨ bilinear D a b = 1 := by omega
  rcases hp with hp | hp | hp
  all_goals
    have he : mode D a s 0 (E D b) =
        ((bilinear D a b : ℂ) ^ 2 / 16) • E D b := hmid
    rw [hp] at he
    norm_num at he
    rw [chi_E]
    norm_num [phase, hp, paritySign]
    simp only [spectralSign, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, he, map_zero]
    module

private theorem sign_orbit (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a b : Charge D) (ha : bilinear D a a = 4) (hb : bilinear D b b = 4)
    (s : ℂ) (hs : s ^ 2 = 1) :
    chiLinear D a (E D b) = spectralSign D a s (E D b) := by
  by_cases he : b = a
  · subst b; exact sign_matching D a ha s hs
  by_cases ho : b = -a
  · subst b; rw [E_neg]; exact sign_matching D a ha s hs
  have hbnd := norm_four_inner_bounds D hD hroot a b ha hb he ho
  by_cases hm : bilinear D a b = -2
  · exact sign_neg_two D a b ha s hs hm
  by_cases hp : bilinear D a b = 2
  · have hn : bilinear D a (-b) = -2 := by rw [bilinear_neg_right, hp]
    simpa only [E_neg] using sign_neg_two D a (-b) ha s hs hn
  exact sign_middle D a b s (by omega) (by omega)

/-- The explicit all-mode involution equals the Peirce spectral sign on EVERY
vector of the literal theta-fixed canonical Sugawara energy-two space. -/
theorem actual_fixed_energy_two_spectral_sign (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ c : Charge D, bilinear D c c ≠ 2)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (v : ↥(fixedSpace D ⊓
      (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ))) :
    chi D a (v : Carrier D) =
      (1 - (8192 / 217 : ℂ) •
        (mode D a s 0 * (mode D a s 0 - (1 / 2 : ℂ) • 1) *
          (mode D a s 0 - (2 : ℂ) • 1))) (v : Carrier D) := by
  let S := fixedSpace D ⊓ (sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (2 : ℂ)
  let F : S →ₗ[ℂ] Carrier D := (chiLinear D a).comp S.subtype
  let G : S →ₗ[ℂ] Carrier D := (spectralSign D a s).comp S.subtype
  have he : F = G := by
    apply (actualFixedEnergyTwoBasis D hD hroot).ext
    intro j
    rcases j with p | q
    · change chiLinear D a (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p) : Carrier D) =
        spectralSign D a s (actualFixedEnergyTwoBasis D hD hroot (Sum.inl p) : Carrier D)
      rw [actual_basis_neutral_coe]
      rcases p with ⟨p, hp⟩
      obtain ⟨i, j, rfl⟩ := Multiset.card_eq_two.mp hp
      rw [pairOccupation_pair]
      simpa only [Q, monomial_add_single, ← X_pow_eq_monomial, pow_one] using
        sign_Q D a ha s hs i j
    · change chiLinear D a (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q) : Carrier D) =
        spectralSign D a s (actualFixedEnergyTwoBasis D hD hroot (Sum.inr q) : Carrier D)
      rw [actualFixedEnergyTwoBasis_charge_coe]
      exact sign_orbit D hD hroot a (normFourOrbitRep D q).1 ha
        (normFourOrbitRep D q).2 s hs
  exact LinearMap.congr_fun he v

#print axioms chi_involutive
#print axioms chi_vacuum
#print axioms stateField_chi
#print axioms actual_fixed_energy_two_spectral_sign

end
end D5.S3.VertexAlgebra.Lattice.NormFourPeirceInvolution
