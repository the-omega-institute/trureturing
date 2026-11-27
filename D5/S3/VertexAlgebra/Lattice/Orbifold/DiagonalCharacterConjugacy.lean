/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/DiagonalCharacterConjugacy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/DiagonalCharacterConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex charge characters give actual conformal lattice lift conjugacies. -/

import D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGround
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
Complex charge characters act by scalars on the actual lattice state carrier.
Charge homogeneity gives the mode law as in `CyclicIsometryLift`.
A character trivial on the fixed charges descends to the image of the charge
difference. Divisibility of the complex units extends it to the whole charge
group. The extended character conjugates lifts with matching fixed phases.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticePositiveEnergy LatticeFiniteNegativeGeneration
open LatticeSectorIntertwiner (inclusion inclusion_canonical canonical_ground_normalization)
open scoped VertexOperator

noncomputable section

open private ground_current_product current_field from
  D5.S3.VertexAlgebra.Lattice.IsometryLift
open private neutral_negative_single from
  D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

abbrev Character (D : LatticeData) := Multiplicative (Charge D) →* ℂˣ

local notation "ofAdd" => Multiplicative.ofAdd

private def complexUnitsDivisible : DivisibleBy (Additive ℂˣ) ℤ := by
  haveI : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj (by
    intro n hn a
    let u : ℂˣ := Additive.toMul a
    let root : ℂ := (u : ℂ) ^ ((n : ℂ)⁻¹)
    have hroot : root ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Units.ne_zero u))
    refine ⟨Additive.ofMul (Units.mk0 root hroot), ?_⟩
    change (Units.mk0 root hroot : ℂˣ) ^ n = u
    apply Units.ext
    exact Complex.cpow_nat_inv_pow (u : ℂ) hn)
  exact AddGroup.divisibleByIntOfDivisibleByNat _

/-- A character of an additive group is a quotient along an endomorphism
precisely when it is trivial on the fixed subgroup. -/
theorem exists_character_div_iff {A : Type*} [AddCommGroup A]
    (g : A →+ A) (χ : Multiplicative A →* ℂˣ) :
    (∃ η : Multiplicative A →* ℂˣ, ∀ a, χ (ofAdd a) = η (ofAdd (g a)) / η (ofAdd a)) ↔
      ∀ a, g a = a → χ (ofAdd a) = 1 := by
  constructor
  · rintro ⟨η, hη⟩ a ha
    rw [hη, ha, div_self']
  · intro hχ
    letI := complexUnitsDivisible
    let difference : A →+ A := g - AddMonoidHom.id A
    let χadd : A →+ Additive ℂˣ := χ.toAdditiveRight
    have hker : difference.rangeRestrict.ker ≤ χadd.ker := by
      intro a ha
      rw [AddMonoidHom.mem_ker] at ha ⊢
      have hzero := congrArg Subtype.val ha
      change g a - a = 0 at hzero
      exact hχ a (sub_eq_zero.mp hzero)
    let descended : difference.range →+ Additive ℂˣ :=
      difference.rangeRestrict.liftOfSurjective difference.rangeRestrict_surjective ⟨χadd, hker⟩
    have hBaer := Module.Baer.of_divisible (Additive ℂˣ)
    obtain ⟨ηadd, hext⟩ :=
      hBaer.extension_property_addMonoidHom difference.range.subtype Subtype.val_injective descended
    refine ⟨ηadd.toMultiplicativeLeft, fun a => ?_⟩
    have h := DFunLike.congr_fun hext (difference.rangeRestrict a)
    change ηadd (g a - a) = descended (difference.rangeRestrict a) at h
    rw [show descended (difference.rangeRestrict a) = χadd a by
      simp [descended], map_sub] at h
    exact h.symm

private def diagonalLinear (D : LatticeData) (phase : Charge D → ℂˣ) :
    Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun a => (phase a : ℂ) • Finsupp.lsingle a)

private theorem diagonalLinear_single (D : LatticeData) (phase : Charge D → ℂˣ)
    (a : Charge D) (p : Oscillator D) :
    diagonalLinear D phase (Finsupp.single a p) = (phase a : ℂ) • Finsupp.single a p := by
  simp [diagonalLinear]

/-- The charge diagonal on the actual lattice carrier, inverted by reciprocal scalars. -/
def diagonal (D : LatticeData) (χ : Character D) : Carrier D ≃ₗ[ℂ] Carrier D :=
  LinearEquiv.ofLinearMap
    (diagonalLinear D (fun a => χ (ofAdd a)))
    (diagonalLinear D (fun a => (χ (ofAdd a))⁻¹))
    (by
      apply Finsupp.lhom_ext
      intro a p
      simp [LinearMap.comp_apply, diagonalLinear_single, smul_smul])
    (by
      apply Finsupp.lhom_ext
      intro a p
      simp [LinearMap.comp_apply, diagonalLinear_single, smul_smul])

theorem diagonal_single (D : LatticeData) (χ : Character D)
    (a : Charge D) (p : Oscillator D) :
    diagonal D χ (Finsupp.single a p) = (χ (ofAdd a) : ℂ) • Finsupp.single a p :=
  diagonalLinear_single D _ a p

private theorem mode_smul (D : LatticeData) (u v : Carrier D) (n : ℤ) (c d : ℂ) :
    ((Y D (c • u))[[n]]) (d • v) = (c * d) • (((Y D u)[[n]]) v) := by
  rw [map_smul]
  simp only [VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply, map_smul, smul_smul]

/-- Preservation of every integer mode on arbitrary states of the actual lattice VOA. -/
theorem diagonal_modes (D : LatticeData) (χ : Character D)
    (u v : Carrier D) (n : ℤ) :
    diagonal D χ (((Y D u)[[n]]) v) =
      ((Y D (diagonal D χ u))[[n]]) (diagonal D χ v) := by
  let B := diagonal D χ
  let left : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun u => B (((Y D u)[[n]]) v)
      map_add' := by intro u w; simp
      map_smul' := by intro c u; simp }
  let right : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun u => ((Y D (B u))[[n]]) (B v)
      map_add' := by intro u w; simp
      map_smul' := by intro c u; simp }
  have h : left = right := by
    apply Finsupp.lhom_ext
    intro a p
    let l := B.toLinearMap.comp ((Y D (Finsupp.single a p))[[n]])
    let r := ((Y D (B (Finsupp.single a p)))[[n]]).comp B.toLinearMap
    have he : l = r := by
      apply Finsupp.lhom_ext
      intro b q
      change diagonal D χ (((Y D (Finsupp.single a p))[[n]]) (Finsupp.single b q)) =
        ((Y D (diagonal D χ (Finsupp.single a p)))[[n]]) (diagonal D χ (Finsupp.single b q))
      have hχ : (χ (ofAdd (a + b)) : ℂ) = (χ (ofAdd a) : ℂ) * (χ (ofAdd b) : ℂ) :=
        congrArg Units.val (χ.map_mul (ofAdd a) (ofAdd b))
      have hh := LatticeSectorIntertwiner.charge_homogeneity D a b p q n
      conv_lhs => rw [hh, diagonal_single, ← hh, hχ]
      rw [diagonal_single, diagonal_single, mode_smul]
    exact LinearMap.congr_fun he v
  exact LinearMap.congr_fun h u

theorem diagonal_neutral (D : LatticeData) (χ : Character D) (p : Oscillator D) :
    diagonal D χ (Finsupp.single 0 p) = Finsupp.single 0 p := by
  rw [diagonal_single]
  change ((χ 1 : ℂˣ) : ℂ) • Finsupp.single 0 p = _
  rw [map_one, Units.val_one, one_smul]

theorem diagonal_vacuum (D : LatticeData) (χ : Character D) :
    diagonal D χ (vacuum D) = vacuum D :=
  diagonal_neutral D χ 1

theorem diagonal_translation (D : LatticeData) (χ : Character D) (v : Carrier D) :
    diagonal D χ (translation D v) = translation D (diagonal D χ v) := by
  rw [LatticeActualVertexAlgebra.translation_as_mode, diagonal_modes, diagonal_vacuum,
    ← LatticeActualVertexAlgebra.translation_as_mode]

theorem diagonal_omega (D : LatticeData) (χ : Character D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    diagonal D χ (LatticeActualConformalState.omega D H) = LatticeActualConformalState.omega D H :=
  diagonal_neutral D χ _

private theorem diagonal_apply (D : LatticeData) (χ : Character D)
    (a : Charge D) (v : Carrier D) :
    diagonal D χ v a = (χ (ofAdd a) : ℂ) • v a := by
  classical
  let ev : Carrier D →ₗ[ℂ] Oscillator D := Finsupp.lapply a
  have he : ev.comp (diagonal D χ).toLinearMap = (χ (ofAdd a) : ℂ) • ev := by
    apply Finsupp.lhom_ext
    intro b p
    change (diagonal D χ (Finsupp.single b p)) a = (χ (ofAdd a) : ℂ) • Finsupp.single b p a
    rw [diagonal_single, Finsupp.smul_apply]
    by_cases h : b = a
    · subst b
      rfl
    · simp [Finsupp.single_eq_of_ne h.symm]
  exact LinearMap.congr_fun he v

/-- All actual homogeneous spaces are preserved, even without a Gram inverse. -/
theorem diagonal_mem_grade_iff (D : LatticeData) (χ : Character D)
    (n : ℤ) (v : Carrier D) : diagonal D χ v ∈ grade D n ↔ v ∈ grade D n := by
  simp only [mem_grade_iff, diagonal_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  constructor
  · intro h a ha
    exact (mul_eq_zero.mp (h a ha)).resolve_left (Units.ne_zero (χ (ofAdd a.1)))
  · intro h a ha
    rw [h a ha, mul_zero]

/-- For a lift carrying every charge sector to its image under `g`, the
source-side character twist is conjugate to the lift if the character is
trivial on fixed charges. The equation is `Dη ∘ U = (U ∘ Dχ) ∘ Dη`. -/
theorem conjugate_character_twist (D : LatticeData) (g : Charge D ≃+ Charge D)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (χ : Character D)
    (hU : ∀ (a : Charge D) (p : Oscillator D), ∃ q : Oscillator D,
      U (Finsupp.single a p) = Finsupp.single (g a) q)
    (hχ : ∀ a, g a = a → χ (ofAdd a) = 1) :
    ∃ η : Character D, U.trans (diagonal D η) =
      (diagonal D η).trans ((diagonal D χ).trans U) := by
  obtain ⟨η, hη⟩ := (exists_character_div_iff g.toAddMonoidHom χ).mpr hχ
  refine ⟨η, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  change diagonal D η (U (Finsupp.single a p)) =
    U (diagonal D χ (diagonal D η (Finsupp.single a p)))
  obtain ⟨q, hq⟩ := hU a p
  have ha : η (ofAdd (g a)) = η (ofAdd a) * χ (ofAdd a) :=
    (eq_div_iff_mul_eq''.mp (hη a)).symm
  calc
    _ = (η (ofAdd (g a)) : ℂ) • Finsupp.single (g a) q := by
      rw [hq, diagonal_single]
    _ = _ := by
      simp only [diagonal_single, map_smul, smul_smul, hq, ha, Units.val_mul]

#print axioms exists_character_div_iff
#print axioms diagonal
#print axioms diagonal_modes
#print axioms diagonal_vacuum
#print axioms diagonal_translation
#print axioms diagonal_omega
#print axioms diagonal_mem_grade_iff
#print axioms conjugate_character_twist

/-- The state-field intertwining law on the actual lattice carrier. -/
abbrev PreservesModes (D : LatticeData) (U : Carrier D ≃ₗ[ℂ] Carrier D) : Prop :=
  ∀ (u v : Carrier D) (n : ℤ),
    U (((Y D u)[[n]]) v) = ((Y D (U u))[[n]]) (U v)

private theorem preservesModes_trans (D : LatticeData) {U V : Carrier D ≃ₗ[ℂ] Carrier D}
    (hU : PreservesModes D U) (hV : PreservesModes D V) : PreservesModes D (U.trans V) := by
  intro u v n
  simp only [LinearEquiv.trans_apply, hU, hV]

private theorem preservesModes_symm (D : LatticeData) {U : Carrier D ≃ₗ[ℂ] Carrier D}
    (hU : PreservesModes D U) : PreservesModes D U.symm := by
  intro u v n
  apply U.injective
  rw [U.apply_symm_apply, hU, U.apply_symm_apply, U.apply_symm_apply]

abbrev ground (D : LatticeData) (a : Charge D) : Carrier D :=
  Finsupp.single a (1 : Oscillator D)

private theorem ground_ne_zero (D : LatticeData) (a : Charge D) : ground D a ≠ 0 := by
  classical
  simp

private theorem ground_mul (D : LatticeData) (a b : Charge D) :
    ((Y D (ground D a))[[-bilinear D a b - 1]]) (ground D b) =
      epsilon D a b • ground D (a + b) := by
  change ((Y D (inclusion D a 1))[[-bilinear D a b - 1]]) (inclusion D b 1) = _
  rw [← inclusion_canonical, canonical_ground_normalization, map_smul]
  rfl

private theorem epsilon_ne_zero (D : LatticeData) (a b : Charge D) : epsilon D a b ≠ 0 := by
  unfold epsilon paritySign
  split_ifs <;> simp

/-- The charged ground states determine every mode-preserving linear
equivalence. Opposite ground charges first give the neutral currents, whose
negative modes generate all oscillator monomials in each charge sector. -/
theorem eq_of_ground (D : LatticeData) {U V : Carrier D ≃ₗ[ℂ] Carrier D}
    (hU : PreservesModes D U) (hV : PreservesModes D V)
    (hGround : ∀ a : Charge D, U (ground D a) = V (ground D a)) : U = V := by
  classical
  let W := U.toLinearMap.eqLocus V.toLinearMap
  have hprod (u v : Carrier D) (hu : u ∈ W) (hv : v ∈ W) (n : ℤ) : mu D u n v ∈ W := by
    change U u = V u at hu
    change U v = V v at hv
    change U (((Y D u)[[n]]) v) = V (((Y D u)[[n]]) v)
    rw [hU, hV, hu, hv]
  have hcurrent (i : Fin D.rank) :
      Finsupp.single 0 (MvPolynomial.X (i, 0) : Oscillator D) ∈ W := by
    let a := unitCharge D i
    have h := hprod (ground D a) (ground D (-a)) (hGround a) (hGround (-a))
      (bilinear D a a - 2)
    rw [ground_current_product] at h
    have hs := W.smul_mem (epsilon D a (-a)) h
    simpa [smul_smul, LatticeActualGeneratorLocality.paritySign_square,
      epsilon, chargePolynomial, a, unitCharge, apply_ite, ite_smul] using hs
  have hsingle (a : Charge D) (p : Oscillator D) : Finsupp.single a p ∈ W := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      simpa [← Finsupp.single_smul, MvPolynomial.smul_eq_C_mul] using W.smul_mem c (hGround a)
    | add p q hp hq =>
      simpa only [Finsupp.single_add] using W.add_mem hp hq
    | mul_X p x hp =>
      have h := hprod _ _ (hcurrent x.1) hp (-(x.2 : ℤ) - 1)
      change ((Y D (Finsupp.single 0 (MvPolynomial.X (x.1, 0) : Oscillator D)))
        [[-(x.2 : ℤ) - 1]]) (Finsupp.single a p) ∈ W at h
      rw [current_field, neutral_negative_single] at h
      simpa only [Prod.mk.eta, mul_comm] using h
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  exact hsingle a p

private theorem ground_ratio_character (D : LatticeData) (W : Carrier D ≃ₗ[ℂ] Carrier D)
    (hW : PreservesModes D W) (ratio : Charge D → ℂˣ)
    (hRatio : ∀ a, W (ground D a) = (ratio a : ℂ) • ground D a) :
    ∃ χ : Character D, ∀ a, χ (ofAdd a) = ratio a := by
  have hmul (a b : Charge D) : ratio (a + b) = ratio a * ratio b := by
    have h := hW (ground D a) (ground D b) (-bilinear D a b - 1)
    simp only [ground_mul, map_smul, hRatio, mode_smul, smul_smul] at h
    have hs := (smul_left_injective ℂ (ground_ne_zero D (a + b))) h
    apply Units.ext
    change (ratio (a + b) : ℂ) = (ratio a : ℂ) * (ratio b : ℂ)
    apply mul_left_cancel₀ (epsilon_ne_zero D a b)
    exact hs.trans (by ring)
  exact ⟨MonoidHom.mk' (fun a => ratio (Multiplicative.toAdd a)) hmul, fun _ => rfl⟩

/-- Two mode-preserving lifts of the same charge action are conjugate by an
actual conformal diagonal when their charged ground phases agree at every
fixed charge. The oscillator action of each lift follows from its mode law
and its action on the charged ground states. -/
theorem conjugate_of_fixed_ground (D : LatticeData) (g : Charge D ≃+ Charge D)
    (U V : Carrier D ≃ₗ[ℂ] Carrier D) (phaseU phaseV : Charge D → ℂˣ)
    (hU : PreservesModes D U) (hV : PreservesModes D V)
    (hGroundU : ∀ a, U (ground D a) = (phaseU a : ℂ) • ground D (g a))
    (hGroundV : ∀ a, V (ground D a) = (phaseV a : ℂ) • ground D (g a))
    (hFixed : ∀ a, g a = a → phaseV a = phaseU a) :
    ∃ η : Character D, U.trans (diagonal D η) = (diagonal D η).trans V := by
  let ratio (a : Charge D) : ℂˣ := phaseV a / phaseU a
  have hRatio (a : Charge D) :
      (V.trans U.symm) (ground D a) = (ratio a : ℂ) • ground D a := by
    apply U.injective
    simp only [LinearEquiv.trans_apply, U.apply_symm_apply, map_smul, hGroundU, hGroundV,
      ratio, smul_smul, Units.val_div_eq_div_val, div_mul_cancel₀ _ (Units.ne_zero (phaseU a))]
  obtain ⟨χ, hχ⟩ := ground_ratio_character D (V.trans U.symm)
    (preservesModes_trans D hV (preservesModes_symm D hU)) ratio hRatio
  have hFixedχ (a : Charge D) (ha : g a = a) : χ (ofAdd a) = 1 := by
    rw [hχ a]
    change phaseV a / phaseU a = 1
    rw [hFixed a ha, div_self']
  obtain ⟨η, hη⟩ := (exists_character_div_iff g.toAddMonoidHom χ).mpr hFixedχ
  refine ⟨η, eq_of_ground D (preservesModes_trans D hU (diagonal_modes D η))
    (preservesModes_trans D (diagonal_modes D η) hV) fun a => ?_⟩
  have hPhase : η (ofAdd (g a)) * phaseU a = η (ofAdd a) * phaseV a := by
    have hd := (hχ a).symm.trans (hη a)
    change phaseV a / phaseU a = η (ofAdd (g a)) / η (ofAdd a) at hd
    exact (div_eq_div_iff_mul_eq_mul.mp hd).symm.trans (mul_comm _ _)
  simp only [LinearEquiv.trans_apply, hGroundU, diagonal_single, map_smul, hGroundV, smul_smul]
  rw [mul_comm (phaseU a : ℂ), ← Units.val_mul, hPhase, Units.val_mul]

#print axioms eq_of_ground
#print axioms conjugate_of_fixed_ground

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy
