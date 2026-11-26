import D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft
import D5.S3.VertexAlgebra.LatticeActualConformalState
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! The character extension and conjugacy of standard lifts on the actual lattice carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.StandardLiftCharacterConjugacy

open CategoryTheory
open LatticeGeneratingFieldLocality (Charge LatticeData Carrier Oscillator)
open LatticeAllStateField (vacuum)
open LatticeActualConformalState (omega)
open PhaseCharacterDraft (PreservesModes diagonal diagonal_single diagonal_preserves
  ground_phase_classification)
open private preserving_trans preserving_symm from
  D5.S3.VertexAlgebra.Lattice.PhaseCharacterDraft

noncomputable section

section Characters

variable {L : Type} [AddCommGroup L]

/-- The difference homomorphism whose image is `(1 − g)L`. -/
def oneSub (g : L ≃+ L) : L →+ L where
  toFun a := a - g a
  map_zero' := by simp only [map_zero, sub_self]
  map_add' a b := by rw [map_add, add_sub_add_comm]

theorem oneSub_apply (g : L ≃+ L) (a : L) : oneSub g a = a - g a := rfl

/-- A character trivial on the fixed lattice descends along `1 − g` to its image.
The additive type tag records multiplication in the group of complex units. -/
theorem exists_character_on_range (g : L ≃+ L) (chi : L →+ Additive ℂˣ)
    (hchi : ∀ a, g a = a → chi a = 0) :
    ∃ psi : (oneSub g).range →+ Additive ℂˣ,
      ∀ a, psi ((oneSub g).rangeRestrict a) = chi a := by
  let f := (oneSub g).rangeRestrict
  have hker : f.ker ≤ chi.ker := by
    intro a ha
    have h : f a = 0 := AddMonoidHom.mem_ker.mp ha
    have hd : a - g a = 0 := congrArg (fun x : (oneSub g).range => (x : L)) h
    exact AddMonoidHom.mem_ker.mpr (hchi a (sub_eq_zero.mp hd).symm)
  let psi := f.liftOfSurjective (oneSub g).rangeRestrict_surjective ⟨chi, hker⟩
  have hpsi : psi.comp f = chi := AddMonoidHom.liftOfRightInverse_comp ..
  exact ⟨psi, fun a => DFunLike.congr_fun hpsi a⟩

private theorem complexUnits_nsmul_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun u : Additive ℂˣ => n • u) := by
  intro u
  let z := (u.toMul : ℂ) ^ ((n : ℂ)⁻¹)
  have hz : z ^ n = (u.toMul : ℂ) := Complex.cpow_nat_inv_pow _ hn
  have hne : z ≠ 0 := by
    intro h
    rw [h, zero_pow hn] at hz
    exact u.toMul.ne_zero hz.symm
  refine ⟨Additive.ofMul (Units.mk0 z hne), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  simpa only [toMul_nsmul, toMul_ofMul,
    Units.val_pow_eq_pow_val, Units.val_mk0] using hz

/-- Every complex unit character on a subgroup extends across its inclusion. -/
theorem exists_character_extension (H : AddSubgroup L) (psi : H →+ Additive ℂˣ) :
    ∃ delta : L →+ Additive ℂˣ, ∀ x : H, delta (x : L) = psi x := by
  let : DivisibleBy (Additive ℂˣ) ℕ :=
    divisibleByOfSMulRightSurj _ _ complexUnits_nsmul_surjective
  let : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  let : Injective (AddCommGrpCat.of (Additive ℂˣ)) := AddCommGrpCat.injective_of_divisible _
  let i := AddCommGrpCat.ofHom H.subtype
  let : Mono i := ConcreteCategory.mono_of_injective i Subtype.val_injective
  obtain ⟨d, hd⟩ := Injective.factors (AddCommGrpCat.ofHom psi) i
  refine ⟨d.hom, fun x => ?_⟩
  exact ConcreteCategory.congr_hom hd x

/-- In multiplicative notation this says `chi(a) = delta(a − g a)`. -/
theorem exists_character_coboundary (g : L ≃+ L) (chi : L →+ Additive ℂˣ)
    (hchi : ∀ a, g a = a → chi a = 0) :
    ∃ delta : L →+ Additive ℂˣ, ∀ a, chi a = delta (a - g a) := by
  obtain ⟨psi, hpsi⟩ := exists_character_on_range g chi hchi
  obtain ⟨delta, hdelta⟩ := exists_character_extension (oneSub g).range psi
  exact ⟨delta, fun a => ((hdelta ((oneSub g).rangeRestrict a)).trans (hpsi a)).symm⟩

end Characters

/-- A standard monomial lift acts with phase one on every fixed ground charge. -/
def IsStandardLift (D : LatticeData) (g : Charge D ≃+ Charge D)
    (U : Carrier D ≃ₗ[ℂ] Carrier D) (theta : Charge D → ℂˣ) : Prop :=
  PreservesModes D U ∧
    (∀ a, U (Finsupp.single a 1) = (theta a : ℂ) • Finsupp.single (g a) 1) ∧
    ∀ a, g a = a → theta a = 1

private theorem relative_ground (D : LatticeData) (g : Charge D ≃+ Charge D)
    (U V : Carrier D ≃ₗ[ℂ] Carrier D) (thetaU thetaV : Charge D → ℂˣ)
    (hU : ∀ a, U (Finsupp.single a 1) = (thetaU a : ℂ) • Finsupp.single (g a) 1)
    (hV : ∀ a, V (Finsupp.single a 1) = (thetaV a : ℂ) • Finsupp.single (g a) 1)
    (a : Charge D) :
    (V.trans U.symm) (Finsupp.single a 1) =
      ((thetaV a / thetaU a : ℂˣ) : ℂ) • Finsupp.single a 1 := by
  apply U.injective
  change U (U.symm (V (Finsupp.single a 1))) =
    U (((thetaV a / thetaU a : ℂˣ) : ℂ) • Finsupp.single a 1)
  rw [U.apply_symm_apply, hV, map_smul, hU, smul_smul, ← Units.val_mul, div_mul_cancel]

private theorem eq_of_same_ground (D : LatticeData) (g : Charge D ≃+ Charge D)
    (U V : Carrier D ≃ₗ[ℂ] Carrier D) (hU : PreservesModes D U) (hV : PreservesModes D V)
    (theta : Charge D → ℂˣ)
    (hUg : ∀ a, U (Finsupp.single a 1) = (theta a : ℂ) • Finsupp.single (g a) 1)
    (hVg : ∀ a, V (Finsupp.single a 1) = (theta a : ℂ) • Finsupp.single (g a) 1) : U = V := by
  have hground (a : Charge D) :
      (V.trans U.symm) (Finsupp.single a 1) = ((1 : ℂˣ) : ℂ) • Finsupp.single a 1 := by
    simpa only [div_self'] using relative_ground D g U V theta theta hUg hVg a
  have hsector := (ground_phase_classification D (V.trans U.symm)
    (preserving_trans D V U.symm hV (preserving_symm D U hU)) (fun _ => 1) hground).2.2
  apply LinearEquiv.toLinearMap_injective
  apply Finsupp.lhom_ext
  intro a p
  change U (Finsupp.single a p) = V (Finsupp.single a p)
  have h := hsector a p
  change U.symm (V (Finsupp.single a p)) = ((1 : ℂˣ) : ℂ) • Finsupp.single a p at h
  rw [Units.val_one, one_smul] at h
  exact (U.symm_apply_eq.mp h).symm

/-- The actual diagonal character conjugates standard lifts of the same charge action.
It fixes the neutral sector pointwise, including the vacuum and the conformal vector. -/
theorem standard_lifts_conjugate (D : LatticeData) (g : Charge D ≃+ Charge D)
    (U V : Carrier D ≃ₗ[ℂ] Carrier D) (thetaU thetaV : Charge D → ℂˣ)
    (hU : IsStandardLift D g U thetaU) (hV : IsStandardLift D g V thetaV) :
    ∃ delta : Charge D →+ Additive ℂˣ,
      let C := diagonal D (fun a => (delta a).toMul)
      PreservesModes D C ∧
        (∀ p : Oscillator D, C (Finsupp.single 0 p) = Finsupp.single 0 p) ∧
        (C.trans U).trans C.symm = V := by
  let eta (a : Charge D) : ℂˣ := thetaV a / thetaU a
  have hclass := ground_phase_classification D (V.trans U.symm)
    (preserving_trans D V U.symm hV.1 (preserving_symm D U hU.1))
    eta (relative_ground D g U V thetaU thetaV hU.2.1 hV.2.1)
  let chi : Charge D →+ Additive ℂˣ :=
    { toFun := fun a => Additive.ofMul (eta a)
      map_zero' := congrArg Additive.ofMul hclass.1
      map_add' := fun a b => congrArg Additive.ofMul (hclass.2.1 a b) }
  have hchi (a : Charge D) (ha : g a = a) : chi a = 0 := by
    change Additive.ofMul (thetaV a / thetaU a) = 0
    simp only [hV.2.2 a ha, hU.2.2 a ha, div_self', ofMul_one]
  obtain ⟨delta, hdelta⟩ := exists_character_coboundary g chi hchi
  let d (a : Charge D) : ℂˣ := (delta a).toMul
  let C := diagonal D d
  have hC : PreservesModes D C :=
    diagonal_preserves D d (fun a b => congrArg Additive.toMul (delta.map_add a b))
  have hneutral (p : Oscillator D) : C (Finsupp.single 0 p) = Finsupp.single 0 p := by
    rw [diagonal_single]
    have hzero : d 0 = 1 := congrArg Additive.toMul delta.map_zero
    rw [hzero, Units.val_one, one_smul]
  have hphase (a : Charge D) : thetaV a * d (g a) = d a * thetaU a := by
    have h := congrArg Additive.toMul (hdelta a)
    change thetaV a / thetaU a = (delta (a - g a)).toMul at h
    rw [map_sub, toMul_sub] at h
    exact div_eq_div_iff_mul_eq_mul.mp h
  let theta (a : Charge D) := thetaV a * d (g a)
  have hleft (a : Charge D) :
      (C.trans U) (Finsupp.single a 1) = (theta a : ℂ) • Finsupp.single (g a) 1 := by
    change U (C (Finsupp.single a 1)) = _
    rw [diagonal_single, map_smul, hU.2.1, smul_smul, ← Units.val_mul, ← hphase a]
  have hright (a : Charge D) :
      (V.trans C) (Finsupp.single a 1) = (theta a : ℂ) • Finsupp.single (g a) 1 := by
    change C (V (Finsupp.single a 1)) = _
    rw [hV.2.1, map_smul, diagonal_single, smul_smul, ← Units.val_mul]
  have h := eq_of_same_ground D g (C.trans U) (V.trans C)
    (preserving_trans D C U hC hU.1) (preserving_trans D V C hV.1 hC) theta hleft hright
  refine ⟨delta, hC, hneutral, ?_⟩
  change (C.trans U).trans C.symm = V
  apply LinearEquiv.ext
  intro x
  change C.symm ((C.trans U) x) = V x
  rw [h]
  exact C.symm_apply_apply (V x)

/-- A lift `R` of the lattice conjugating isometry reindexes the charges. The
diagonal correction then gives a VOA conjugacy from `U` to `V`. The two equations
for `R` at the vacuum and Sugawara vector are the usual conformal lift properties. -/
theorem standard_lifts_conjugate_of_lattice_conjugacy (D : LatticeData)
    (g g' r : Charge D ≃+ Charge D) (hr : ∀ a, r (g a) = g' (r a))
    (U V R : Carrier D ≃ₗ[ℂ] Carrier D) (thetaU thetaV thetaR : Charge D → ℂˣ)
    (hU : IsStandardLift D g U thetaU) (hV : IsStandardLift D g' V thetaV)
    (hR : PreservesModes D R)
    (hRg : ∀ a, R (Finsupp.single a 1) = (thetaR a : ℂ) • Finsupp.single (r a) 1)
    (hRv : R (vacuum D) = vacuum D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hRomega : R (omega D H) = omega D H) :
    ∃ T : Carrier D ≃ₗ[ℂ] Carrier D,
      PreservesModes D T ∧ T (vacuum D) = vacuum D ∧ T (omega D H) = omega D H ∧
        U.trans T = T.trans V := by
  let W := (R.symm.trans U).trans R
  let thetaW (b : Charge D) : ℂˣ :=
    (thetaR (r.symm b))⁻¹ * thetaU (r.symm b) * thetaR (g (r.symm b))
  have hRinv (b : Charge D) :
      R.symm (Finsupp.single b 1) =
        (((thetaR (r.symm b))⁻¹ : ℂˣ) : ℂ) • Finsupp.single (r.symm b) 1 := by
    apply R.injective
    rw [R.apply_symm_apply, map_smul, hRg, r.apply_symm_apply, smul_smul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hcharge (b : Charge D) : r (g (r.symm b)) = g' b := by
    rw [hr, r.apply_symm_apply]
  have hWg (b : Charge D) :
      W (Finsupp.single b 1) = (thetaW b : ℂ) • Finsupp.single (g' b) 1 := by
    change R (U (R.symm (Finsupp.single b 1))) = _
    simp only [hRinv, map_smul, hU.2.1, hRg, hcharge, smul_smul, thetaW, Units.val_mul]
  have hWfixed (b : Charge D) (hb : g' b = b) : thetaW b = 1 := by
    have hfix : g (r.symm b) = r.symm b := r.injective (by rw [hcharge, hb, r.apply_symm_apply])
    change (thetaR (r.symm b))⁻¹ * thetaU (r.symm b) * thetaR (g (r.symm b)) = 1
    rw [hU.2.2 _ hfix, hfix, mul_one, inv_mul_cancel]
  have hW : IsStandardLift D g' W thetaW :=
    ⟨preserving_trans D _ R (preserving_trans D R.symm U (preserving_symm D R hR) hU.1) hR,
      hWg, hWfixed⟩
  obtain ⟨delta, hC, hneutral, hconj⟩ := standard_lifts_conjugate D g' W V thetaW thetaV hW hV
  let C := diagonal D (fun a => (delta a).toMul)
  change (C.trans W).trans C.symm = V at hconj
  have hfixNeutral (p : Oscillator D) :
      C.symm (Finsupp.single 0 p) = Finsupp.single 0 p := C.symm_apply_eq.mpr (hneutral p).symm
  refine ⟨R.trans C.symm, preserving_trans D R C.symm hR (preserving_symm D C hC), ?_, ?_, ?_⟩
  · change C.symm (R (vacuum D)) = vacuum D
    rw [hRv]
    exact hfixNeutral 1
  · change C.symm (R (omega D H)) = omega D H
    rw [hRomega]
    exact hfixNeutral _
  · apply LinearEquiv.ext
    intro x
    change C.symm (R (U x)) = V (C.symm (R x))
    have hx := DFunLike.congr_fun hconj (C.symm (R x))
    change C.symm (R (U (R.symm (C (C.symm (R x)))))) = V (C.symm (R x)) at hx
    simpa only [C.apply_symm_apply, R.symm_apply_apply] using hx

/-- Pulling back the state argument by `T⁻¹` transports any cover branch-change
law. For a third-twisted field, `branch` is the chosen cube-root rescaling. -/
theorem pullback_twisted_covariance (D : LatticeData)
    (U V T : Carrier D ≃ₗ[ℂ] Carrier D) (hT : U.trans T = T.trans V)
    {F : Type*} (field : Carrier D → F) (branch : F → F)
    (hfield : ∀ a, field (U a) = branch (field a)) (a : Carrier D) :
    field (T.symm (V a)) = branch (field (T.symm a)) := by
  have h : T.symm (V a) = U (T.symm a) := by
    apply T.injective
    have ha := DFunLike.congr_fun hT (T.symm a)
    change T (U (T.symm a)) = V (T (T.symm a)) at ha
    simpa only [T.apply_symm_apply] using ha.symm
  rw [h, hfield]

#print axioms exists_character_coboundary
#print axioms standard_lifts_conjugate_of_lattice_conjugacy

end
end D5.S3.VertexAlgebra.Lattice.StandardLiftCharacterConjugacy
