import D5.S3.Factorization.Embeddings.FiniteKernelModThree
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Tactic
import Mathlib.Algebra.Field.ULift
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree
open _root_.D5.S3.Factorization.Embeddings.FiniteKernelModThree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v

/-- The source's natural coefficient is read through its literal dictionary.
Its single data field ranges over all natural coefficients. The law varies only
this coefficient; the quotient, all structures and every premise stay in scope. -/
abbrev scalarSignature : Signature where
  Params := Unit
  State _ := OfNat ℕ 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev scalarActual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ n => n.ofNat) (fun e => nomatch e)
abbrev scalarBad (n : ℕ) : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => n) (fun e => nomatch e)
private theorem scalarDependence : ObservationalDependence scalarSignature scalarActual := by
  intro i
  refine ⟨(), ⟨0⟩, ⟨1⟩, ?_⟩
  change (0 : ℕ) ≠ 1
  decide

namespace descent
abbrev arena : Arena where
  signature := scalarSignature
  Law r := ∀ {A : Type u} {L : Type v} [AddCommGroup A] [AddCommGroup L]
    (f : A →+ L) (hf : Function.Surjective f) [Finite f.ker]
    (h3 : ∀ a : A, r.readout () () inferInstance • a = 0 → a = 0)
    [Module.Free ℤ L] [Module.Finite ℤ L],
    Module.Finite (ZMod 3) (ModN A 3) ∧
      Module.finrank (ZMod 3) (ModN A 3) = Module.finrank ℤ L
private theorem bad_law : ¬ arena.{u,v}.Law (scalarBad 1) := by
  intro h
  let A := ULift.{u} (ZMod 3)
  let L := PUnit.{v + 1}
  let f : A →+ L := 0
  have hf : Function.Surjective f := fun x => ⟨0, Subsingleton.elim _ _⟩
  have h1 (a : A) (ha : (1 : ℕ) • a = 0) : a = 0 := by simpa using ha
  obtain ⟨hfinite, hdim⟩ := h f hf h1
  letI := hfinite
  have hdim0 : Module.finrank (ZMod 3) (ModN A 3) = 0 := hdim.trans (Module.finrank_eq_zero_of_subsingleton ℤ L)
  letI : Subsingleton (ModN A 3) := (Module.finrank_eq_zero_iff_of_free (ZMod 3) (ModN A 3)).mp hdim0
  have hz : ModN.mkQ (G := A) 3 (⟨1⟩ : A) = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  change (3 : ℤ) • a = (⟨1⟩ : A) at ha
  have he := congrArg (fun x : A => x.down) ha
  change (3 : ℤ) • a.down = (1 : ZMod 3) at he
  have hz : (3 : ℤ) • a.down = 0 := by
    rw [ofNat_zsmul]
    exact ZModModule.char_nsmul_eq_zero 3 _
  exact zero_ne_one (hz.symm.trans he)

def evidence : Registration arena.{u,v} (type_of% @modThree_finite_finrank.{u,v}) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@modThree_finite_finrank, scalarBad 1, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarBad 1, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := scalarDependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@modThree_finite_finrank.{u,v}) (Realization scalarSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree.descent.unit
  realizationName := `Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree.descent.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨evidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ n => n.ofNat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.Embeddings.FiniteKernelModThree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain",
        "body", "domain", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end descent

namespace embedded
open NumberField
abbrev arena : Arena where
  signature := scalarSignature
  Law r := ∀ {K : Type u} {U : Type v} [Field K] [NumberField K] [CommGroup U]
    (i : U →* (𝓞 K)ˣ) (hi : Function.Injective i)
    (h3 : ∀ x : U, x ^ r.readout () () inferInstance = 1 → x = 1),
    Module.Finite (ZMod 3) (ModN (Additive U) 3) ∧
      Module.finrank (ZMod 3) (ModN (Additive U) 3) ≤ NumberField.Units.rank K
private theorem bad_law : ¬ arena.{u,v}.Law (scalarBad 1) := by
  intro h
  let K := ULift.{u} (CyclotomicField 3 ℚ)
  letI : NumberField K := NumberField.of_ringEquiv (CyclotomicField 3 ℚ) K
    ULift.ringEquiv.symm
  letI : IsCyclotomicExtension {3} ℚ K :=
    IsCyclotomicExtension.equiv {3} ℚ (CyclotomicField 3 ℚ) (ULift.algEquiv (R := ℚ) (A := CyclotomicField 3 ℚ)).symm
  let ζ := IsCyclotomicExtension.zeta 3 ℚ K
  have hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : IsPrimitiveRoot η 3 := hζ.toInteger_isPrimitiveRoot.isUnit_unit (by decide)
  let U := ULift.{v} (Multiplicative (ZMod 3))
  let e : Multiplicative (ZMod 3) ≃* Subgroup.zpowers η :=
    hη.zmodEquivZPowers.toMultiplicativeLeft
  let i : U →* (𝓞 K)ˣ :=
    (Subgroup.zpowers η).subtype.comp (e.toMonoidHom.comp MulEquiv.ulift.toMonoidHom)
  have hi : Function.Injective i := Subtype.val_injective.comp (e.injective.comp ULift.down_injective)
  have h1 (x : U) (hx : x ^ (1 : ℕ) = 1) : x = 1 := by simpa using hx
  obtain ⟨hfinite, hdim⟩ := h i hi h1
  have hrank : NumberField.Units.rank K = 0 := by
    dsimp only [NumberField.Units.rank]
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) K (by decide),
      IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3 K]
    rfl
  letI := hfinite
  have hdim0 : Module.finrank (ZMod 3) (ModN (Additive U) 3) = 0 :=
    Nat.eq_zero_of_le_zero (hrank ▸ hdim)
  letI : Subsingleton (ModN (Additive U) 3) :=
    (Module.finrank_eq_zero_iff_of_free (ZMod 3) (ModN (Additive U) 3)).mp hdim0
  have hz : ModN.mkQ (G := Additive U) 3
      (Additive.ofMul (⟨Multiplicative.ofAdd 1⟩ : U)) = 0 := Subsingleton.elim _ _
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  change (3 : ℤ) • a = Additive.ofMul (⟨Multiplicative.ofAdd 1⟩ : U) at ha
  have he := congrArg (fun x : Additive U => x.toMul.down.toAdd) ha
  change (3 : ℤ) • a.toMul.down.toAdd = (1 : ZMod 3) at he
  have hz : (3 : ℤ) • a.toMul.down.toAdd = 0 := by
    rw [ofNat_zsmul]
    exact ZModModule.char_nsmul_eq_zero 3 _
  exact zero_ne_one (hz.symm.trans he)

def evidence : Registration arena.{u,v} (type_of% @embedded_units_modThree.{u,v}) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@embedded_units_modThree, scalarBad 1, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarBad 1, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := scalarDependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@embedded_units_modThree.{u,v}) (Realization scalarSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree.embedded.unit
  realizationName := `Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree.embedded.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨evidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ n => n.ofNat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.Embeddings.FiniteKernelModThree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain",
        "body", "domain", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end embedded

namespace witness
abbrev arena : Arena where
  signature := scalarSignature
  Law r := ∀ {U : Type u} [CommGroup U] (u v : U),
    ModN.mkQ (G := Additive U) 3 (Additive.ofMul u) =
      ModN.mkQ (G := Additive U) 3 (Additive.ofMul v) →
    ∃ w : U, u = v * w ^ r.readout () () inferInstance
private theorem bad_law : ¬ arena.{u}.Law (scalarBad 0) := by
  intro h
  let U := Multiplicative (ULift.{u} ℤ)
  have hq : ModN.mkQ (G := Additive U) 3 (Additive.ofMul (Multiplicative.ofAdd ⟨3⟩)) =
      ModN.mkQ (G := Additive U) 3 (Additive.ofMul (1 : U)) := by
    change ModN.mkQ (G := ULift.{u} ℤ) 3 (⟨3⟩ : ULift.{u} ℤ) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨⟨1⟩, rfl⟩
  obtain ⟨w, hw⟩ := h (Multiplicative.ofAdd ⟨3⟩ : U) 1 hq
  change (Multiplicative.ofAdd ⟨3⟩ : U) = 1 * w ^ 0 at hw
  rw [pow_zero, mul_one] at hw
  have he := congrArg (fun x : U => x.toAdd.down) hw
  norm_num at he

def evidence : Registration arena.{u} (type_of% @exists_original_cube_of_quotient_eq.{u}) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨@exists_original_cube_of_quotient_eq, scalarBad 0, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarBad 0, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := scalarDependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@exists_original_cube_of_quotient_eq.{u}) (Realization scalarSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree.witness.unit
  realizationName := `Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree.witness.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ n => n.ofNat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.Embeddings.FiniteKernelModThree
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end witness

end Reg.D5.S3.Factorization.Embeddings.FiniteKernelModThree
