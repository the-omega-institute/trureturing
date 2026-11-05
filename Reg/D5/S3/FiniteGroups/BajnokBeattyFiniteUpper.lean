import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! Source-bound group-cardinality readouts with the full abstract telescope. -/
namespace Reg.D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
open _root_.D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

private abbrev Sample := ULift.{u} (ZMod 2 × ZMod 2)
private theorem sample_noncyclic : ¬ IsAddCyclic Sample.{u} := by
  intro h
  have hh := (AddEquiv.ulift : Sample.{u} ≃+ (ZMod 2 × ZMod 2)).isAddCyclic.mp h
  have hc := (AddGroup.isAddCyclic_prod_iff.mp hh).2.2
  norm_num [Nat.card_zmod, Nat.Coprime] at hc
private theorem sample_cover {s : ℕ} (hs : 2 ≤ s) :
    ∀ g : Sample.{u}, ∃ x y : ℤ, |x|+|y| ≤ (s : ℤ) ∧
      x • (ULift.up (1,0) : Sample.{u}) + y • ULift.up (0,1) = g := by
  rintro ⟨⟨a,b⟩⟩
  refine ⟨a.val,b.val,?_,?_⟩
  · have ha := a.val_lt
    have hb := b.val_lt
    simp only [Int.abs_natCast]
    omega
  · apply ULift.ext
    change (a.val : ℤ) • ((1,0) : ZMod 2 × ZMod 2) +
      (b.val : ℤ) • (0,1) = (a,b)
    apply Prod.ext <;> simp [zsmul_eq_mul]

abbrev natSignature : Signature where
  Params := Unit
  State _ := Type u
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev intSignature : Signature where
  Params := Unit
  State _ := Type u
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance
noncomputable def natActual : Realization natSignature.{u} := realize natSignature
  (fun _ _ G => Nat.card G) (fun e => nomatch e)
noncomputable def natRejected : Realization natSignature.{u} := realize natSignature
  (fun _ _ _ => 1000) (fun e => nomatch e)
noncomputable def intActual : Realization intSignature.{u} := realize intSignature
  (fun _ _ G => (Nat.card G : ℤ)) (fun e => nomatch e)
noncomputable def intRejected : Realization intSignature.{u} := realize intSignature
  (fun _ _ _ => 1000) (fun e => nomatch e)

abbrev dichotomyArena : Arena where
  signature := intSignature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] [Finite G] {s : ℕ}
    (_ : 3 ≤ s) (_ : ¬ IsAddCyclic G) (a b : G)
    (_ : ∀ g : G, ∃ x y : ℤ, |x|+|y| ≤ (s : ℤ) ∧ x • a+y • b = g) , ∃ c : ℕ, 2 ≤ c ∧
      (R.readout () () G ≤ 2*(s : ℤ)^2 ∨
        (Odd (c : ℤ) ∧ (c : ℤ) ∣ 2*(s : ℤ)+1 ∧
          2*R.readout () () G ≤ (2*(s : ℤ)+1)^2-(c : ℤ)^2))
private theorem dichotomyRejected_law : ¬ dichotomyArena.{u}.Law intRejected := by
  intro h
  obtain ⟨c,hc,hl | ⟨_,hd,hh⟩⟩ := h (G := Sample.{u}) (s := 3) (by norm_num) sample_noncyclic
    (ULift.up (1,0)) (ULift.up (0,1)) (sample_cover (by norm_num))
  · norm_num [intRejected,realize] at hl
  · have hdN : c ∣ 7 := by exact_mod_cast hd
    have hp : Nat.Prime 7 := by norm_num
    rcases hp.eq_one_or_self_of_dvd c hdN with he | he
    · omega
    · subst c
      norm_num [intRejected,realize] at hh
noncomputable def dichotomySource : Registration dichotomyArena.{u}
    (type_of% (@finite_noncyclic_upper_dichotomy.{u})) where
  actual := intActual
  bridge := Iff.rfl
  variation := ⟨finite_noncyclic_upper_dichotomy, intRejected, dichotomyRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intRejected, ?_, rfl, dichotomyRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), ULift.{u} (Fin 1), ULift.{u} (Fin 2),
      by norm_num [intActual,realize,Nat.card_eq_fintype_card]⟩
noncomputable def dichotomyRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@finite_noncyclic_upper_dichotomy.{u}) (Realization intSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.finite_noncyclic_upper_dichotomy.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.dichotomySource
  realizationSource := none
  generated := false
  arena := .source ⟨dichotomyArena⟩
  objectArena := .source ⟨dichotomyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source dichotomyArena ⟨dichotomySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize intSignature
    (fun _ _ G => (Nat.card G : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev primeArena : Arena where
  signature := natSignature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] [Finite G] {s : ℕ}
    (_ : 3 ≤ s) (_ : ¬ IsAddCyclic G) (a b : G)
    (_ : ∀ g : G, ∃ x y : ℤ, |x|+|y| ≤ (s : ℤ) ∧ x • a+y • b = g) (_ : Nat.Prime (2*s+1)), R.readout () () G ≤ 2*s^2
private theorem primeRejected_law : ¬ primeArena.{u}.Law natRejected := by
  intro h
  have hh := h (G := Sample.{u}) (s := 3) (by norm_num) sample_noncyclic
    (ULift.up (1,0)) (ULift.up (0,1)) (sample_cover (by norm_num)) (by norm_num)
  norm_num [natRejected,realize] at hh
noncomputable def primeSource : Registration primeArena.{u}
    (type_of% (@finite_noncyclic_upper_prime.{u})) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨finite_noncyclic_upper_prime, natRejected, primeRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, primeRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), ULift.{u} (Fin 1), ULift.{u} (Fin 2),
      by norm_num [natActual,realize,Nat.card_eq_fintype_card]⟩
noncomputable def primeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@finite_noncyclic_upper_prime.{u}) (Realization natSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.finite_noncyclic_upper_prime.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.primeSource
  realizationSource := none
  generated := false
  arena := .source ⟨primeArena⟩
  objectArena := .source ⟨primeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source primeArena ⟨primeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature
    (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev compositeArena : Arena where
  signature := natSignature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] [Finite G] {s : ℕ}
    (_ : 3 ≤ s) (_ : ¬ IsAddCyclic G) (a b : G)
    (_ : ∀ g : G, ∃ x y : ℤ, |x|+|y| ≤ (s : ℤ) ∧ x • a+y • b = g) (_ : ¬ Nat.Prime (2*s+1)),
    2*R.readout () () G ≤ (2*s+1)^2-(Nat.minFac (2*s+1))^2
private theorem compositeRejected_law : ¬ compositeArena.{u}.Law natRejected := by
  intro h
  have hh := h (G := Sample.{u}) (s := 4) (by norm_num) sample_noncyclic
    (ULift.up (1,0)) (ULift.up (0,1)) (sample_cover (by norm_num)) (by norm_num)
  norm_num [natRejected,realize] at hh
noncomputable def compositeSource : Registration compositeArena.{u}
    (type_of% (@finite_noncyclic_upper_composite.{u})) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨finite_noncyclic_upper_composite, natRejected, compositeRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, compositeRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), ULift.{u} (Fin 1), ULift.{u} (Fin 2),
      by norm_num [natActual,realize,Nat.card_eq_fintype_card]⟩
noncomputable def compositeRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@finite_noncyclic_upper_composite.{u}) (Realization natSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.finite_noncyclic_upper_composite.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.compositeSource
  realizationSource := none
  generated := false
  arena := .source ⟨compositeArena⟩
  objectArena := .source ⟨compositeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source compositeArena ⟨compositeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature
    (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev upperArena : Arena where
  signature := natSignature.{u}
  Law R := ∀ {G : Type u} [AddCommGroup G] [Finite G] {s : ℕ}
    (_ : 3 ≤ s) (_ : ¬ IsAddCyclic G) (a b : G)
    (_ : ∀ g : G, ∃ x y : ℤ, |x|+|y| ≤ (s : ℤ) ∧ x • a+y • b = g) , if Nat.Prime (2*s+1) then R.readout () () G ≤ 2*s^2
    else 2*R.readout () () G ≤ (2*s+1)^2-(Nat.minFac (2*s+1))^2
private theorem upperRejected_law : ¬ upperArena.{u}.Law natRejected := by
  intro h
  have hh := h (G := Sample.{u}) (s := 3) (by norm_num) sample_noncyclic
    (ULift.up (1,0)) (ULift.up (0,1)) (sample_cover (by norm_num))
  norm_num [natRejected,realize] at hh
noncomputable def upperSource : Registration upperArena.{u}
    (type_of% (@finite_noncyclic_upper.{u})) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨finite_noncyclic_upper, natRejected, upperRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, upperRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), ULift.{u} (Fin 1), ULift.{u} (Fin 2),
      by norm_num [natActual,realize,Nat.card_eq_fintype_card]⟩
noncomputable def upperRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@finite_noncyclic_upper.{u}) (Realization natSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.finite_noncyclic_upper.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyFiniteUpper.upperSource
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature
    (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
