import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySharpMaximum
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift

/-! The complete maximum law with an actual group-cardinality observation.
Only the first upper-bound occurrence is intervened on; the literal uniform
bound and the full finite noncyclic attainment assertion remain in the law. -/
namespace Reg.D5.S3.FiniteGroups.BajnokBeattySharpMaximum
open _root_.D5.S3.FiniteGroups.BajnokBeattySharpMaximum
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

noncomputable def actual : Realization natSignature.{u} := realize natSignature
  (fun _ _ G => Nat.card G) (fun e => nomatch e)
noncomputable def rejected : Realization natSignature.{u} := realize natSignature
  (fun _ _ _ => 1000) (fun e => nomatch e)

abbrev maximumArena : Arena where
  signature := natSignature.{u}
  Law R := ∀ (s : ℕ) (_ : 3 ≤ s),
    (∀ (G : Type u) [AddCommGroup G] [Finite G],
      ¬ IsAddCyclic G → ∀ a b : G, a ≠ b →
        (∀ g : G, ∃ x y : ℤ,
          |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) →
        R.readout () () G ≤ MaximumOrder s ∧ Nat.card G ≤ 2 * s^2 + 2 * s - 4) ∧
    (∃ c k : ℕ, 2 ≤ c ∧ 1 ≤ k ∧
      ∃ a b : ZMod c × ZMod (c * k), a ≠ b ∧
        ¬ IsAddCyclic (ZMod c × ZMod (c * k)) ∧
        (∀ g : ZMod c × ZMod (c * k), ∃ x y : ℤ,
          |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) ∧
        Finite (ZMod c × ZMod (c * k)) ∧
        Nat.card (ZMod c × ZMod (c * k)) = MaximumOrder s)

private theorem rejected_law : ¬ maximumArena.{u}.Law rejected := by
  intro h
  have hh := (h 3 (by norm_num)).1 Sample.{u} sample_noncyclic
    (ULift.up (1,0)) (ULift.up (0,1)) (by
      intro he
      have he' : (1 : ZMod 2) = 0 := congrArg (fun x : Sample.{u} => x.down.1) he
      norm_num at he') (sample_cover (by norm_num))
  norm_num [rejected, realize, MaximumOrder] at hh

noncomputable def maximumSource : Registration maximumArena.{u}
    (type_of% (@sharp_maximum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_maximum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), ULift.{u} (Fin 1), ULift.{u} (Fin 2),
      by norm_num [actual, realize, Nat.card_eq_fintype_card]⟩

noncomputable def maximumRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@sharp_maximum.{u})
      (Realization natSignature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySharpMaximum.sharp_maximum.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySharpMaximum.maximumSource
  realizationSource := none
  generated := false
  arena := .source ⟨maximumArena⟩
  objectArena := .source ⟨maximumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source maximumArena ⟨maximumSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature
    (fun _ _ G => Nat.card G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattySharpMaximum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","body","body","body","body",
        "body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySharpMaximum
