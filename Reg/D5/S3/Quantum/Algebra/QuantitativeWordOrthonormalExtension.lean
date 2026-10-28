import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension

structure Parameters where
  D : ℕ
  m : ℕ
  e : Fin m → EuclideanSpace ℂ (Fin D)

abbrev signature : Signature where
  Params := Parameters
  State p := EuclideanSpace ℂ (Fin p.D)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := EuclideanSpace ℂ (Fin p.D)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => (Submodule.span ℂ (Set.range p.e)).starProjection x)
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ p x => x + if h : 0 < p.D then
    EuclideanSpace.single ⟨0, h⟩ (1 : ℂ) else 0)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D r M : ℕ) (_hr : 2 ≤ r) (_hrD : r ≤ D) (_hM : M ≤ D ^ 2)
    (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ < 1)
    (A : Fin M → Module.End ℂ (EuclideanSpace ℂ (Fin D)))
    (_hA : ∀ a x, ‖A a x‖ ≤ ‖x‖)
    (η : Fin r → EuclideanSpace ℂ (Fin D)) (_hη : Orthonormal ℂ η),
    ∃ (m : ℕ) (hrm : r ≤ m), m ≤ D ∧
      ∃ e : Fin m → EuclideanSpace ℂ (Fin D),
        Orthonormal ℂ e ∧ (∀ b, e (Fin.castLE hrm b) = η b) ∧
        (∀ a j, ‖A a (e j) - R.readout () ⟨D, m, e⟩ (A a (e j))‖ ≤ δ) ∧
        ∃ c : Fin m → (List (Fin M) × Fin r →₀ ℂ),
          (∀ j, ∀ p ∈ (c j).support, p.1.length ≤ m - r) ∧
          (∀ j, e j = (c j).sum fun p z => z • (p.1.reverse.map A).prod (η p.2)) ∧
          (∀ j, (c j).sum (fun _ z => ‖z‖) ≤ ((D : ℝ) / δ) ^ (m - r))

def registration : Registration arena (type_of% @quantitative_word_orthonormal_extension) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    obtain ⟨m, hrm, hm, e, he, hη, ht, c, hc⟩ :=
      h 2 2 1 (by omega) (by omega) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
        (fun _ => 0) (by intros; simp) (fun i => EuclideanSpace.single i 1)
        EuclideanSpace.orthonormal_single
    have hres := ht 0 (Fin.castLE hrm 0)
    norm_num [rejected, realize, PiLp.norm_single] at hres
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨quantitative_word_orthonormal_extension, rejected, hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hbad⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  · intro i
    let e : Fin 2 → EuclideanSpace ℂ (Fin 2) := fun j => EuclideanSpace.single j 1
    let p : Parameters := ⟨2, 2, e⟩
    refine ⟨p, 0, e 0, ?_⟩
    change (Submodule.span ℂ (Set.range e)).starProjection 0 ≠
      (Submodule.span ℂ (Set.range e)).starProjection (e 0)
    have hmem : e 0 ∈ Submodule.span ℂ (Set.range e) := Submodule.subset_span ⟨0, rfl⟩
    have hproj : (Submodule.span ℂ (Set.range e)).starProjection (e 0) = e 0 :=
      Submodule.starProjection_eq_self_iff.mpr hmem
    rw [map_zero, hproj]
    intro hz
    have hn : ‖e 0‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one 0
    rw [← hz, norm_zero] at hn
    exact zero_ne_one hn

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@quantitative_word_orthonormal_extension)
      (type_of% (realize signature
        (fun _ p x => (Submodule.span ℂ (Set.range p.e)).starProjection x)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension.quantitative_word_orthonormal_extension.information_unit,
  realizationName := `Reg.D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p x => (Submodule.span ℂ (Set.range p.e)).starProjection x)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension,
    definition := none,
    coordinates := #[0, 13, 15],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "body", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1

end Reg.D5.S3.Quantum.Algebra.QuantitativeWordOrthonormalExtension
