import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Exact terminal coefficients as a dependent family -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Certificates.Algebra.BergmanQuestion15Refutation
open _root_.D5.S0.Certificates.Algebra.BergmanCyclicSemigroup
open _root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients

namespace Reg.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients

universe u
noncomputable section

abbrev Parameters := Σ F : Type u, Σ _field : Field F, Σ _n : ℕ, Bool

abbrev signature : Signature where
  Params := Parameters.{u}
  State := fun p => Fin 3 → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ ⟨F, field, n, q⟩ => by
    letI := field
    exact Algebra F n q
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ ⟨F, field, n, q⟩ a => by
    letI := field
    exact ((a 0 + a 1) ^ n - a 1 ^ n) • delta F (Model n q) (.terminal 0) +
      ((a 1 + a 2) ^ n - a 2 ^ n) • delta F (Model n q) (.terminal 1) +
      ((a 2 + a 0) ^ n - a 0 ^ n) • delta F (Model n q) (.terminal 2))
    (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ ⟨_, field, _, _⟩ _ => by
    letI := field
    exact 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] (n : ℕ) (hn : 0 < n)
    (q : Bool) (a : Fin 3 → F),
      positivePower (combination n q a) (n - 1) =
        r.readout () ⟨F, field, n, q⟩ a

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let F := ULift.{u} ℚ
  have H := h (F := F) 1 (by decide) false (![1, 0, 0])
  change positivePower (combination 1 false (![1, 0, 0] : Fin 3 → F)) (1 - 1) = 0 at H
  rw [terminal_coefficients 1 (by decide) false] at H
  have hc := congrArg (fun v : Algebra F 1 false =>
    v ⟨.terminal 0, by intro h; cases h⟩) H
  norm_num [delta] at hc

abbrev coefficientsAudit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.terminal_coefficients.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.terminal_coefficients.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let F := ULift.{u} ℚ
    let p : Parameters.{u} := ⟨F, inferInstance, 1, false⟩
    refine ⟨p, ![1, 0, 0], 0, ?_⟩
    intro he
    have hc := congrArg (fun v : Algebra F 1 false =>
      v ⟨.terminal 0, by intro h; cases h⟩) he
    norm_num [actual, realize, delta, p] at hc
    change (1 : F) = 0 at hc
    exact one_ne_zero hc

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.terminal_coefficients.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.terminal_coefficients.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.coefficientsAudit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨coefficientsAudit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
    definition := none
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Pair

abbrev Parameters := Σ F : Type u, Σ _field : Field F, Σ _n : ℕ, Σ _q : Bool, Fin 3

abbrev signature : Signature where
  Params := Parameters.{u}
  State := fun ⟨F, field, n, q, _⟩ => by
    letI := field
    exact Algebra F n q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ ⟨F, field, n, q, _⟩ => by
    letI := field
    exact Algebra F n q
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ ⟨_, field, n, _, _⟩ v => by
    letI := field
    exact positivePower v (n - 1)) (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ ⟨_, field, _, _, _⟩ _ => by
    letI := field
    exact 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] (n : ℕ) (hn : 2 ≤ n)
    (q : Bool) (i : Fin 3) (v : Algebra F n q)
    (hv : v ∈ Submodule.span F (Set.range (fun j : {j : Fin 3 // j ≠ i} =>
      delta F (Model n q) (generator n q j.val)))) (hne : v ≠ 0),
      r.readout () ⟨F, field, n, q, i⟩ v ≠ 0

private abbrev witness (F : Type u) [Field F] : Algebra F 2 false :=
  delta F (Model 2 false) (generator 2 false 0)

private theorem witness_mem (F : Type u) [Field F] :
    witness F ∈ Submodule.span F (Set.range (fun j : {j : Fin 3 // j ≠ 2} =>
      delta F (Model 2 false) (generator 2 false j.val))) :=
  Submodule.subset_span ⟨⟨0, by decide⟩, rfl⟩

private theorem witness_ne (F : Type u) [Field F] : witness F ≠ 0 := by
  have hg : generator 2 false 0 ≠ 0 := by simp [generator, normal, survives]
  intro h
  have hc := congrArg (fun v : Algebra F 2 false => v ⟨generator 2 false 0, hg⟩) h
  simp [witness, delta, hg] at hc

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let F := ULift.{u} ℚ
  exact h 2 (by decide) false 2 (witness F) (witness_mem F) (witness_ne F) rfl

abbrev pairAudit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.pair_span_nonvanishing.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.pair_span_nonvanishing.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let F := ULift.{u} ℚ
    let p : Parameters.{u} := ⟨F, inferInstance, 2, false, 2⟩
    refine ⟨p, witness F, 0, ?_⟩
    intro he
    have hn := pair_span_nonvanishing 2 (by decide) false 2
      (witness F) (witness_mem F) (witness_ne F)
    apply hn
    simpa [actual, realize, p, positivePower] using he

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.pair_span_nonvanishing.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.pair_span_nonvanishing.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.Pair.pairAudit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨pairAudit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
    definition := none
    coordinates := #[0, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Pair

namespace Root

abbrev Parameters := Σ F : Type u, Σ _field : Field F, Bool

abbrev signature : Signature where
  Params := Parameters.{u}
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ ⟨F, field, q⟩ n => by
    letI := field
    exact ∃ v ∈ Submodule.span F
      (Set.range (fun i => delta F (Model n q) (generator n q i))),
      v ≠ 0 ∧ positivePower v (n - 1) = 0) (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] (n : ℕ) (hn : 0 < n)
    (hdiv : 6 ∣ n) (q : Bool) (ω : F) (hω : IsPrimitiveRoot ω 3),
      r.readout () ⟨F, field, q⟩ n

private noncomputable def cubeRoot : ULift.{u} ℂ :=
  ⟨Complex.exp (2 * Real.pi * Complex.I / 3)⟩

private theorem cubeRoot_primitive : IsPrimitiveRoot cubeRoot.{u} 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by decide)
  constructor
  · apply ULift.ext
    exact h.pow_eq_one
  · intro l hl
    exact h.dvd_of_pow_eq_one l (congrArg ULift.down hl)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h 6 (by decide) (by decide) false cubeRoot cubeRoot_primitive

abbrev rootAudit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.root_witness.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.root_witness.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let F := ULift.{u} ℂ
    let p : Parameters.{u} := ⟨F, inferInstance, false⟩
    refine ⟨p, 6, 1, ?_⟩
    intro he
    have h6 : actual.readout i p 6 :=
      root_witness 6 (by decide) (by decide) false cubeRoot cubeRoot_primitive
    have h1 : actual.readout i p 1 := (Iff.of_eq he).mp h6
    rcases h1 with ⟨v, _, hne, hp⟩
    exact hne hp

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.root_witness.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.root_witness.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.Root.rootAudit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨rootAudit⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
    definition := none
    coordinates := #[0, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Root

namespace Criterion

abbrev Parameters := Σ F : Type u, Σ field : Field F,
  letI := field
  PLift (CharZero F)

abbrev signature : Signature where
  Params := Parameters.{u}
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ ⟨F, field, _⟩ q => by
    letI := field
    exact ∃ v ∈ Submodule.span F
      (Set.range (fun i => delta F (Model 6 q) (generator 6 q i))),
      v ≠ 0 ∧ positivePower v 5 = 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] [charZero : CharZero F] (q : Bool),
    r.readout () ⟨F, field, ⟨charZero⟩⟩ q ↔ ∃ ω : F, IsPrimitiveRoot ω 3

theorem exact_bridge : arena.{u}.Law actual ↔
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.sixth_power_criterion.{u}) :=
  Iff.rfl

theorem actual_law : arena.{u}.Law actual := sixth_power_criterion

/-- The literal existential observation is constant in the presentation flag.
This observation cannot supply the dependence slot of this audit template. -/
theorem no_q_dependence : ¬ (∀ i : signature.{u}.Role,
    ∃ p s t, actual.readout i p s ≠ actual.readout i p t) := by
  intro h
  rcases h () with ⟨⟨F, field, charZero⟩, s, t, hne⟩
  letI := field
  letI := charZero.down
  exact hne (propext ((sixth_power_criterion (F := F) s).trans
    (sixth_power_criterion (F := F) t).symm))

end Criterion

end

end Reg.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
