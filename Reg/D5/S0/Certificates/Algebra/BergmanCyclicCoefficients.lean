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
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ ⟨_, field, n, _, _⟩ v => by
    letI := field
    classical
    exact decide (positivePower v (n - 1) ≠ 0)) (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] (n : ℕ) (hn : 2 ≤ n)
    (q : Bool) (i : Fin 3) (v : Algebra F n q)
    (hv : v ∈ Submodule.span F (Set.range (fun j : {j : Fin 3 // j ≠ i} =>
      delta F (Model n q) (generator n q j.val)))) (hne : v ≠ 0),
      r.readout () ⟨F, field, n, q, i⟩ v = true

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
  have H := h 2 (by decide) false 2 (witness F) (witness_mem F) (witness_ne F)
  cases H

abbrev pairAudit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.pair_span_nonvanishing.{u}) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.pair_span_nonvanishing.{u}),
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
    have hz : positivePower (0 : Algebra F 2 false) (2 - 1) = 0 := by
      simp [positivePower]
    simpa [actual, realize, p, hn, hz] using he

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
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Pair

namespace Root

abbrev Parameters := Σ F : Type u, Σ _field : Field F, Σ _n : ℕ, Bool

abbrev signature : Signature where
  Params := Parameters.{u}
  State := fun ⟨F, field, n, q⟩ => by
    letI := field
    exact Algebra F n q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ ⟨F, field, n, q⟩ => by
    letI := field
    exact Algebra F n q
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ ⟨_, field, n, _⟩ v => by
    letI := field
    exact positivePower v (n - 1)) (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ ⟨F, field, n, q⟩ _ => by
    letI := field
    exact delta F (Model n q) (.terminal 0)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] (n : ℕ) (hn : 0 < n)
    (hdiv : 6 ∣ n) (q : Bool) (ω : F) (hω : IsPrimitiveRoot ω 3),
      ∃ v ∈ Submodule.span F
        (Set.range (fun i => delta F (Model n q) (generator n q i))),
        v ≠ 0 ∧ r.readout () ⟨F, field, n, q⟩ v = 0

private noncomputable def cubeRoot : ULift.{u} ℂ :=
  ⟨Complex.exp (2 * Real.pi * Complex.I / 3)⟩

private theorem cubeRoot_primitive : IsPrimitiveRoot cubeRoot.{u} 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by decide)
  constructor
  · apply ULift.ext
    exact h.pow_eq_one
  · intro l hl
    exact h.dvd_of_pow_eq_one l (congrArg ULift.down hl)

private theorem terminal_ne (F : Type u) [Field F] (n : ℕ) (q : Bool) :
    delta F (Model n q) (.terminal 0) ≠ 0 := by
  intro h
  have hc := congrArg (fun v : Algebra F n q =>
    v ⟨.terminal 0, by intro h; cases h⟩) h
  simpa [delta] using hc

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  rcases h 6 (by decide) (by decide) false cubeRoot cubeRoot_primitive with
    ⟨v, _, _, hv⟩
  exact terminal_ne (ULift.{u} ℂ) 6 false hv

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
    let F := ULift.{u} ℚ
    let p : Parameters.{u} := ⟨F, inferInstance, 1, false⟩
    refine ⟨p, delta F (Model 1 false) (.terminal 0), 0, ?_⟩
    simpa [actual, realize, p, positivePower] using terminal_ne F 1 false

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
    coordinates := #[0, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 8
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

namespace CriterionRoot

abbrev Parameters := Σ F : Type u, Field F

abbrev signature : Signature where
  Params := Parameters.{u}
  State := fun p => p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u} :=
  realize signature (fun _ ⟨_, field⟩ ω => by
    letI := field
    classical
    exact decide (IsPrimitiveRoot ω 3)) (fun e => nomatch e)

abbrev rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {F : Type u} [field : Field F] [charZero : CharZero F] (q : Bool),
    (∃ v ∈ Submodule.span F
      (Set.range (fun i => delta F (Model 6 q) (generator 6 q i))),
      v ≠ 0 ∧ positivePower v 5 = 0) ↔
    ∃ ω : F, r.readout () ⟨F, field⟩ ω = true

private theorem actual_law : arena.{u}.Law actual := by
  intro F field charZero q
  simpa [actual, realize] using sixth_power_criterion (F := F) q

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : CharZero (ULift.{u} ℂ) := ⟨by
    intro m n he
    exact (Nat.cast_injective (R := ℂ)) (congrArg ULift.down he)⟩
  have hw := root_witness 6 (by decide) (by decide) false
    Root.cubeRoot Root.cubeRoot_primitive
  rcases (h (F := ULift.{u} ℂ) false).mp hw with ⟨ω, hω⟩
  cases hω

abbrev audit : Registration arena.{u}
    (type_of% @_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.sixth_power_criterion.{u}) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, rejected, rejected_law⟩
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
    refine ⟨⟨F, inferInstance⟩, Root.cubeRoot, 0, ?_⟩
    have hn : ¬ IsPrimitiveRoot (0 : F) 3 := by
      intro h
      have hp := h.pow_eq_one
      norm_num at hp
    simpa [actual, realize, hn] using Root.cubeRoot_primitive.{u}

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.sixth_power_criterion.{u})
    (type_of% actual.{u}) Unit Unit := {
  unitName := `D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.sixth_power_criterion.__information_unit
  realizationName := `Reg.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients.CriterionRoot.audit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨audit⟩
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
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CriterionRoot

end

end Reg.D5.S0.Certificates.Algebra.BergmanCyclicCoefficients
