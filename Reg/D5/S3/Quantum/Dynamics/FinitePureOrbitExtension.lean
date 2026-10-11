import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
import D5.S3.Quantum.Dynamics.PositivePauliClockOrder
import Reg.Support.DependentFamily
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Field.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open scoped BigOperators

set_option quotPrecheck false in
local notation "identityChannel" => fun (d : ℕ) =>
  ({ toCompletelyPositiveMap := {
      toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := by
        intro k X hX
        change 0 ≤ X.map id
        simpa only [CStarMatrix.map_id] using hX }
     trace_preserving := fun _ => rfl } : QuantumChannel (Fin d) (Fin d))

namespace Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension

open _root_.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel

universe u v w

/-- The observed data are the natural cutoff for stabilization. -/
@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n - 1) (fun impossible => nomatch impossible)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun impossible => nomatch impossible)

/-- The entire original telescope, with only the conclusion's cutoff observed. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} {V : Type v} {ι : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι]
    (A : V ≃ₗ[K] V) (S : ι → Submodule K V)
    (_hS : iSupIndep S) (_hne : ∀ i, S i ≠ ⊥) (_hcard : 2 ≤ Fintype.card ι)
    (x : V) (_hx : x ≠ 0)
    (_hprefix : ∀ j < 2 * finrank K V - 1, ∃ i, (A ^ j) x ∈ S i),
    (∃ L, 1 ≤ L ∧ L < R.readout () () (2 * finrank K V) ∧
      wordPotential A S (L + 1) = wordPotential A S L) ∧
    ∀ k : ℕ, ∃ i, (A ^ k) x ∈ S i

private theorem actual_law : arena.{u,v,w}.Law actual :=
  @pure_prefix_potential_stabilizes.{u,v,w}

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let K := ULift.{u} ℚ
  let V := ULift.{v} (Fin 2 → ℚ)
  let ι := ULift.{w} (Fin 2)
  let b0 : Basis (Fin 2) K (Fin 2 → ℚ) :=
    (Pi.basisFun ℚ (Fin 2)).mapCoeffs ULift.ringEquiv.symm (fun _ _ => rfl)
  let b : Basis ι K V := (b0.map ULift.moduleEquiv.symm).reindex Equiv.ulift.symm
  letI : Module.Finite K V := Module.Finite.of_basis b
  let S : ι → Submodule K V := fun i => Submodule.span K {b i}
  have hS : iSupIndep S := b.linearIndependent.iSupIndep_span_singleton
  have hne (i : ι) : S i ≠ ⊥ := by
    intro hz
    exact b.ne_zero i (Submodule.span_singleton_eq_bot.mp hz)
  let z : ι := ULift.up 0
  have hx : b z ≠ 0 := b.ne_zero z
  have hp : ∀ j < 2 * finrank K V - 1,
      ∃ i, ((LinearEquiv.refl K V) ^ j) (b z) ∈ S i := by
    intro j _
    refine ⟨z, ?_⟩
    change ((1 : V ≃ₗ[K] V) ^ j) (b z) ∈ S z
    rw [one_pow]
    exact Submodule.subset_span (Set.mem_singleton (b z))
  obtain ⟨L, _, hL, _⟩ :=
    (h (LinearEquiv.refl K V) S hS hne (by simp [ι]) (b z) hx hp).1
  exact Nat.not_lt_zero L hL

def registration : Registration arena.{u,v,w} (arena.{u,v,w}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    exact ⟨(), 0, 2, by norm_num [actual, realize]⟩

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@pure_prefix_potential_stabilizes.{u,v,w})
      (type_of% (realize signature (fun _ _ n => n - 1) (fun impossible => nomatch impossible)))
      Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.informationUnit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => n - 1) (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FinitePureOrbitExtension,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension

namespace Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Channel

universe u

open _root_.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder MatrixOrder

local notation "mixed" =>
  _root_.D5.S3.Quantum.Dynamics.PositivePauliClockOrder.mixedState

private theorem mixed_not_pure : ¬ IsPure mixed := by
  rintro ⟨v, hv⟩
  have hunit : star v ⬝ᵥ v = 1 := by
    have h := mixed.2.2
    rw [hv] at h
    change Matrix.trace (Matrix.vecMulVec v (star v)) = 1 at h
    simpa only [Matrix.trace_vecMulVec, dotProduct_comm] using h
  have hidem : Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec v (star v) := by
    simp only [Matrix.vecMulVec_mul_vecMulVec, hunit, one_smul]
  have hm := congrArg CStarMatrix.ofMatrix.symm hv
  change (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
    Matrix.vecMulVec v (star v) at hm
  rw [← hm] at hidem
  have hh := congrFun₂ hidem 0 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hh

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 * n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {κ : Type u} [Fintype κ]
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∑ u, (K u).conjTranspose * K u = 1) (ρ : DensityState (Fin d))
    (_hpure : ∀ n < R.readout () () d,
      IsPure (((finite_kraus_quantum_channel K hK).choose.mapState)^[n] ρ)),
    ∀ n : ℕ, IsPure (((finite_kraus_quantum_channel K hK).choose.mapState)^[n] ρ)

private theorem actual_law : arena.{u}.Law actual := @finite_pure_prefix_extension.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact mixed_not_pure (h (κ := PUnit.{u+1}) (fun _ => 1) (by simp) mixed
    (fun n hn => (Nat.not_lt_zero n hn).elim) 0)

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_pure_prefix_extension.{u})
    (type_of% (realize signature (fun _ _ n => 2 * n) (fun e => nomatch e))) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Channel.informationUnit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Channel.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ n => 2 * n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FinitePureOrbitExtension,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "body", "domain", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Channel

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ComplexOrder MatrixOrder Matrix

namespace Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Kraus

universe u

set_option quotPrecheck false in
local notation "basisState" => fun {d : ℕ} (i : Fin d) =>
  pureState (Pi.single i 1) (by simp [dotProduct, Pi.single_apply])

private theorem basisState_ne : basisState (0 : Fin 2) ≠ basisState (1 : Fin 2) := by
  intro h
  have he := congrArg (fun ρ : DensityState (Fin 2) => ρ.1 0 0) h
  norm_num [pureState, Matrix.vecMulVec_apply, Pi.single_apply] at he

namespace Lift

@[reducible] def signature : Signature where
  Params := Σ d : ℕ, Σ _ : Module.End ℂ (Fin d → ℂ), ℕ
  State p := Fin p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => (p.2.1 ^ p.2.2) v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {d N : ℕ} {κ : Type u} [Fintype κ]
    (channel : QuantumChannel (Fin d) (Fin d))
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (_hK : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ u, K u * X * (K u).conjTranspose)
    (ρ : ℕ → DensityState (Fin d))
    (_hstep : ∀ n < N, ρ (n + 1) = channel.mapState (ρ n))
    (_hpure : ∀ n ≤ N, IsPure (ρ n)),
    ∃ (A : Module.End ℂ (Fin d → ℂ)) (x : Fin d → ℂ),
      (∃ hx : x ≠ 0, directionState x hx = ρ 0) ∧
      (∀ n ≤ N, R.readout () ⟨d, A, n⟩ x ≠ 0) ∧
      ∀ n < N, ∃ μ : κ → ℂ,
        ∀ u, K u *ᵥ ((A ^ n) x) =
          μ u • ((A ^ (n + 1)) x)

private theorem actual_law : arena.{u}.Law actual := @linear_lift_of_pure_prefix.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨A, x, _, hn, _⟩ := h (N := 0) (identityChannel 1) (fun _ : PUnit.{u+1} => 1)
    (by intro X; simp; rfl) (fun _ => basisState 0)
    (fun n hn => (Nat.not_lt_zero n hn).elim) (fun _ _ => ⟨_, rfl⟩)
  exact hn 0 (Nat.zero_le _) rfl

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨⟨1, LinearMap.id, 0⟩, 0, (fun _ => 1), ?_⟩
    intro h
    have hh := congrFun h 0
    exact zero_ne_one hh

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@linear_lift_of_pure_prefix.{u})
    (type_of% (realize signature (fun _ p v => (p.2.1 ^ p.2.2) v) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Kraus.Lift.informationUnit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Kraus.Lift.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p v => (p.2.1 ^ p.2.2) v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FinitePureOrbitExtension,
    definition := none, coordinates := #[0, 10, 12],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body",
        "arg", "body", "arg", "fn", "arg", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Lift

namespace Transition

@[reducible] def signature : Signature where
  Params := Σ d : ℕ, QuantumChannel (Fin d) (Fin d)
  State p := DensityState (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := DensityState (Fin p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p ρ => p.2.mapState ρ) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p ρ => if h : p.1 = 2 then
    (h.symm ▸ basisState 1 : DensityState (Fin p.1)) else p.2.mapState ρ)
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {κ : Type u} [Fintype κ]
    (channel : QuantumChannel (Fin d) (Fin d))
    (K : κ → Matrix (Fin d) (Fin d) ℂ)
    (_hK : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ u, K u * X * (K u).conjTranspose)
    (v w : Fin d → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (μ : κ → ℂ)
    (_hcol : ∀ u, K u *ᵥ v = μ u • w),
    R.readout () ⟨d, channel⟩ (directionState v hv) = directionState w hw

private theorem actual_law : arena.{u}.Law actual := @map_directionState_of_collinear.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨A, x, ⟨hx, hinit⟩, hnz, hcol⟩ :=
    linear_lift_of_pure_prefix (N := 1) (identityChannel 2)
      (fun _ : PUnit.{u+1} => 1) (by intro X; simp; rfl) (fun _ => basisState 0)
      (fun _ _ => rfl) (fun _ _ => ⟨_, rfl⟩)
  obtain ⟨μ, hμ⟩ := hcol 0 (by omega)
  have hy := hnz 1 (le_refl _)
  have hbad := h (identityChannel 2) (fun _ : PUnit.{u+1} => 1)
    (by intro X; simp; rfl) x ((A ^ 1) x) hx hy μ (by simpa using hμ)
  change basisState 1 = directionState ((A ^ 1) x) hy at hbad
  have hgood := map_directionState_of_collinear (identityChannel 2) (fun _ : PUnit.{u+1} => 1)
    (by intro X; simp; rfl) x ((A ^ 1) x)
    hx hy μ (by simpa using hμ)
  change directionState x hx = directionState ((A ^ 1) x) hy at hgood
  exact basisState_ne (hinit.symm.trans (hgood.trans hbad.symm))

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    exact ⟨⟨2, identityChannel 2⟩, basisState 0, basisState 1, basisState_ne⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@map_directionState_of_collinear.{u})
    (type_of% (realize signature (fun _ p ρ => p.2.mapState ρ) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Kraus.Transition.informationUnit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Kraus.Transition.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p ρ => p.2.mapState ρ) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FinitePureOrbitExtension,
    definition := none, coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Transition

end Reg.D5.S3.Quantum.Dynamics.FinitePureOrbitExtension.Kraus
