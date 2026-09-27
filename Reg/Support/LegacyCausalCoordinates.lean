import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

namespace Reg.Support.LegacyCausalCoordinates
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment

abbrev ICData := Bool × Bool × Bool × Bool
abbrev OIData := Bool × (Bool × Bool) × (Bool × Bool)
abbrev UnifiedData := ICData ⊕ OIData
abbrev Code := Bool × Bool × Bool × Bool

def icEquiv : IC.Model ≃ ICData where
  toFun m := (m.outcome false false, m.outcome false true,
    m.outcome true false, m.outcome true true)
  invFun b := ⟨fun u t => if u then (if t then b.2.2.2 else b.2.2.1)
    else (if t then b.2.1 else b.1)⟩
  left_inv := by
    rintro ⟨f⟩
    dsimp
    apply congrArg _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM.mk
    funext u t
    cases u <;> cases t <;> rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

def oiEquiv : OI.Model ≃ OIData where
  toFun m := (match m.direction with | .xCausesY => false | .yCausesX => true,
    (m.root false, m.root true), (m.child false, m.child true))
  invFun b := ⟨if b.1 then .yCausesX else .xCausesY,
    (fun u => if u then b.2.1.2 else b.2.1.1),
    (fun x => if x then b.2.2.2 else b.2.2.1)⟩
  left_inv := by
    rintro ⟨d, f, g⟩
    have hf : (fun b => if b then f true else f false) = f := by
      funext b; cases b <;> rfl
    have hg : (fun b => if b then g true else g false) = g := by
      funext b; cases b <;> rfl
    cases d <;> dsimp <;> rw [hf, hg]
  right_inv := by rintro ⟨a, ⟨b, c⟩, ⟨d, e⟩⟩; cases a <;> rfl

/-- Branch-preserving transport of exactly the original 16 + 32 models. -/
def unifiedEquiv : UnifiedBoolSCM ≃ UnifiedData := Equiv.sumCongr icEquiv oiEquiv

def objectArena : Arena := Arena.ofFintype UnifiedData
def icObjectArena : Arena := Arena.ofFintype ICData

theorem state_count : Fintype.card UnifiedData = 48 := by decide

/-- Two typed readouts share an output type; there is no dependent Eq.rec cast. -/
def pairSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def pairRealization {X Y : Type} [DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (pairSignature X Y) where
  readout := fun i x => Bool.rec (f x) (g x) i
  anchor := Fin.elim0

-- Sorted pairs encode the two original treatment marginals exactly.
def icInt (b : ICData) : Code :=
  (b.1 && b.2.2.1, b.1 || b.2.2.1, b.2.1 && b.2.2.2, b.2.1 || b.2.2.2)
def icCF (b : ICData) : Code := b

def oiObs (b : OIData) : Code :=
  let c := Bool.rec b.2.2.1 b.2.2.2 b.2.1.1
  let d := Bool.rec b.2.2.1 b.2.2.2 b.2.1.2
  Bool.rec (b.2.1.1, c, b.2.1.2, d) (c, b.2.1.1, d, b.2.1.2) b.1

def oiInt (b : OIData) : Code :=
  Bool.rec (b.2.2.1, b.2.2.1, b.2.2.2, b.2.2.2)
    (b.2.1.1, b.2.1.2, b.2.1.1, b.2.1.2) b.1

theorem ic_int_kernel (a b : ICData) :
    icInt a = icInt b ↔ IC.Int (icEquiv.symm a) = IC.Int (icEquiv.symm b) := by
  revert a b
  decide +kernel

theorem ic_cf_kernel (a b : ICData) :
    icCF a = icCF b ↔ IC.CF (icEquiv.symm a) = IC.CF (icEquiv.symm b) := by
  revert a b
  decide +kernel

theorem oi_obs_kernel (a b : OIData) :
    oiObs a = oiObs b ↔ OI.Obs (oiEquiv.symm a) = OI.Obs (oiEquiv.symm b) := by
  revert a b
  decide +kernel

theorem oi_int_kernel (a b : OIData) :
    oiInt a = oiInt b ↔ OI.Int (oiEquiv.symm a) = OI.Int (oiEquiv.symm b) := by
  revert a b
  decide +kernel

def icCoarse : UnifiedData → Option Code
  | .inl b => some (icInt b)
  | .inr _ => none
def icFine : UnifiedData → Option Code
  | .inl b => some (icCF b)
  | .inr _ => none
def oiCoarse : UnifiedData → Option Code
  | .inl _ => none
  | .inr b => some (oiObs b)
def oiFine : UnifiedData → Option Code
  | .inl _ => none
  | .inr b => some (oiInt b)

def icActual := pairRealization icCoarse icFine
def oiActual := pairRealization oiCoarse oiFine
def localActual := pairRealization icInt icCF

def restrictedArena (A : Arena) (Y E : Type) [DecidableEq Y]
    (embed : E → A.State) : PrimitiveLawArena where
  toArena := A
  signature := pairSignature A.State Y
  Law r := ∃ a b : E, r.readout false (embed a) = r.readout false (embed b) ∧
    r.readout true (embed a) ≠ r.readout true (embed b)

def icLawArena := restrictedArena objectArena (Option Code) ICData Sum.inl
def oiLawArena := restrictedArena objectArena (Option Code) OIData Sum.inr
def localLawArena := restrictedArena icObjectArena Code ICData id

/-- Source domains remain the original SCMs; the finite state transport and
branch relations are certified by the equivalences and readout lemmas below. -/
def icDomainArena : ObjectDomainArena where
  toPrimitiveLawArena := icLawArena
  Domain := IC.Model

def oiDomainArena : ObjectDomainArena where
  toPrimitiveLawArena := oiLawArena
  Domain := OI.Model

def localDomainArena : ObjectDomainArena where
  toPrimitiveLawArena := localLawArena
  Domain := IC.Model

/-- Vary either relation on the same embedded branch, with every other slot fixed. -/
theorem restricted_sensitivity (A : Arena) (Y E : Type) [DecidableEq Y]
    (embed : E → A.State) (f g : A.State → Y)
    (h : (restrictedArena A Y E embed).Law (pairRealization f g)) :
    FiniteSlotSensitivity (restrictedArena A Y E embed) := by
  constructor
  · intro i
    cases i
    · refine ⟨pairRealization f g, pairRealization g g, ?_, ?_, ?_⟩
      · intro j different
        cases j
        · exact (different rfl).elim
        · rfl
      · intro j; exact Fin.elim0 j
      · constructor
        · intro _ bad
          obtain ⟨a, b, same, different⟩ := bad
          exact different same
        · intro _; exact h
    · refine ⟨pairRealization f g, pairRealization f f, ?_, ?_, ?_⟩
      · intro j different
        cases j
        · rfl
        · exact (different rfl).elim
      · intro j; exact Fin.elim0 j
      · constructor
        · intro _ bad
          obtain ⟨a, b, same, different⟩ := bad
          exact different same
        · intro _; exact h
  · intro i; exact Fin.elim0 i

theorem ic_bridge : LegacyPrimitiveRealization icLawArena
    (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N) icActual := by
  constructor
  change (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N) ↔ _
  constructor
  · rintro ⟨M, N, h, h'⟩
    refine ⟨icEquiv M, icEquiv N, ?_, ?_⟩
    · exact congrArg some ((ic_int_kernel _ _).mpr (by simpa using h))
    · intro e
      apply h'
      simpa using (ic_cf_kernel _ _).mp (Option.some.inj e)
  · rintro ⟨a, b, h, h'⟩
    exact ⟨icEquiv.symm a, icEquiv.symm b,
      (ic_int_kernel _ _).mp (Option.some.inj h),
      fun e => h' (congrArg some ((ic_cf_kernel _ _).mpr e))⟩

theorem oi_bridge : LegacyPrimitiveRealization oiLawArena
    (∃ M N : OI.Model, OI.Obs M = OI.Obs N ∧ OI.Int M ≠ OI.Int N) oiActual := by
  constructor
  constructor
  · rintro ⟨M, N, h, h'⟩
    refine ⟨oiEquiv M, oiEquiv N, ?_, ?_⟩
    · exact congrArg some ((oi_obs_kernel _ _).mpr (by simpa using h))
    · intro e
      apply h'
      simpa using (oi_int_kernel _ _).mp (Option.some.inj e)
  · rintro ⟨a, b, h, h'⟩
    exact ⟨oiEquiv.symm a, oiEquiv.symm b,
      (oi_obs_kernel _ _).mp (Option.some.inj h),
      fun e => h' (congrArg some ((oi_int_kernel _ _).mpr e))⟩

theorem local_bridge : LegacyPrimitiveRealization localLawArena
    (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N) localActual := by
  constructor
  constructor
  · rintro ⟨M, N, h, h'⟩
    refine ⟨icEquiv M, icEquiv N, (ic_int_kernel _ _).mpr (by simpa using h), ?_⟩
    intro e
    apply h'
    simpa using (ic_cf_kernel (icEquiv M) (icEquiv N)).mp e
  · rintro ⟨a, b, h, h'⟩
    exact ⟨icEquiv.symm a, icEquiv.symm b,
      (ic_int_kernel _ _).mp h, fun e => h' ((ic_cf_kernel _ _).mpr e)⟩

theorem ic_positive : icLawArena.Law icActual :=
  ic_bridge.equivalence.mp
    _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual

theorem oi_positive : oiLawArena.Law oiActual :=
  oi_bridge.equivalence.mp
    _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention

theorem local_positive : localLawArena.Law localActual :=
  local_bridge.equivalence.mp
    _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual

theorem ic_variation : icLawArena.Law icActual ∧
    ¬ icLawArena.Law (pairRealization icCoarse icCoarse) := by
  refine ⟨ic_positive, ?_⟩
  rintro ⟨a, b, same, different⟩
  exact different same

theorem oi_variation : oiLawArena.Law oiActual ∧
    ¬ oiLawArena.Law (pairRealization oiCoarse oiCoarse) := by
  refine ⟨oi_positive, ?_⟩
  rintro ⟨a, b, same, different⟩
  exact different same

theorem local_variation : localLawArena.Law localActual ∧
    ¬ localLawArena.Law (pairRealization icInt icInt) := by
  refine ⟨local_positive, ?_⟩
  rintro ⟨a, b, same, different⟩
  exact different same

theorem ic_sensitivity : FiniteSlotSensitivity icLawArena :=
  restricted_sensitivity objectArena (Option Code) ICData Sum.inl icCoarse icFine ic_positive

theorem oi_sensitivity : FiniteSlotSensitivity oiLawArena :=
  restricted_sensitivity objectArena (Option Code) OIData Sum.inr oiCoarse oiFine oi_positive

theorem local_sensitivity : FiniteSlotSensitivity localLawArena :=
  restricted_sensitivity icObjectArena Code ICData id icInt icCF local_positive

theorem ic_dependence : ∀ i : Bool, ∃ x y : UnifiedData,
    icActual.readout i x ≠ icActual.readout i y := by
  intro i
  refine ⟨.inl (false, false, false, false), .inl (true, true, true, true), ?_⟩
  cases i <;> change (some (false, false, false, false) : Option Code) ≠
    some (true, true, true, true) <;> decide

theorem oi_dependence : ∀ i : Bool, ∃ x y : UnifiedData,
    oiActual.readout i x ≠ oiActual.readout i y := by
  intro i
  refine ⟨.inr (false, (false, false), (false, false)),
    .inr (false, (true, true), (true, true)), ?_⟩
  cases i <;> change (some (false, false, false, false) : Option Code) ≠
    some (true, true, true, true) <;> decide

theorem local_dependence : ∀ i : Bool, ∃ x y : ICData,
    localActual.readout i x ≠ localActual.readout i y := by
  intro i
  refine ⟨(false, false, false, false), (true, true, true, true), ?_⟩
  cases i <;> change (false, false, false, false) ≠ (true, true, true, true) <;> decide

/-- Both off-branch readouts are still exactly None. -/
theorem ic_opposite_branch (b : OIData) :
    icCoarse (.inr b) = none ∧ icFine (.inr b) = none := ⟨rfl, rfl⟩
theorem oi_opposite_branch (b : ICData) :
    oiCoarse (.inl b) = none ∧ oiFine (.inl b) = none := ⟨rfl, rfl⟩

/-- Each individual readout relation, including cross-branch pairs, is preserved. -/
theorem ic_coarse_transport (x y : UnifiedData) :
    icCoarse x = icCoarse y ↔
      interventionCounterfactualUnifiedRealization.readout .intervention (unifiedEquiv.symm x) =
      interventionCounterfactualUnifiedRealization.readout .intervention (unifiedEquiv.symm y) := by
  cases x <;> cases y <;>
    simp [icCoarse, unifiedEquiv, interventionCounterfactualUnifiedRealization, ic_int_kernel] <;>
    first | rfl | exact ⟨congrArg some, Option.some.inj⟩

theorem ic_fine_transport (x y : UnifiedData) :
    icFine x = icFine y ↔
      interventionCounterfactualUnifiedRealization.readout .counterfactual (unifiedEquiv.symm x) =
      interventionCounterfactualUnifiedRealization.readout .counterfactual (unifiedEquiv.symm y) := by
  cases x <;> cases y <;>
    simp [icFine, unifiedEquiv, interventionCounterfactualUnifiedRealization, ic_cf_kernel] <;>
    first | rfl | exact ⟨congrArg some, Option.some.inj⟩

theorem oi_coarse_transport (x y : UnifiedData) :
    oiCoarse x = oiCoarse y ↔
      observationInterventionUnifiedRealization.readout .observation (unifiedEquiv.symm x) =
      observationInterventionUnifiedRealization.readout .observation (unifiedEquiv.symm y) := by
  cases x <;> cases y <;>
    simp [oiCoarse, unifiedEquiv, observationInterventionUnifiedRealization, oi_obs_kernel] <;>
    first | rfl | exact ⟨congrArg some, Option.some.inj⟩

theorem oi_fine_transport (x y : UnifiedData) :
    oiFine x = oiFine y ↔
      observationInterventionUnifiedRealization.readout .intervention (unifiedEquiv.symm x) =
      observationInterventionUnifiedRealization.readout .intervention (unifiedEquiv.symm y) := by
  cases x <;> cases y <;>
    simp [oiFine, unifiedEquiv, observationInterventionUnifiedRealization, oi_int_kernel] <;>
    first | rfl | exact ⟨congrArg some, Option.some.inj⟩

#print axioms ic_coarse_transport
#print axioms ic_fine_transport
#print axioms oi_coarse_transport
#print axioms oi_fine_transport
#print axioms ic_bridge
#print axioms oi_bridge
#print axioms local_bridge
#print axioms ic_sensitivity
#print axioms oi_sensitivity
#print axioms local_sensitivity
#print axioms ic_dependence
#print axioms oi_dependence
#print axioms local_dependence

end Reg.Support.LegacyCausalCoordinates

open Reg.Support.LegacyCausalCoordinates LeanInformationAudit
register_information_template pairRealization
