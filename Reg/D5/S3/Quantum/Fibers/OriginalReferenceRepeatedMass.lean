import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass
import Reg.Support.DependentFamily

/-! Full-telescope dependent-family declarations for native output mass balance. -/

open scoped ComplexOrder InnerProductSpace BigOperators Matrix TensorProduct
open TraceClassFiniteBlocks MeasureTheory Set
open _root_.D5.S3.Quantum.Fibers
open OriginalReferenceKraus OriginalReferenceOutputMeasure
open OriginalReferenceRepeatedMass OriginalRepeatedPrefix
open OriginalControlComposition
open OriginalControlMarkedJump OriginalMarkedConcatenation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => (-1:ℝ)) (fun a => nomatch a)


private def band : Band := ⟨1/5,3/10,2/5,by norm_num,by norm_num,by norm_num,by norm_num⟩
namespace Native

def theoremLaw (R : Realization signature.{0}) : Prop :=
  ∀ (c a T : ℝ) (k : ℝ → ℝ)
    (hc : c < 1/2) (ha : a ∈ Ioo 0 c)
    (hk : OriginalControl (c,c,1-2*c) T k (fun _ => (0:ℝ)))
    (i : Fin 5) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t),
        IntegrableOn (modeCoefficient c a k i) (Ioc s t) ∧
    R.readout ⟨()⟩ () (∫ u in Ioc s t, modeCoefficient c a k i u) =
      (survival c k s * p c (k s) i - survival c k t * p c (k t) i) / p c a i

abbrev arena : Arena where
  signature := signature.{0}
  Law := theoremLaw

private theorem actual_law : arena.Law actual := by
  intro c a T k hc ha hk i s t hs ht hst
  exact native_mode_balance c a T k hc ha hk i s t hs ht hst

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hk := (band.suffix_facts 0 false).1
  have he := (h band.c band.a 1 band.lateSuffix band.c_lt
    ⟨band.a_pos,band.ab.trans band.bc⟩ hk 0 0 0 (by norm_num) (by norm_num) le_rfl).2
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% (@native_mode_balance)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_mode_balance)
    (type_of% (realize signature.{0} (fun _ _ r => r) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Native.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Native.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{0} (fun _ _ r => r) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Native

namespace Repeated

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : Band) (n : ℕ) (hn : 1 ≤ n) (e : Bool)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1),
        let k := if e then B.early n hn else B.late n hn
    (∀ i : Fin 5,
      (∀ t ∈ Ioc (1:ℝ) 2,
        modeOutput B.c B.a k i rho hpos t =
          ((B.q^n : ℝ) : ℂ) • modeOutput B.c B.a
            (if e then B.earlySuffix else B.lateSuffix) i rho hpos (t-1)) ∧
      (∫ t in Ioc (0:ℝ) 1, modeCoefficient B.c B.a k i t) = 1-B.q^n ∧
      (∫ t in Ioc (1:ℝ) 2, modeCoefficient B.c B.a k i t) = B.q^n*(1-B.q) ∧
      (∫ t in Ioc (0:ℝ) 2, modeCoefficient B.c B.a k i t) = 1-B.q^(n+1) ∧
      (∫ t in Ioc (1:ℝ) 2, modeOutput B.c B.a k i rho hpos t) =
        ((B.q^n*(1-B.q) : ℝ) : ℂ) •
          TraceClass.ofOperator (compression rho.1 i)
            (compression_traceClass (TraceClass.isTraceClass_coe rho) hpos i)) ∧
    (∑ i : Fin 5, ‖∫ t in Ioc (1:ℝ) 2, modeOutput B.c B.a k i rho hpos t‖) =
      B.q^n*(1-B.q)*‖rho‖ ∧
    R.readout ⟨()⟩ () ((∑ i : Fin 5, ‖∫ t in Ioc (0:ℝ) 2, modeOutput B.c B.a k i rho hpos t‖) +
      ‖((B.q^(n+1) : ℝ) : ℂ) • rho‖) = ‖rho‖

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

private theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ B n hn e rho hpos
  exact repeated_reference_completeness B n hn e rho hpos

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hz : 0 ≤ (0 : TraceClass (Blocks (Fin 5)
      (EuclideanSpace ℂ (ULift.{u} Unit)))).1 := le_rfl
  have he := (h (H := EuclideanSpace ℂ (ULift.{u} Unit)) band 1
    (by norm_num) false 0 hz).2.2
  norm_num [rejected, realize] at he

def family : Registration arena.{u} (type_of% (@repeated_reference_completeness.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_reference_completeness.{u})
    (type_of% (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Repeated.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Repeated.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Repeated

namespace Distance

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1),
        (∀ (i : Fin 5) (E : Set ℝ), MeasurableSet E →
      (∫ t in (Ioc (0:ℝ) 1) ∩ E, modeOutput B.c B.a (B.early n hn) i rho hpos t) =
      ∫ t in (Ioc (0:ℝ) 1) ∩ E, modeOutput B.c B.a (B.late n hn) i rho hpos t) ∧
    R.readout ⟨()⟩ () ((∑ i : Fin 5, ∫ t in Ioc (0:ℝ) 2,
      ‖modeOutput B.c B.a (B.early n hn) i rho hpos t -
        modeOutput B.c B.a (B.late n hn) i rho hpos t‖)) =
      2*(B.q^n*(1-B.q))*‖rho‖

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

private theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ B n hn rho hpos
  exact repeated_reference_distance B n hn rho hpos

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hz : 0 ≤ (0 : TraceClass (Blocks (Fin 5)
      (EuclideanSpace ℂ (ULift.{u} Unit)))).1 := le_rfl
  have he := (h (H := EuclideanSpace ℂ (ULift.{u} Unit)) band 1
    (by norm_num) 0 hz).2
  norm_num [rejected, realize] at he

def family : Registration arena.{u} (type_of% (@repeated_reference_distance.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_reference_distance.{u})
    (type_of% (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Distance.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Distance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Distance

namespace Live

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 5) H)) (hpos : 0 ≤ rho.1),
    (∀ (c a k S : ℝ) (z : EuclideanSpace ℂ (Fin 5) ⊗[ℂ] H),
      referenceSuccess c a k S (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (referenceSuccess (H := ℂ) c a k S).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a k S : ℝ) (x : EuclideanSpace ℂ (Fin 5)) (i : Fin 5),
      referenceSuccess (H := ℂ) c a k S x i =
        (successfulKraus c a k S *ᵥ x) i) ∧
    (∀ (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ),
      (liveFailure c a k i rho hpos t).1 =
        (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
          (rho.1.comp (absorbingJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint)) ∧
    (∀ e : Bool, let k := if e then B.early n hn else B.late n hn
      referenceSuccess (H := H) B.c B.a (k 2) (survival B.c k 2) =
        (Real.sqrt (B.q^(n+1)) : ℂ) • ContinuousLinearMap.id ℂ _) ∧
    R.readout ⟨()⟩ () (liveDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos) =
      B.q^n*(1-B.q)*‖rho‖

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

private theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ B n hn rho hpos
  exact repeated_live_operational B n hn rho hpos

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hz : 0 ≤ (0 : TraceClass (Blocks (Fin 5)
      (EuclideanSpace ℂ (ULift.{u} Unit)))).1 := le_rfl
  have he := (h (H := EuclideanSpace ℂ (ULift.{u} Unit)) band 1
    (by norm_num) 0 hz).2.2.2.2
  norm_num [rejected, realize] at he

def family : Registration arena.{u} (type_of% (@repeated_live_operational.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_live_operational.{u})
    (type_of% (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Live.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Live.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


end Live

namespace Stopped

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (B : Band) (n : ℕ) (hn : 1 ≤ n)
    (rho : TraceClass (Blocks (Fin 6) H)) (hpos : 0 ≤ rho.1),
    (∀ (c a k S : ℝ) (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H),
      stoppedSuccess c a k S (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (stoppedSuccess (H := ℂ) c a k S).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a : ℝ) (k : ℝ → ℝ) (i : Fin 5) (t : ℝ),
      (stoppedFailure c a k i rho hpos t).1 =
        (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).comp
          (rho.1.comp (stoppedJump c a (k t) (survival c k t) (jumpRate c k t) i).adjoint)) ∧
    (∀ (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5) (x : H),
      stoppedJump c a k S g i (insertion (5 : Fin 6) x) = 0) ∧
    stoppedSuccessOutput B.c B.a (B.early n hn 2) (survival B.c (B.early n hn) 2) rho =
      stoppedSuccessOutput B.c B.a (B.late n hn 2) (survival B.c (B.late n hn) 2) rho ∧
    R.readout ⟨()⟩ () (stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos) =
      B.q^n*(1-B.q)*liveWeight rho hpos ∧
    (‖rho‖ = 1 → stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) rho hpos ≤
      B.q^n*(1-B.q)) ∧
    (∀ (c a k S : ℝ) (g : Fin 5 → ℝ) (i : Fin 5)
      (z : EuclideanSpace ℂ (Fin 6) ⊗[ℂ] H),
      stoppedJump c a k S g i (tensorCoordinates z) = tensorCoordinates
        (TensorProduct.map (stoppedJump (H := ℂ) c a k S g i).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H) z)) ∧
    (∀ (c a k S : ℝ) (x : Blocks (Fin 6) H),
      (∀ i : Fin 5, stoppedSuccess c a k S x i.castSucc =
        ((Real.sqrt S : ℂ) * (Real.sqrt (p c k i / p c a i) : ℂ)) • x i.castSucc) ∧
      stoppedSuccess c a k S x 5 = x 5) ∧
    (∀ (e : Bool) (i : Fin 5) (E : Set ℝ), MeasurableSet E →
      IntegrableOn (stoppedFailure B.c B.a
        (if e then B.early n hn else B.late n hn) i rho hpos) ((Ioc (0 : ℝ) 2) ∩ E))

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

private theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ B n hn rho hpos
  exact repeated_stopped_operational B n hn rho hpos

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hz : 0 ≤ (0 : TraceClass (Blocks (Fin 6)
      (EuclideanSpace ℂ (ULift.{u} Unit)))).1 := le_rfl
  have he := (h (H := EuclideanSpace ℂ (ULift.{u} Unit)) band 1
    (by norm_num) 0 hz).2.2.2.2.1
  have hw : 0 ≤ liveWeight (0 : TraceClass (Blocks (Fin 6)
      (EuclideanSpace ℂ (ULift.{u} Unit)))) hz :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hq := early_late_native_survival band 1 (by norm_num) 0
  have hp := mul_nonneg (mul_nonneg hq.1.le (sub_nonneg.mpr hq.2.1.le)) hw
  norm_num [rejected, realize] at he
  nlinarith

def family : Registration arena.{u} (type_of% (@repeated_stopped_operational.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_stopped_operational.{u})
    (type_of% (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Stopped.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Stopped.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


end Stopped

namespace Supremum

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ (B : Band) (n : ℕ) (hn : 1 ≤ n),
    (∀ (s : JointState.{u} 5),
      liveDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive =
        B.q^n*(1-B.q)) ∧
    (∃ s : JointState.{u} 6, liveWeight s.rho s.positive = 1 ∧
      stoppedDistance B.c B.a 2 (B.early n hn) (B.late n hn) s.rho s.positive =
        B.q^n*(1-B.q)) ∧
    R.readout ⟨()⟩ () (operationalDistance.{u} B.c B.a 2 (B.early n hn) (B.late n hn)) = B.q^n*(1-B.q) ∧
    (∀ (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ),
      OriginalRepeatedMarkedLaw.eventTV
        (markedLaw B.c B.a beta 2 m theta (B.early n hn))
        (markedLaw B.c B.a beta 2 m theta (B.late n hn)) =
      operationalDistance.{u} B.c B.a 2 (B.early n hn) (B.late n hn))

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

private theorem actual_law : arena.{u}.Law actual := by
  intro B n hn
  exact repeated_operational_supremum.{u} B n hn

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have he := (h band 1 (by norm_num)).2.2.1
  have hq := early_late_native_survival band 1 (by norm_num) 0
  have hp := mul_nonneg hq.1.le (sub_nonneg.mpr hq.2.1.le)
  norm_num [rejected, realize] at he
  nlinarith

def family : Registration arena.{u} (type_of% (@repeated_operational_supremum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@repeated_operational_supremum.{u})
    (type_of% (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Supremum.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass.Supremum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ r => r) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


end Supremum

end Reg.D5.S3.Quantum.Fibers.OriginalReferenceRepeatedMass
