import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.GainRayCriticalSpan
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Linear.GainRayCriticalSpan
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u

abbrev growthSignature : Signature where
  Params := Type u
  State p := Submodule ℝ (p → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def growthActual : Realization growthSignature.{u} :=
  realize growthSignature (fun _ _ K => Module.finrank ℝ K) (fun e => nomatch e)

def growthRejected : Realization growthSignature.{u} :=
  realize growthSignature (fun _ _ _ => 0) (fun e => nomatch e)

def growthArena : Arena where
  signature := growthSignature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι]
    (t : ι → ℝ) (_ht : Function.Injective t) (V K : Submodule ℝ (ι → ℝ))
    (a : ι → ℝ) (_ha : a ∈ V) (_hna : ∀ i, a i ≠ 0) (d : ℕ)
    (_h : ∀ v ∈ V, ∀ j ≤ d, (fun i => v i * t i ^ j) ∈ K),
    min (Fintype.card ι) (Module.finrank ℝ V + d) ≤ R.readout () ι K

theorem growthRejected_law : ¬ growthArena.{u}.Law growthRejected := by
  intro h
  let ι := ULift.{u} (Fin 1)
  have hh := h (ι := ι) (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
    ⊤ ⊤ (fun _ => 1) (by trivial) (by intro i; exact one_ne_zero) 0 (by intros; trivial)
  norm_num [growthRejected, realize, ι, growthSignature] at hh

def growthRegistration : Registration growthArena.{u} (growthArena.Law growthActual) where
  actual := growthActual
  bridge := Iff.rfl
  variation := ⟨weighted_polynomial_span_growth, growthRejected, growthRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨growthRejected, ?_, rfl, growthRejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨ULift.{u} (Fin 1), (⊥ : Submodule ℝ (ULift.{u} (Fin 1) → ℝ)),
      (⊤ : Submodule ℝ (ULift.{u} (Fin 1) → ℝ)), ?_⟩
    change Module.finrank ℝ (⊥ : Submodule ℝ (ULift.{u} (Fin 1) → ℝ)) ≠
      Module.finrank ℝ (⊤ : Submodule ℝ (ULift.{u} (Fin 1) → ℝ))
    simp

def growth : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@weighted_polynomial_span_growth.{u})
    (type_of% (realize growthSignature.{u} (fun _ _ K => Module.finrank ℝ K)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayCriticalSpan.growthUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayCriticalSpan.growthRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨growthArena⟩,
  objectArena := .source ⟨growthArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source growthArena ⟨growthRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize growthSignature.{u} (fun _ _ K => Module.finrank ℝ K)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Linear.GainRayCriticalSpan, definition := none, coordinates := #[0], readouts := #[{ path := #["body","body","body","body","body","body", "body","body","body","body","body","arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

open scoped Matrix

abbrev scalarSignature : Signature where
  Params := (d : ℕ) × List Bool
  State p := Readout p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Mat →ₗ[ℝ] Matrix (Fin (p.1+1)) (Fin (p.1+1)) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def scalarActual : Realization scalarSignature :=
  realize scalarSignature (fun _ p C => response p.1 p.2 C) (fun e => nomatch e)

def scalarRejected : Realization scalarSignature :=
  realize scalarSignature (fun _ p C =>
    (scalarFunctional p.1 p.2 C).smulRight (1 : Matrix _ _ ℝ)) (fun e => nomatch e)

def scalarArena : Arena where
  signature := scalarSignature
  Law R := ∀ (d : ℕ) (_hd : 1 ≤ d) (w : List Bool)
    (_hM : false ∈ w) (_hJ : true ∈ w) (_hN : w.length+1 = 2*(d+1)+1)
    (C : Readout d w) (_hb : C.mulVec (fun _ => 1) = 0)
    (_he : ∀ T : Mat, R.readout () ⟨d,w⟩ C T =
      scalarFunctional d w C T • (1 : Matrix _ _ ℝ))
    (_hell : scalarFunctional d w C ≠ 0),
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) = 3

def auditWord : List Bool := [false,true,false,true]

def auditReadout : Readout 1 auditWord :=
  !![1,-1,0,0,0; 0,0,0,0,0]

def auditMatrices : Fin 5 → Mat :=
  ![!![1,0;0,1], !![0,1;1,1], !![1,1;0,1], !![0,1;1,2], !![1,2;0,1]]

theorem audit_prefix (i : Fin 5) : acquisition (auditWord.take i.val) = auditMatrices i := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [auditWord,auditMatrices,acquisition,Raw,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem audit_drift : auditReadout.mulVec (fun _ => 1) = 0 := by
  classical
  ext k
  change (∑ i : Fin 5, auditReadout k i * 1) = 0
  fin_cases k <;> norm_num [auditReadout,Fin.sum_univ_succ]

theorem audit_scale : scalarFunctional 1 auditWord auditReadout (1 : Mat) = 1 := by
  classical
  unfold scalarFunctional response
  simp only [LinearMap.coe_mk,AddHom.coe_mk,Matrix.mul_apply,responseMatrix]
  change (∑ i : Fin 5, auditReadout 0 i *
    (Matrix.trace (acquisition (auditWord.take i.val) * 1) * (i.val : ℝ)^0)) = 1
  simp only [audit_prefix]
  norm_num [auditMatrices,auditReadout,Fin.sum_univ_succ,Matrix.trace,Matrix.diag,Fin.sum_univ_two]

theorem audit_span : 4 ≤ Module.finrank ℝ (Submodule.span ℝ
    (Set.range (fun i : Fin (auditWord.length+1) => acquisition (auditWord.take i.val)))) := by
  let H := Submodule.span ℝ
    (Set.range (fun i : Fin (auditWord.length+1) => acquisition (auditWord.take i.val)))
  let v : Fin 4 → H := fun i => ⟨auditMatrices ⟨i.val,by omega⟩,
    Submodule.subset_span ⟨⟨i.val,by simp [auditWord]; omega⟩,audit_prefix _⟩⟩
  have hind : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp H.subtype
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have h00 := congrArg (fun A : Mat => A 0 0) hc
    have h01 := congrArg (fun A : Mat => A 0 1) hc
    have h10 := congrArg (fun A : Mat => A 1 0) hc
    have h11 := congrArg (fun A : Mat => A 1 1) hc
    simp [v,auditMatrices,Fin.sum_univ_succ] at h00 h01 h10 h11
    have hc0 : c 0 = 0 := by linarith
    have hc1 : c 1 = 0 := by linarith
    have hc2 : c 2 = 0 := by linarith
    have hc3 : c 3 = 0 := by linarith
    intro i
    fin_cases i <;> assumption
  simpa using hind.fintype_card_le_finrank

theorem scalarRejected_law : ¬ scalarArena.Law scalarRejected := by
  intro h
  have hell : scalarFunctional 1 auditWord auditReadout ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : Mat →ₗ[ℝ] ℝ => f 1) hz
    simpa [audit_scale] using hh
  have hh := h 1 (by omega) auditWord (by simp [auditWord]) (by simp [auditWord])
    rfl auditReadout audit_drift (fun _ => rfl) hell
  have hs := audit_span
  omega

def scalarRegistration : Registration scalarArena (scalarArena.Law scalarActual) where
  actual := scalarActual
  bridge := Iff.rfl
  variation := ⟨critical_scalar_span,scalarRejected,scalarRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarRejected, ?_, rfl, scalarRejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1,auditWord⟩, auditReadout, (0 : Readout 1 auditWord), ?_⟩
    intro heq
    have hh := congrArg (fun f : Mat →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ => f 1 0 0) heq
    change scalarFunctional 1 auditWord auditReadout 1 = response 1 auditWord 0 1 0 0 at hh
    rw [audit_scale] at hh
    norm_num [response] at hh

def scalar : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@critical_scalar_span)
    (type_of% (realize scalarSignature (fun _ p C => response p.1 p.2 C)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayCriticalSpan.scalarUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayCriticalSpan.scalarRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨scalarArena⟩,
  objectArena := .source ⟨scalarArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source scalarArena ⟨scalarRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize scalarSignature (fun _ p C => response p.1 p.2 C)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Linear.GainRayCriticalSpan, definition := none, coordinates := #[0,2], readouts := #[{ path := #["body","body","body","body","body","body","body","body","domain","body","fn","arg","fn","arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Observer.Linear.GainRayCriticalSpan
