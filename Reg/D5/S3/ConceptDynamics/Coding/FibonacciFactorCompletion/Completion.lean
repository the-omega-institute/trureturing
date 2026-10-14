import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal52
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ xs => listWeight xs) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (model : Model)
    (xs : List Return) (hK : 1 ≤ K)
    (hw : GuardTrace K d false .high xs (initial .high model)),
    let ω := uPadding (executionWord xs)
    pastState ω 0 = hSide .high ∧
    (∀ p : ℕ, p ≤ xs.length →
      execute .high (xs.take p) (initial .high model) <
        pastState ω ((executionWord (xs.take p)).length : ℤ)) ∧
    ω ∈ AuxiliaryLanguage K d ∧ Occurs ω (executionWord xs) ∧
    AuxiliaryFactor K d (executionWord xs) ∧
    wordWeight (executionWord xs) = r.readout () () xs


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := h 1 0 .original [] (by decide) (by trivial)
  have impossible := bad.2.2.2.2.2
  change 0 = 1 at impossible
  omega

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.auxiliary_lower_padding) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.auxiliary_lower_padding, rejected, rejected_law⟩
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
    refine ⟨(), [], [⟨1, 1, by decide, by decide⟩], ?_⟩
    norm_num [actual, realize, listWeight]

def auxiliary_lower_padding_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.auxiliary_lower_padding)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ xs => listWeight xs) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal52.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal52.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ xs => listWeight xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms auxiliary_lower_padding_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal52


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal55
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ xs => listWeight xs) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))),
    ∃ R : Return, R.r = 1 ∧
      ∀ (model : Model) (w : List CuLetter),
        AuxiliaryFactor K ((lam - b) / g ^ 2 / chi ^ K) w → CuLetter.c ∈ w →
        ∃ (a : ℕ) (first : Return) (rest : List Return),
          let filled := if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w
          let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
          let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
          filled = List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
          (∀ (a' : ℕ) (xs' : List Return),
            filled = List.replicate a' CuLetter.u ++ executionWord xs' →
            a' = a ∧ xs' = first :: rest) ∧
          ActualPairSupply model o b .strict (reset :: extra :: rest) ∧
          executionWord (reset :: extra :: rest) =
            CuLetter.c :: (List.replicate (R.m + a) CuLetter.u ++
              List.replicate first.r CuLetter.c ++
              List.replicate (first.m + 1) CuLetter.u ++ executionWord rest) ∧
          r.readout () () (reset :: extra :: rest) = wordWeight w + (20 + 6 * R.m) +
            (if w.getLast? = some CuLetter.c then 12 else 6)

theorem strict_interval_inhabited : ∃ b : ℝ,
    lam - g ^ 2 * chi ^ 2 * hSide .high < b ∧
    b < lam - g ^ 2 * chi ^ 2 * (aSide .high / (1 - rho * chi ^ 2)) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have g1 : g < 1 := by dsimp [g, t]; nlinarith
  have rp : 0 < rho := pow_pos gp 6
  have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide : (6 : ℕ) ≠ 0)
  have cp : 0 < chi := pow_pos gp 20
  have c1 : chi < 1 := pow_lt_one₀ gp.le g1 (by decide : (20 : ℕ) ≠ 0)
  have c2p : 0 < chi ^ 2 := pow_pos cp 2
  have c2l : chi ^ 2 < 1 := pow_lt_one₀ cp.le c1 (by decide : (2 : ℕ) ≠ 0)
  have prodl : rho * chi ^ 2 < rho := by nlinarith
  have dp : 0 < 1 - rho * chi ^ 2 := by linarith
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have fh : aSide .high / (1 - rho * chi ^ 2) < hSide .high := by
    apply (div_lt_iff₀ dp).mpr
    dsimp [aSide]
    nlinarith [mul_lt_mul_of_pos_right prodl hp]
  have qp : 0 < g ^ 2 * chi ^ 2 := mul_pos (pow_pos gp 2) c2p
  let L := lam - g ^ 2 * chi ^ 2 * hSide .high
  let U := lam - g ^ 2 * chi ^ 2 * (aSide .high / (1 - rho * chi ^ 2))
  have lu : L < U := by
    dsimp [L, U]
    nlinarith [mul_lt_mul_of_pos_left fh qp]
  refine ⟨(L + U) / 2, ?_, ?_⟩ <;> change _ < _ <;> dsimp [L, U] at * <;> linarith

theorem single_c_factor (d : ℝ) : AuxiliaryFactor 2 d [CuLetter.c] := by
  let ω : ℤ → CuLetter := fun i => if i = 0 then .c else .u
  have hc (i : ℤ) (hi : ω i = .c) : i = 0 := by
    by_contra h
    simp [ω, h] at hi
  refine ⟨ω, ⟨?_, ?_⟩, 0, ?_⟩
  · intro i allc
    have h0 := hc i (by simpa using allc ⟨0, by decide⟩)
    have h1 := hc (i + 1) (by simpa using allc ⟨1, by decide⟩)
    omega
  · intro i allc
    have h0 := hc i (by simpa using allc ⟨0, by decide⟩)
    have h1 := hc (i - 1) (by simpa using allc ⟨1, by decide⟩)
    omega
  · intro k
    have hk : k.val = 0 := by
      have hk' : k.val < 1 := k.isLt
      omega
    simp [ω, hk]

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hqb, hbp⟩ := strict_interval_inhabited
  obtain ⟨R, hr, hR⟩ := h (fun _ => false) b 2 (by decide) hqb hbp
  obtain ⟨a, first, rest, hall⟩ := hR .original [.c]
    (single_c_factor ((lam - b) / g ^ 2 / chi ^ 2)) (by simp)
  have impossible := hall.2.2.2.2
  simp [rejected, realize, wordWeight] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.auxiliary_factor_upper_completion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.auxiliary_factor_upper_completion, rejected, rejected_law⟩
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
    refine ⟨(), [], [⟨1, 1, by decide, by decide⟩], ?_⟩
    norm_num [actual, realize, listWeight]

def auxiliary_factor_upper_completion_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.auxiliary_factor_upper_completion)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ xs => listWeight xs) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal55.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal55.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ xs => listWeight xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms auxiliary_factor_upper_completion_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal55

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal56
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => List Return
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => List Return
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => []) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (j : Side) (model : Model)
    (xs ys : List Return) (hweight : listWeight xs = listWeight ys)
    (hsource : source j model xs = source j model ys),
    r.readout () () xs = ys

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let r : Return := ⟨1, 1, by decide, by decide⟩
  have bad := h .high .original [r] [r] rfl rfl
  simp [rejected, realize] at bad

def evidence : Registration sourceArena
    (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.actual_source_address_injection) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.actual_source_address_injection,
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
    let r : Return := ⟨1, 1, by decide, by decide⟩
    refine ⟨(), [], [r], ?_⟩
    simp [actual, realize, r]

def actual_source_address_injection_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.actual_source_address_injection)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal56.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal56.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_source_address_injection_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion.ExactOriginal56
