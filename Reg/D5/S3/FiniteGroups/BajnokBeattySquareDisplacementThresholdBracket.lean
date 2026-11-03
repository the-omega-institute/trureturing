/- Same-delivery registration attempt. No binding acceptance.
The complete signed infinite parameter telescope and all natural valid states
are retained. Exactly two roles read the actual complete quotient counts.
Source-selection and full-telescope occurrence binding remain unfinished:
https://github.com/the-omega-institute/trureturing/issues/25856 .
No judge changes, audit gate, finite fixture Law or validation claim. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
import Reg.Support.DependentFamily

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S0.Tower.DBonacci.PerronRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

private noncomputable def correctedCenter (p q : ℤ) : ℝ :=
  let nu : ℝ := (q : ℝ)^2
  let beta := dbonacciPerronRoot (q.toNat^2)
  let sigma := Real.log beta
  let alpha := (nu-1)/(4*(q : ℝ)*sigma)
  let d := ((nu+1)*sigma/(6*(q : ℝ)*(nu-1)))*
    (((nu^2+1)*beta-2*nu^2)/((nu+1)*beta-2*nu))
  alpha*(p : ℝ)+1/(2*(q : ℝ))+(d-1/(2*(q : ℝ)))/(p : ℝ)

private noncomputable def radius (p q : ℤ) : ℝ := (q : ℝ)/(10*(p : ℝ)^3)

abbrev thresholdSignature : Signature where
  Params := {pq : ℤ × ℤ // 5 ≤ pq.1 ∧ Odd pq.1 ∧ 3 ≤ pq.2 ∧ Odd pq.2}
  State pq := {t : ℕ // ((pq.1.2+1)/2).toNat ≤ t}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def thresholdActual : Realization thresholdSignature :=
  realize thresholdSignature
    (fun i pq t => if i = 0 then (square_return_pair pq.1.1 pq.1.2 t.1).1
      else (square_return_pair pq.1.1 pq.1.2 t.1).2)
    (fun e => nomatch e)

noncomputable def thresholdRejected (i : Fin 2) : Realization thresholdSignature :=
  realize thresholdSignature
    (fun j pq t => if j = i then 0 else thresholdActual.readout j pq t)
    (fun e => nomatch e)

abbrev thresholdArena : Arena where
  signature := thresholdSignature
  Law R := ∀ (p q : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q),
    let pq : thresholdSignature.Params := ⟨(p,q),hp5,hpo,hq3,hqo⟩
    let tmin := ((q+1)/2).toNat
    let tlate := ((q*p+1)/2).toNat
    ∃! T : ℕ, ∃ hT : tmin < T,
      (∀ (t : ℕ) (ht : tmin ≤ t), t < T →
        R.readout 1 pq ⟨t,ht⟩ < R.readout 0 pq ⟨t,ht⟩) ∧
      R.readout 0 pq ⟨T,hT.le⟩ ≤ R.readout 1 pq ⟨T,hT.le⟩ ∧
      (∀ (t : ℕ) (hTt : T < t),
        R.readout 0 pq ⟨t,(hT.trans hTt).le⟩ <
          R.readout 1 pq ⟨t,(hT.trans hTt).le⟩) ∧
      T ≤ tlate ∧ correctedCenter p q-radius p q < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil (correctedCenter p q+radius p q)

private theorem actual_bridge : (type_of% actual_square_displacement_threshold_bracket) ↔
    thresholdArena.Law thresholdActual := by
  constructor
  · intro h p q hp5 hpo hq3 hqo
    obtain ⟨T,⟨hT,hbefore,hat,hafter,hlate,hlo,hhi⟩,huniq⟩ := h p q hp5 hpo hq3 hqo
    refine ⟨T,⟨hT,hbefore,hat,hafter,hlate,hlo,hhi⟩,?_⟩
    intro U hU
    obtain ⟨hU,hbefore,hat,hafter,hlate,hlo,hhi⟩ := hU
    exact huniq U ⟨hU,hbefore,hat,hafter,hlate,hlo,hhi⟩
  · intro h p q hp5 hpo hq3 hqo
    obtain ⟨T,⟨hT,hbefore,hat,hafter,hlate,hlo,hhi⟩,huniq⟩ := h p q hp5 hpo hq3 hqo
    refine ⟨T,⟨hT,hbefore,hat,hafter,hlate,hlo,hhi⟩,?_⟩
    intro U hU
    obtain ⟨hU,hbefore,hat,hafter,hlate,hlo,hhi⟩ := hU
    exact huniq U ⟨hU,hbefore,hat,hafter,hlate,hlo,hhi⟩

private theorem actual_law : thresholdArena.Law thresholdActual :=
  actual_bridge.mp actual_square_displacement_threshold_bracket

private theorem rejected_law (i : Fin 2) : ¬ thresholdArena.Law (thresholdRejected i) := by
  intro h
  obtain ⟨T,hT,_⟩ := h 5 3 (by norm_num) (by decide) (by norm_num) (by decide)
  obtain ⟨hTmin,hbefore,hat,hafter,hlate,hlo,hhi⟩ := hT
  fin_cases i
  · have hh := hbefore 2 (by norm_num) hTmin
    have hn : (square_return_pair 5 3 2).2 < 0 := by
      simpa [thresholdRejected,thresholdActual,realize] using hh
    omega
  · have hh := hafter (T+1) (by omega)
    have hn : (square_return_pair 5 3 (T+1)).1 < 0 := by
      simpa [thresholdRejected,thresholdActual,realize] using hh
    omega

-- These actual states prove dependence only. They do not replace the Law.
set_option maxRecDepth 10000 in
private theorem actual_dependence : ObservationalDependence thresholdSignature thresholdActual := by
  intro i
  let pq : thresholdSignature.Params := ⟨(5,3),by decide⟩
  refine ⟨pq,⟨4,by decide⟩,⟨5,by decide⟩,?_⟩
  have h4 := actual_counts 2 1 4 (by norm_num) (by norm_num) (by norm_num)
  have h5 := actual_counts 2 1 5 (by norm_num) (by norm_num) (by norm_num)
  change (square_return_pair 5 3 4).1 = 2*(Nat.choose 115 60+Nat.choose 115 80) ∧
    (square_return_pair 5 3 4).2 = 4*Nat.choose 115 65 at h4
  change (square_return_pair 5 3 5).1 = 2*(Nat.choose 145 75+Nat.choose 145 95) ∧
    (square_return_pair 5 3 5).2 = 4*Nat.choose 145 80 at h5
  fin_cases i
  · change (square_return_pair 5 3 4).1 ≠ (square_return_pair 5 3 5).1
    rw [h4.1,h5.1]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 60 ≤ 115),
      Nat.choose_eq_factorial_div_factorial (by decide : 80 ≤ 115),
      Nat.choose_eq_factorial_div_factorial (by decide : 75 ≤ 145),
      Nat.choose_eq_factorial_div_factorial (by decide : 95 ≤ 145),Nat.factorial]
  · change (square_return_pair 5 3 4).2 ≠ (square_return_pair 5 3 5).2
    rw [h4.2,h5.2]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 65 ≤ 115),
      Nat.choose_eq_factorial_div_factorial (by decide : 80 ≤ 145),Nat.factorial]

noncomputable def thresholdSource : Registration thresholdArena
    (type_of% actual_square_displacement_threshold_bracket) where
  actual := thresholdActual
  bridge := actual_bridge
  variation := ⟨actual_law,thresholdRejected 0,rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨thresholdRejected i,?_,rfl,rejected_law i⟩
      intro j hj
      funext pq t
      simp [thresholdRejected,realize,hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def thresholdRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_square_displacement_threshold_bracket)
      (Realization thresholdSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket.actual_square_displacement_threshold_bracket.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket.thresholdSource
  realizationSource := none
  generated := false
  arena := .source ⟨thresholdArena⟩
  objectArena := .source ⟨thresholdArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source thresholdArena ⟨thresholdSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize thresholdSignature
    (fun i pq t => if i = 0 then (square_return_pair pq.1.1 pq.1.2 t.1).1
      else (square_return_pair pq.1.1 pq.1.2 t.1).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket
