import D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Dependent-family evidence for exact metallic endpoint jets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets

open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelBlocks
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelData
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries Finset
open scoped Matrix


structure Input where
  n : ℕ
  L : ℕ
  k : ℕ → ℕ
  b : ℕ → ℤ
  D : ℕ → PowerSeries ℤ
  Q : ℕ → PowerSeries ℤ
  s : ℕ → ℕ

def claimAt (a : Input) : Prop :=
  let n := a.n
  let L := a.L
  let k := a.k
  let b := a.b
  let D := a.D
  let Q := a.Q
  let s := a.s
  let ν := if n % 2 = 0 then 1 else 2
  let ρ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
  ∀ h : ℕ, ∃ P : Fin 4 → Polynomial ℚ,
    (∀ i, (P i).natDegree ≤ h) ∧ ∀ K : ℕ, 1 ≤ K →
      let p := (K * ν) * L
      s p = s (p - 1) + (n + 1) ∧
      reverseAt (s p) (reverseAt (s p) (Q p)) = Q p ∧
      reverseAt (s p) (reverseAt (s (p - 1)) (Q (p - 1))) =
        X ^ (n + 1) * Q (p - 1) ∧
      (P 0).eval (K : ℚ) = ((coeff h (reverseAt (s p) (Q p)) : ℤ) : ℚ) ∧
      (P 1).eval (K : ℚ) = ((coeff h (reverseAt (s (p - 1)) (Q (p - 1))) : ℤ) : ℚ) ∧
      (h < 2 * K * ρ →
        (P 2).eval (K : ℚ) = ((coeff h (Q p) : ℤ) : ℚ) ∧
        (P 3).eval (K : ℚ) = ((coeff h (X ^ (n + 1) * Q (p - 1)) : ℤ) : ℚ))

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Input) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ a => claimAt a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n L : ℕ) (hn : 1 ≤ n)
    (k : ℕ → ℕ) (b : ℕ → ℤ) (D Q : ℕ → PowerSeries ℤ) (s : ℕ → ℕ)
    (hL : L = if n = 1 then 3 else 6 * n - 4)
    (data : ∀ p, let z := Nat.rec TailState.v₂ (fun _ z => nextState (max n 2) z) p
      k p = (if n = 1 then (if p % 3 = 2 then 1 else 0)
        else (fractionData (max n 2) z).1) ∧
      b p = (if n = 1 then (if p % 3 = 1 then 1 else -1)
        else (fractionData (max n 2) z).2.1) ∧
      D p = (if n = 1 then (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X)
        else (fractionData (max n 2) z).2.2))
    (s0 : s 0 = 0) (ss : ∀ p, s (p + 1) = s p + k p + 1)
    (qzero : Q 0 = 1) (qone : Q 1 = D 0)
    (qstep : ∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
      C (b (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p)
    (support : ∀ p r, s p < r → coeff r (Q p) = 0),
    r.readout () () ⟨n, L, k, b, D, Q, s⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Φ, hΦ, hu, hbase, hgrow, L, k, b, D, Q, s, hL, data,
    hs0, hs, q0, q1, qrec, hdegree, hboundary⟩ := normal_family 1 (by omega)
  exact h 1 L (by omega) k b D Q s hL data hs0 hs q0 q1 qrec (fun p => (hdegree p).2)

def badInput : Input := ⟨0, 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

private theorem bad_claim : ¬ claimAt badInput := by
  intro h
  obtain ⟨P, hp, hv⟩ := h 0
  have hh := (hv 1 (by omega)).1
  norm_num [badInput] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨Φ, hΦ, hu, hbase, hgrow, L, k, b, D, Q, s, hL, data,
    hs0, hs, q0, q1, qrec, hdegree, hboundary⟩ := normal_family 1 (by omega)
  refine ⟨(), badInput, ⟨1, L, k, b, D, Q, s⟩, ?_⟩
  intro h
  apply bad_claim
  exact Eq.mpr h (continuant_endpoint_jets 1 L (by omega) k b D Q s hL data hs0 hs q0 q1 qrec
    (fun p => (hdegree p).2))

def family : Registration arena (type_of% (@continuant_endpoint_jets)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuant_endpoint_jets, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@continuant_endpoint_jets) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets.continuant_endpoint_jets.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => claimAt a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms continuant_endpoint_jets
#print axioms family
#print axioms registration

end Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelEndpointJets
