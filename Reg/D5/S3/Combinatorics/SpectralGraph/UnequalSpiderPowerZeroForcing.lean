import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing
import Reg.Support.SingleDependentReadout

/-! # Escape Registration for Unequal-Leg Spider Power Zero Forcing -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing

open _root_.D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
  (IsZeroForcing zeroForcingNumber)
open _root_.D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Matrix
open scoped BigOperators Matrix

namespace SlidingWindow

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    ∀ k : ℕ,
      (∀ x : ℕ → ℝ, x ∈ slidingWindowSpace k ↔
        ∀ s : ℕ, x (s + k) = - ∑ t ∈ Finset.range k, x (s + t)) ∧
      (∀ (x : slidingWindowSpace k) (i : Fin k), slidingWindowEquiv k x i = x.1 i.val) ∧
      (∀ v : Fin k → ℝ, ∃! x : ℕ → ℝ, x ∈ slidingWindowSpace k ∧ ∀ i : Fin k, x i.val = v i) ∧
      Module.finrank ℝ (slidingWindowSpace k) = O.readout () () k ∧
      (∀ L : ℕ, k + 1 ≤ L → ∀ x ∈ slidingWindowSpace k,
        windowMatrix k L *ᵥ (fun d : Fin L => x d.val) = 0) ∧
      (∀ L : ℕ, k + 1 ≤ L → ∀ d e : Fin L, d ≠ e →
        (0 < ((windowMatrix k L)ᵀ * windowMatrix k L) d e ↔ Nat.dist d.val e.val ≤ k))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 : Module.finrank ℝ (slidingWindowSpace 1) = 1 :=
    (sliding_window_kernel_and_band_support 1).2.2.2.1
  have h0 : Module.finrank ℝ (slidingWindowSpace 1) = 0 :=
    (h 1).2.2.2.1
  exact Nat.one_ne_zero (h1.symm.trans h0)

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@sliding_window_kernel_and_band_support)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sliding_window_kernel_and_band_support, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@sliding_window_kernel_and_band_support)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing.SlidingWindow.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing.SlidingWindow.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SlidingWindow

namespace MainTheorem

abbrev sig : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)

def rejected : Realization sig :=
  realize.{0,0,0,0,0} sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law O :=
    ∀ (m k : ℕ) (ell : Fin m → ℕ),
      2 ≤ m → 1 ≤ k → (∀ i : Fin m, k + 1 ≤ ell i) →
      Fintype.card (Vertex m ell) = 1 + ∑ i : Fin m, ell i ∧
      (∀ u v : Vertex m ell, (spiderTree m ell).dist u v = distance m ell u v) ∧
      (∀ u v : Vertex m ell,
        (power m k ell).Adj u v ↔ u ≠ v ∧ (spiderTree m ell).dist u v ≤ k) ∧
      IsZeroForcing (power m k ell) (spiderTailForcingSet m k ell : Set (Vertex m ell)) ∧
      (spiderTailForcingSet m k ell).card = (m - 1) * k ∧
      spiderSymmMatrix m k ell ∈ SymGraphMatrices (power m k ell) ∧
      matrixNullity (spiderSymmMatrix m k ell) = (m - 1) * k ∧
      (spiderSymmMatrix m k ell).rank = (1 + ∑ i : Fin m, ell i) - (m - 1) * k ∧
      (∀ H ∈ SymGraphMatrices (power m k ell),
        matrixNullity H ≤ (m - 1) * k ∧
        (1 + ∑ i : Fin m, ell i) - (m - 1) * k ≤ H.rank) ∧
      IsGreatest (matrixNullity '' SymGraphMatrices (power m k ell)) ((m - 1) * k) ∧
      IsLeast (Matrix.rank '' SymGraphMatrices (power m k ell))
        ((1 + ∑ i : Fin m, ell i) - (m - 1) * k) ∧
      zeroForcingNumber (power m k ell) = (m - 1) * O.readout () () k ∧
      maxSymNullity (power m k ell) = (m - 1) * k ∧
      minSymRank (power m k ell) = (1 + ∑ i : Fin m, ell i) - (m - 1) * k

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 : zeroForcingNumber (power 2 1 (fun _ => 2)) = 1 :=
    (unequal_spider_power_zero_forcing 2 1 (fun _ => 2)
      (by decide) (by decide) (fun _ => by decide)).2.2.2.2.2.2.2.2.2.2.2.1
  have h0 : zeroForcingNumber (power 2 1 (fun _ => 2)) = 0 :=
    (h 2 1 (fun _ => 2)
      (by decide) (by decide) (fun _ => by decide)).2.2.2.2.2.2.2.2.2.2.2.1
  exact Nat.one_ne_zero (h1.symm.trans h0)

theorem dependence : ObservationalDependence sig actual := by
  rintro ⟨⟩
  exact ⟨(), 0, 1, Nat.zero_ne_one⟩

def evidence : Registration arena
    (type_of% (@unequal_spider_power_zero_forcing)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unequal_spider_power_zero_forcing, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@unequal_spider_power_zero_forcing)
      (type_of% (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e)))
      Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing.MainTheorem.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing.MainTheorem.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} sig (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MainTheorem

end Reg.D5.S3.Combinatorics.SpectralGraph.UnequalSpiderPowerZeroForcing
