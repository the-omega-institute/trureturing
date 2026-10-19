import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.NestedPressureLimit
import Reg.Support.SingleDependentReadout
import Reg.Support.FibonacciFactorWitnesses
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

theorem zero_count_positive (model : Model) (K : ℕ) (d : ℝ) (strict : Bool)
    (hK : 1 ≤ K) : 0 < actualCount model K d strict 0 := by
  letI : Finite (ActualDictionary model K d strict 0) :=
    (actual_dictionary_bound model K d strict 0 hK).1
  letI : Nonempty (ActualDictionary model K d strict 0) := ⟨⟨[], trivial, rfl⟩⟩
  exact Nat.card_pos

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ N => 3^(N+1)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (N : ℕ) (hK : 1 ≤ K),
    Finite (ActualDictionary model K d strict N) ∧
    actualCount model K d strict N ≤ factorCount (AuxiliaryLanguage K d) N ∧
    actualCount model K d strict N ≤ r.readout () () N

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have positive := zero_count_positive .original 1 0 false (by decide)
  have upper := (h .original 1 0 false 0 (by decide)).2.2
  change actualCount .original 1 0 false 0 ≤ 0 at upper
  omega

def evidence : Registration sourceArena (type_of% @actual_dictionary_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_dictionary_bound, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℕ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ q N => Nat.card (NoCFactor q.1 q.2 N)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (N : ℕ), r.readout () ⟨K,d⟩ N ≤ 1

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := h 1 0 0
  norm_num [rejected, realize] at bad

def evidence : Registration sourceArena (type_of% @no_c_factor_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_c_factor_card, rejected, rejected_law⟩
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
    refine ⟨⟨1,0⟩, 0, 1, ?_⟩
    change Nat.card (NoCFactor 1 0 0) ≠ Nat.card (NoCFactor 1 0 1)
    have zero_card : Nat.card (NoCFactor 1 0 0) = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨⟨[], ⟨(fun _ => .u), all_u_auxiliary, 0, (by intro k; exact Fin.elim0 k)⟩, rfl⟩,
        (by simp)⟩, ?_⟩
      intro w
      apply Subtype.ext
      apply Subtype.ext
      exact word_weight_geometry.2.2 _ w.val.property.2
    letI : IsEmpty (NoCFactor 1 0 1) := ⟨by
      intro w
      exact word_weight_ne_one _ w.val.property.2⟩
    simp [zero_card]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal33

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39
noncomputable section

open Reg.Support.FibonacciFactorWitnesses
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal31

theorem one_count_zero (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) :
    actualCount model K d strict 1 = 0 := by
  letI : IsEmpty (ActualDictionary model K d strict 1) := ⟨by
    intro xs
    have wt := xs.property.2
    cases eq : xs.val with
    | nil => simp [eq, listWeight] at wt
    | cons a rest =>
      have pos := a.m_pos
      simp only [eq, listWeight] at wt
      omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem budget_witness : ∃ b : ℝ,
    lam - g ^ 2 * chi ^ 2 * hSide .high < b ∧
    b < lam - g ^ 2 * chi ^ 2 * (aSide .high / (1 - rho * chi ^ 2)) := by
  have gp := tail_arithmetic.2.2.2.1
  have gl := tail_arithmetic.2.2.2.2.1
  have rp : 0 < rho := pow_pos gp 6
  have rl : rho < 1 := pow_lt_one₀ gp.le gl (by decide)
  have cp : 0 < chi := pow_pos gp 20
  have cl : chi < 1 := pow_lt_one₀ gp.le gl (by decide)
  have c2l : chi ^ 2 < 1 := pow_lt_one₀ cp.le cl (by decide)
  have rc : rho * chi ^ 2 < rho := by simpa using mul_lt_mul_of_pos_left c2l rp
  have den : 0 < 1 - rho * chi ^ 2 := by linarith
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have lt : aSide .high / (1 - rho * chi ^ 2) < hSide .high := by
    apply (div_lt_iff₀ den).mpr
    dsimp [aSide]
    have := mul_lt_mul_of_pos_right (show 1-rho < 1-rho*chi^2 by linarith) hp
    nlinarith
  have mulpos : 0 < g ^ 2 * chi ^ 2 := mul_pos (pow_pos gp _) (pow_pos cp _)
  have width := mul_lt_mul_of_pos_left lt mulpos
  exact exists_between (by linarith)

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ N => N) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ) (contract : Contract) (N K : ℕ)
    (hK : 2 ≤ K) (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))),
    Finite (ContractDictionary model o b contract N) ∧
    contractCount model o b contract N =
      actualCount model K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) (r.readout () () N)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hb₁, hb₂⟩ := budget_witness
  have original := (contract_count_correspondence .original (fun _ => false) b .strict 0 2
    (by decide) hb₁ hb₂).2
  have changed := (h .original (fun _ => false) b .strict 0 2 (by decide) hb₁ hb₂).2
  change contractCount .original (fun _ => false) b .strict 0 =
    actualCount .original 2 ((lam-b)/g^2/chi^2) (contractStrict (fun _ => false) .strict) 1 at changed
  rw [one_count_zero] at changed
  have positive := zero_count_positive .original 2 ((lam-b)/g^2/chi^2)
    (contractStrict (fun _ => false) .strict) (by decide)
  omega

def evidence : Registration sourceArena (type_of% @contract_count_correspondence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@contract_count_correspondence, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39










