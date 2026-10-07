import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.GoldenResource.ThresholdChainReduction
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction

open Finset
open _root_.D5.S3.Arith.GoldenResource.ThresholdChainReduction
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Weil.GronwallLowerEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ B : ℕ, Σ U : ℕ,
    Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U}
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law := fun r =>
    ∀ {B U : ℕ} (hB : 3 ≤ B) (hU : U ≠ 0)
        (hBU : B ∣ U)
        (e : Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U})
        (horder : Antitone (fun i => goldenLayerMarginal (e i).val.1 (e i).val.2)),
        (exponentLayers B U).card =
          (∑ p ∈ U.primeFactors, (U.factorization p - B.factorization p)) ∧
        (exponentBox B U).card =
          (∏ p ∈ U.primeFactors, (U.factorization p - B.factorization p + 1)) ∧
        (∀ j ≤ (exponentLayers B U).card, r.readout () ⟨B, U, e⟩ j ∈ exponentBox B U) ∧
        (∀ j ≤ (exponentLayers B U).card, ∀ i : Fin (exponentLayers B U).card,
          i.val < j → ∀ k, B.factorization (e i).val.1 < k → k ≤ (e i).val.2 →
            ∃ r : Fin (exponentLayers B U).card,
              r.val < j ∧ (e r).val = ((e i).val.1, k)) ∧
        (∃ j ≤ (exponentLayers B U).card,
          IsLeast (robinLogMargin '' (↑(exponentBox B U) : Set ℕ))
            (robinLogMargin (r.readout () ⟨B, U, e⟩ j)) ∧
          IsLeast ((fun j => robinLogMargin (r.readout () ⟨B, U, e⟩ j)) ''
            Set.Iic (exponentLayers B U).card)
            (robinLogMargin (r.readout () ⟨B, U, e⟩ j))) ∧
        sInf (robinLogMargin '' (↑(exponentBox B U) : Set ℕ)) =
          sInf ((fun j => robinLogMargin (r.readout () ⟨B, U, e⟩ j)) ''
            Set.Iic (exponentLayers B U).card)

def actual : Realization signature :=
  realize signature (fun _ p j => layerChain p.1 p.2.1 p.2.2 j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def enumeration (B U : ℕ) :
    Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U} :=
  (Finset.equivFin (exponentLayers B U)).symm

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let e := enumeration 3 3
  have hlayers : exponentLayers 3 3 = ∅ := by
    ext pk
    simp [exponentLayers]
  have horder : Antitone (fun i => goldenLayerMarginal (e i).val.1 (e i).val.2) := by
    intro i j hij
    have hi : i.val < 0 := by simpa [hlayers] using i.isLt
    omega
  have hp := h (B := 3) (U := 3) (by decide) (by decide) dvd_rfl e horder
  have hzero := hp.2.2.1 0 (Nat.zero_le _)
  change 0 ∈ exponentBox 3 3 at hzero
  have hz := (Nat.mem_divisors.mp (mem_filter.mp hzero).1).1
  norm_num at hz

def registration : Registration arena (
  ∀ {B U : ℕ} (hB : 3 ≤ B) (hU : U ≠ 0)
      (hBU : B ∣ U)
      (e : Fin (exponentLayers B U).card ≃ {pk // pk ∈ exponentLayers B U})
      (horder : Antitone (fun i => goldenLayerMarginal (e i).val.1 (e i).val.2)),
      (exponentLayers B U).card =
        (∑ p ∈ U.primeFactors, (U.factorization p - B.factorization p)) ∧
      (exponentBox B U).card =
        (∏ p ∈ U.primeFactors, (U.factorization p - B.factorization p + 1)) ∧
      (∀ j ≤ (exponentLayers B U).card, layerChain B U e j ∈ exponentBox B U) ∧
      (∀ j ≤ (exponentLayers B U).card, ∀ i : Fin (exponentLayers B U).card,
        i.val < j → ∀ k, B.factorization (e i).val.1 < k → k ≤ (e i).val.2 →
          ∃ r : Fin (exponentLayers B U).card,
            r.val < j ∧ (e r).val = ((e i).val.1, k)) ∧
      (∃ j ≤ (exponentLayers B U).card,
        IsLeast (robinLogMargin '' (↑(exponentBox B U) : Set ℕ))
          (robinLogMargin (layerChain B U e j)) ∧
        IsLeast ((fun j => robinLogMargin (layerChain B U e j)) ''
          Set.Iic (exponentLayers B U).card)
          (robinLogMargin (layerChain B U e j))) ∧
      sInf (robinLogMargin '' (↑(exponentBox B U) : Set ℕ)) =
        sInf ((fun j => robinLogMargin (layerChain B U e j)) ''
          Set.Iic (exponentLayers B U).card)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨threshold_chain_reduction, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let e := enumeration 3 6
    have hlayers : exponentLayers 3 6 = {(2, 1)} := by
      have htwo : Nat.Prime 2 := by norm_num
      have hthree : Nat.Prime 3 := by norm_num
      have hu : (6 : ℕ).primeFactors = {2, 3} := by
        rw [show 6 = 2 * 3 from rfl, Nat.primeFactors_mul (by decide) (by decide),
          htwo.primeFactors, hthree.primeFactors]
        rfl
      have hf : (6 : ℕ).factorization = Finsupp.single 2 1 + Finsupp.single 3 1 := by
        rw [show 6 = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
          htwo.factorization, hthree.factorization]
      simp [exponentLayers, hu, hf, hthree.factorization]
    have hcard : (exponentLayers 3 6).card = 1 := by rw [hlayers]; rfl
    have hvalue (r : Fin (exponentLayers 3 6).card) : (e r).val = (2, 1) := by
      have hr := (e r).property
      simp only [hlayers, mem_singleton] at hr
      exact hr
    refine ⟨⟨3, 6, e⟩, 0, 1, ?_⟩
    change layerChain 3 6 e 0 ≠ layerChain 3 6 e 1
    have hfull : (univ.filter fun r : Fin (exponentLayers 3 6).card => r.val < 1) =
        univ := by
      apply filter_eq_self.mpr
      intro r hr
      simpa [hcard] using r.isLt
    simp only [layerChain, Nat.not_lt_zero, filter_false, prod_empty, mul_one, hfull]
    have hprod : (∏ r : Fin (exponentLayers 3 6).card, (e r).val.1) = 2 := by
      simp only [hvalue]
      simp [hcard]
    rw [hprod]
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.GoldenResource.ThresholdChainReduction.threshold_chain_reduction) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p j => layerChain p.1 p.2.1 p.2.2 j) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "GoldenResource") "ThresholdChainReduction") "threshold_chain_reduction") "Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction/Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p j => layerChain p.1 p.2.1 p.2.2 j) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.GoldenResource.ThresholdChainReduction, definition := none, coordinates := #[0, 1, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `D5.S3.Arith.GoldenResource.ThresholdChainReduction.threshold_chain_reduction, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.observationFact0, `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction


noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.arena
noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.arena
noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.arena
    (∀ {B U : Nat} (hB : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) B)
      (hU : @Ne.{1} Nat U (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (hBU : @Dvd.dvd.{0} Nat Nat.instDvd B U)
      (e :
        Equiv.{1, 1}
          (Fin
            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
      (horder :
        @Antitone.{0, 0}
          (Fin
            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
          Real
          (@PartialOrder.toPreorder.{0}
            (Fin
              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
            (@Fin.instPartialOrder
              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))))
          Real.instPreorder
          fun
            (i :
              Fin
                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
          D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal
            (@Prod.fst.{0, 0} Nat Nat
              (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                (fun (pk : Prod.{0, 0} Nat Nat) =>
                  @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                      (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (fun
                      (x :
                        Fin
                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                    @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1}
                      (Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                            (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                    (@Equiv.instEquivLike.{1, 1}
                      (Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                            (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                  e i)))
            (@Prod.snd.{0, 0} Nat Nat
              (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                (fun (pk : Prod.{0, 0} Nat Nat) =>
                  @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                      (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (fun
                      (x :
                        Fin
                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                    @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1}
                      (Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                            (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                    (@Equiv.instEquivLike.{1, 1}
                      (Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                            (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                  e i)))),
      And
        (@Eq.{1} Nat
          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))
          (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid (Nat.primeFactors U) fun (p : Nat) =>
            @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                (fun (x : Nat) => Nat)
                (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (Nat.factorization U) p)
              (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                (fun (x : Nat) => Nat)
                (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (Nat.factorization B) p)))
        (And
          (@Eq.{1} Nat (@Finset.card.{0} Nat (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U))
            (@Finset.prod.{0, 0} Nat Nat Nat.instCommMonoid (Nat.primeFactors U) fun (p : Nat) =>
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    Nat (fun (x : Nat) => Nat)
                    (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    (Nat.factorization U) p)
                  (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    Nat (fun (x : Nat) => Nat)
                    (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    (Nat.factorization B) p))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And
            (∀ (j : Nat),
              @LE.le.{0} Nat instLENat j
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)) →
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U)
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j))
            (And
              (∀ (j : Nat),
                @LE.le.{0} Nat instLENat j
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)) →
                  ∀
                    (i :
                      Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))),
                    @LT.lt.{0} Nat instLTNat
                        (@Fin.val
                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))
                          i)
                        j →
                      ∀ (k : Nat),
                        @LT.lt.{0} Nat instLTNat
                            (@DFunLike.coe.{1, 1, 1}
                              (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                              (fun (x : Nat) => Nat)
                              (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                              (Nat.factorization B)
                              (@Prod.fst.{0, 0} Nat Nat
                                (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                  (fun (pk : Prod.{0, 0} Nat Nat) =>
                                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                  (@DFunLike.coe.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                    (Fin
                                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                    (fun
                                        (x :
                                          Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                U))) =>
                                      @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                    (@EquivLike.toFunLike.{1, 1, 1}
                                      (Equiv.{1, 1}
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                            pk)))
                                    e i))))
                            k →
                          @LE.le.{0} Nat instLENat k
                              (@Prod.snd.{0, 0} Nat Nat
                                (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                  (fun (pk : Prod.{0, 0} Nat Nat) =>
                                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                  (@DFunLike.coe.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                    (Fin
                                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                    (fun
                                        (x :
                                          Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                U))) =>
                                      @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                    (@EquivLike.toFunLike.{1, 1, 1}
                                      (Equiv.{1, 1}
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                            pk)))
                                    e i))) →
                            @Exists.{1}
                              (Fin
                                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                              fun
                                (r :
                                  Fin
                                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                              And
                                (@LT.lt.{0} Nat instLTNat
                                  (@Fin.val
                                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))
                                    r)
                                  j)
                                (@Eq.{1} (Prod.{0, 0} Nat Nat)
                                  (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                    (fun (pk : Prod.{0, 0} Nat Nat) =>
                                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                    (@DFunLike.coe.{1, 1, 1}
                                      (Equiv.{1, 1}
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (fun
                                          (x :
                                            Fin
                                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                  U))) =>
                                        @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                      (@EquivLike.toFunLike.{1, 1, 1}
                                        (Equiv.{1, 1}
                                          (Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                              (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                              pk))
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                        (@Equiv.instEquivLike.{1, 1}
                                          (Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                              (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                              pk)))
                                      e r))
                                  (@Prod.mk.{0, 0} Nat Nat
                                    (@Prod.fst.{0, 0} Nat Nat
                                      (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                        (fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                        (@DFunLike.coe.{1, 1, 1}
                                          (Equiv.{1, 1}
                                            (Fin
                                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                  U)))
                                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                                (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                  (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                                pk))
                                          (Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                          (fun
                                              (x :
                                                Fin
                                                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                      U))) =>
                                            @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                                (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                  (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                                pk)
                                          (@EquivLike.toFunLike.{1, 1, 1}
                                            (Equiv.{1, 1}
                                              (Fin
                                                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                    U)))
                                              (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                                @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                                  (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                    (Prod.{0, 0} Nat Nat)
                                                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                    U)
                                                  pk))
                                            (Fin
                                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                  U)))
                                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                                (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                  (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                                pk)
                                            (@Equiv.instEquivLike.{1, 1}
                                              (Fin
                                                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                    U)))
                                              (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                                @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                                  (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                    (Prod.{0, 0} Nat Nat)
                                                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                    U)
                                                  pk)))
                                          e i)))
                                    k)))
              (And
                (@Exists.{1} Nat fun (j : Nat) =>
                  And
                    (@LE.le.{0} Nat instLENat j
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (And
                      (@IsLeast.{0} Real Real.instLE
                        (@Set.image.{0, 0} Nat Real D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                          (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U)))
                        (D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j)))
                      (@IsLeast.{0} Real Real.instLE
                        (@Set.image.{0, 0} Nat Real
                          (fun (j : Nat) =>
                            D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j))
                          (@Set.Iic.{0} Nat Nat.instPreorder
                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))))
                        (D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j)))))
                (@Eq.{1} Real
                  (@InfSet.sInf.{0} Real Real.instInfSet
                    (@Set.image.{0, 0} Nat Real D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                      (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U))))
                  (@InfSet.sInf.{0} Real Real.instInfSet
                    (@Set.image.{0, 0} Nat Real
                      (fun (j : Nat) =>
                        D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j))
                      (@Set.Iic.{0} Nat Nat.instPreorder
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))))))))))
    Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration)

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"threshold_chain_reduction\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `D5.S3.Arith.GoldenResource.ThresholdChainReduction.threshold_chain_reduction, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.arena
  (∀ {B U : Nat} (hB : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) B)
    (hU : @Ne.{1} Nat U (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (hBU : @Dvd.dvd.{0} Nat Nat.instDvd B U)
    (e :
      Equiv.{1, 1}
        (Fin
          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
              (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
    (horder :
      @Antitone.{0, 0}
        (Fin
          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
        Real
        (@PartialOrder.toPreorder.{0}
          (Fin
            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
          (@Fin.instPartialOrder
            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))))
        Real.instPreorder
        fun
          (i :
            Fin
              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
        D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal
          (@Prod.fst.{0, 0} Nat Nat
            (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
              (fun (pk : Prod.{0, 0} Nat Nat) =>
                @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1}
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                (Fin
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                (fun
                    (x :
                      Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                  @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                  (@Equiv.instEquivLike.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                e i)))
          (@Prod.snd.{0, 0} Nat Nat
            (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
              (fun (pk : Prod.{0, 0} Nat Nat) =>
                @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1}
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                (Fin
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                (fun
                    (x :
                      Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                  @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                  (@Equiv.instEquivLike.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                e i)))),
    And
      (@Eq.{1} Nat
        (@Finset.card.{0} (Prod.{0, 0} Nat Nat) (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))
        (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid (Nat.primeFactors U) fun (p : Nat) =>
          @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
              (fun (x : Nat) => Nat)
              (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
              (Nat.factorization U) p)
            (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
              (fun (x : Nat) => Nat)
              (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
              (Nat.factorization B) p)))
      (And
        (@Eq.{1} Nat (@Finset.card.{0} Nat (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U))
          (@Finset.prod.{0, 0} Nat Nat Nat.instCommMonoid (Nat.primeFactors U) fun (p : Nat) =>
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  Nat (fun (x : Nat) => Nat)
                  (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  (Nat.factorization U) p)
                (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  Nat (fun (x : Nat) => Nat)
                  (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  (Nat.factorization B) p))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (∀ (j : Nat),
            @LE.le.{0} Nat instLENat j
                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)) →
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U)
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j))
          (And
            (∀ (j : Nat),
              @LE.le.{0} Nat instLENat j
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)) →
                ∀
                  (i :
                    Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))),
                  @LT.lt.{0} Nat instLTNat
                      (@Fin.val
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))
                        i)
                      j →
                    ∀ (k : Nat),
                      @LT.lt.{0} Nat instLTNat
                          (@DFunLike.coe.{1, 1, 1}
                            (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                            (fun (x : Nat) => Nat)
                            (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                            (Nat.factorization B)
                            (@Prod.fst.{0, 0} Nat Nat
                              (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                (fun (pk : Prod.{0, 0} Nat Nat) =>
                                  @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                      (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                (@DFunLike.coe.{1, 1, 1}
                                  (Equiv.{1, 1}
                                    (Fin
                                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                  (Fin
                                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                  (fun
                                      (x :
                                        Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                                    @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                  (@EquivLike.toFunLike.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                    (Fin
                                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                    (@Equiv.instEquivLike.{1, 1}
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                                  e i))))
                          k →
                        @LE.le.{0} Nat instLENat k
                            (@Prod.snd.{0, 0} Nat Nat
                              (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                (fun (pk : Prod.{0, 0} Nat Nat) =>
                                  @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                      (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                (@DFunLike.coe.{1, 1, 1}
                                  (Equiv.{1, 1}
                                    (Fin
                                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                  (Fin
                                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                  (fun
                                      (x :
                                        Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                                    @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                  (@EquivLike.toFunLike.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                    (Fin
                                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                    (@Equiv.instEquivLike.{1, 1}
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                                  e i))) →
                          @Exists.{1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            fun
                              (r :
                                Fin
                                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                            And
                              (@LT.lt.{0} Nat instLTNat
                                (@Fin.val
                                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))
                                  r)
                                j)
                              (@Eq.{1} (Prod.{0, 0} Nat Nat)
                                (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                  (fun (pk : Prod.{0, 0} Nat Nat) =>
                                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                        (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                  (@DFunLike.coe.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                    (Fin
                                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                    (fun
                                        (x :
                                          Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                U))) =>
                                      @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                    (@EquivLike.toFunLike.{1, 1, 1}
                                      (Equiv.{1, 1}
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                                      (Fin
                                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                      (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                            (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                            pk)))
                                    e r))
                                (@Prod.mk.{0, 0} Nat Nat
                                  (@Prod.fst.{0, 0} Nat Nat
                                    (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                                      (fun (pk : Prod.{0, 0} Nat Nat) =>
                                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                            (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                                      (@DFunLike.coe.{1, 1, 1}
                                        (Equiv.{1, 1}
                                          (Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                              (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                              pk))
                                        (Fin
                                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                        (fun
                                            (x :
                                              Fin
                                                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                    U))) =>
                                          @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                              (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                              pk)
                                        (@EquivLike.toFunLike.{1, 1, 1}
                                          (Equiv.{1, 1}
                                            (Fin
                                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                  U)))
                                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                                (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                  (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                                pk))
                                          (Fin
                                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                              (Finset.{0} (Prod.{0, 0} Nat Nat))
                                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                              pk)
                                          (@Equiv.instEquivLike.{1, 1}
                                            (Fin
                                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B
                                                  U)))
                                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat)
                                                (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                                                  (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)
                                                pk)))
                                        e i)))
                                  k)))
            (And
              (@Exists.{1} Nat fun (j : Nat) =>
                And
                  (@LE.le.{0} Nat instLENat j
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (And
                    (@IsLeast.{0} Real Real.instLE
                      (@Set.image.{0, 0} Nat Real D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                        (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U)))
                      (D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j)))
                    (@IsLeast.{0} Real Real.instLE
                      (@Set.image.{0, 0} Nat Real
                        (fun (j : Nat) =>
                          D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j))
                        (@Set.Iic.{0} Nat Nat.instPreorder
                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))))
                      (D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j)))))
              (@Eq.{1} Real
                (@InfSet.sInf.{0} Real Real.instInfSet
                  (@Set.image.{0, 0} Nat Real D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                    (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentBox B U))))
                (@InfSet.sInf.{0} Real Real.instInfSet
                  (@Set.image.{0, 0} Nat Real
                    (fun (j : Nat) =>
                      D5.S3.Weil.GronwallLowerEnvelope.robinLogMargin
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.layerChain B U e j))
                    (@Set.Iic.{0} Nat Nat.instPreorder
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))))))))))
  Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration)

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.observation0 : {B U : Nat} →
  (hB : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) B) →
    (hU : @Ne.{1} Nat U (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (hBU : @Dvd.dvd.{0} Nat Nat.instDvd B U) →
        (e :
            Equiv.{1, 1}
              (Fin
                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
              (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)) →
          (horder :
              @Antitone.{0, 0}
                (Fin
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                Real
                (@PartialOrder.toPreorder.{0}
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Fin.instPartialOrder
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))))
                Real.instPreorder
                fun
                  (i :
                    Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal
                  (@Prod.fst.{0, 0} Nat Nat
                    (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                      (fun (pk : Prod.{0, 0} Nat Nat) =>
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                            (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1}
                          (Fin
                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                        (Fin
                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                        (fun
                            (x :
                              Fin
                                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                          @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                          (Fin
                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                        e i)))
                  (@Prod.snd.{0, 0} Nat Nat
                    (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
                      (fun (pk : Prod.{0, 0} Nat Nat) =>
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                            (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1}
                          (Fin
                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                        (Fin
                          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                        (fun
                            (x :
                              Fin
                                (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                          @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                          (Fin
                            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                          (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                          (@Equiv.instEquivLike.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                        e i)))) →
            (j : Nat) →
              @LE.le.{0} Nat instLENat j
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.signature
                    (@Sigma.mk.{0, 0} Nat
                      (fun (B : Nat) =>
                        @Sigma.{0, 0} Nat fun (U : Nat) =>
                          Equiv.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                      B
                      (@Sigma.mk.{0, 0} Nat
                        (fun (U : Nat) =>
                          Equiv.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                        U e)) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.signature PUnit.unit.{1}
                    (@Sigma.mk.{0, 0} Nat
                      (fun (B : Nat) =>
                        @Sigma.{0, 0} Nat fun (U : Nat) =>
                          Equiv.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                      B
                      (@Sigma.mk.{0, 0} Nat
                        (fun (U : Nat) =>
                          Equiv.{1, 1}
                            (Fin
                              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                        U e)) :=
  fun {B U : Nat} (hB : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) B)
    (hU : @Ne.{1} Nat U (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (hBU : @Dvd.dvd.{0} Nat Nat.instDvd B U)
    (e :
      Equiv.{1, 1}
        (Fin
          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
        (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
          @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
              (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
    (horder :
      @Antitone.{0, 0}
        (Fin
          (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
            (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
        Real
        (@PartialOrder.toPreorder.{0}
          (Fin
            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
          (@Fin.instPartialOrder
            (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
              (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))))
        Real.instPreorder
        fun
          (i :
            Fin
              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
        D5.S3.Arith.GoldenResourceOptimalInteger.goldenLayerMarginal
          (@Prod.fst.{0, 0} Nat Nat
            (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
              (fun (pk : Prod.{0, 0} Nat Nat) =>
                @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1}
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                (Fin
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                (fun
                    (x :
                      Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                  @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                  (@Equiv.instEquivLike.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                e i)))
          (@Prod.snd.{0, 0} Nat Nat
            (@Subtype.val.{1} (Prod.{0, 0} Nat Nat)
              (fun (pk : Prod.{0, 0} Nat Nat) =>
                @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                  (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1}
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                (Fin
                  (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                    (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                (fun
                    (x :
                      Fin
                        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
                  @Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
                  (Fin
                    (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                  (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                        (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                      (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)
                  (@Equiv.instEquivLike.{1, 1}
                    (Fin
                      (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
                    (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                          (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk)))
                e i))))
    (j : Nat)
    (a :
      @LE.le.{0} Nat instLENat j
        (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
          (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.signature
    Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (B : Nat) =>
        @Sigma.{0, 0} Nat fun (U : Nat) =>
          Equiv.{1, 1}
            (Fin
              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
      B
      (@Sigma.mk.{0, 0} Nat
        (fun (U : Nat) =>
          Equiv.{1, 1}
            (Fin
              (@Finset.card.{0} (Prod.{0, 0} Nat Nat)
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U)))
            (@Subtype.{1} (Prod.{0, 0} Nat Nat) fun (pk : Prod.{0, 0} Nat Nat) =>
              @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Prod.{0, 0} Nat Nat)
                  (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                (D5.S3.Arith.GoldenResource.ThresholdChainReduction.exponentLayers B U) pk))
        U e))

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"threshold_chain_reduction\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `D5.S3.Arith.GoldenResource.ThresholdChainReduction.threshold_chain_reduction, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument, .body, .body, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"threshold_chain_reduction\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `D5.S3.Arith.GoldenResource.ThresholdChainReduction.threshold_chain_reduction, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration).actual (Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration).variation.2.choose (Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration).variation.1 (Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"GoldenResource\",\"ThresholdChainReduction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction, declaration := `Reg.D5.S3.Arith.GoldenResource.ThresholdChainReduction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
