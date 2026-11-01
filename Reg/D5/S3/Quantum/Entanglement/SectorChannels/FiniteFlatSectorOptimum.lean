import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum
open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum
universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observation := ∀ {Sector : Type u} [Fintype Sector] [DecidableEq Sector] [Nonempty Sector]
    (r d m : Sector → ℕ) (hr : ∀ s, r s = d s * m s)
    (hd : ∀ s, 0 < d s) (hm : ∀ s, 0 < m s),
    FlatFeasibilityClaim (Sector := Sector) ∧
    ∃ J : ℕ, ∃ hmJ : ∀ s, m s ≤ J,
    ∃ n : ℕ, ∃ a : Fin (n + 1) → ℕ, ∃ f : Sector → Fin (n + 1), ∃ loss : ℕ → ℝ,
    ∃ source : QuantumChannel Sector (TargetLocal r × TargetLocal r),
    ∃ target : QuantumChannel Sector (TargetLocal d × TargetLocal d),
    ∃ E : QuantumChannel (TargetLocal r) (SourceLocal (Coord := Fin J) d),
    ∃ splitting : QuantumChannel (TargetLocal r) (TargetLocal d),
    ∃ joint : QuantumChannel (TargetLocal r × TargetLocal r) (TargetLocal d × TargetLocal d),
      StrictMono a ∧ Function.Surjective f ∧ (∀ s, a (f s) = m s) ∧
      (∀ i : Fin (n + 1), loss i = Real.log (a i : ℝ)) ∧
      StrictMono (fun i : Fin (n + 1) => loss i) ∧
      (∀ X, raw source X = targetEncoding r * X * (targetEncoding r)ᴴ) ∧
      (∀ X, raw target X = targetEncoding d * X * (targetEncoding d)ᴴ) ∧
      (∀ X, raw E X = placement (compactEmbedding r d m J hr hmJ) * X *
        (placement (compactEmbedding r d m J hr hmJ))ᴴ) ∧
      (∀ s (a : Fin (d s)) (b : Fin (m s)),
        ((compactSplit r d m hr).symm ⟨s, (a, b)⟩).2.val = a.val + d s * b.val) ∧
      (∀ X b c, raw splitting X b c = ∑ j : Fin J,
        (placement (compactEmbedding r d m J hr hmJ) * X *
          (placement (compactEmbedding r d m J hr hmJ))ᴴ)
            ⟨b.1, (b.2, j)⟩ ⟨c.1, (c.2, j)⟩) ∧
      TensorRealization splitting splitting joint ∧
      (∀ s t, Real.sqrt ((min (m s) (m t) : ℕ) / (max (m s) (m t) : ℝ)) =
        observation.readout () () (-|Real.log (m s : ℝ) - Real.log (m t : ℝ)| / 2)) ∧
      (∀ X, raw (joint.comp source) X = targetEncoding d *
        (Matrix.of fun s t =>
          (Real.exp (-|Real.log (m s : ℝ) - Real.log (m t : ℝ)| / 2) : ℂ) * X s t) *
          (targetEncoding d)ᴴ) ∧
      (∀ s, (joint.comp source).toCompletelyPositiveMap
          (CStarMatrix.ofMatrix (Matrix.single s s 1)) =
        target.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single s s 1))) ∧
      diamondDistance (joint.comp source) target = 2 * lossTotal n loss / (1 + lossTotal n loss) ∧
      IsLeast (compactProductErrors r d source target)
        (2 * lossTotal n loss / (1 + lossTotal n loss)) ∧
      IsLeast (compactExactProductErrors r d source target)
        (2 * lossTotal n loss / (1 + lossTotal n loss)) ∧
      sInf (compactExactProductErrors r d source target) =
        2 * lossTotal n loss / (1 + lossTotal n loss) ∧
      (n = 0 → diamondDistance (joint.comp source) target = 0) ∧
      ((∀ s t, m s = m t) → diamondDistance (joint.comp source) target = 0)

theorem actual_law : arena.{u}.Law actual := by
  intro Sector _ _ _ r d m hr hd hm
  exact _root_.D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum.result r d m hr hd hm

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨_, J, hmJ, n, a, f, loss, source, target, E, splitting, joint,
    ha, hf, haf, hloss, hstrict, hsource, htarget, hE, hsplit, hAction, hTensor,
    hGram, _⟩ := h (Sector := ULift.{u} Unit) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (by intro s; rfl) (by intro s; norm_num) (by intro s; norm_num)
  have hbad := hGram (⟨()⟩ : ULift.{u} Unit) (⟨()⟩ : ULift.{u} Unit)
  norm_num [rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (0 : ℝ) = 1 := Real.exp_injective (by simpa [actual, realize] using h)
  exact zero_ne_one he

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum.result.{u})
    (type_of% (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum,
    definition := none,
    coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.FiniteFlatSectorOptimum
