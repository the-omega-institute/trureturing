import Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum

/-! Full conductance observations for the complete sharp-product source telescope. -/
noncomputable section
namespace Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
open _root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Original
open Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
abbrev Weights := Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.Weights
abbrev signature := Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.signature
abbrev actual := Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.actual
abbrev rejected := Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer.rejected
end Original

/-- All original conductance-function occurrences remain in their quantified clauses. -/
def observedClaim (m : ℕ) (observe : Original.Weights m → Original.Weights m) : Prop :=
  (∀ w : Original.Weights m, (∀ e ∈ (K2m m).edgeSet, 0 < observe w e) →
    lambda2 (K2m m) (observe w) * totalRes (K2m m) (observe w) ≤ sharpConstant m) ∧
  (∀ w : Original.Weights m, (∀ e ∈ (K2m m).edgeSet, 0 < observe w e) →
    (lambda2 (K2m m) (observe w) * totalRes (K2m m) (observe w) = sharpConstant m ↔
      ∃ t ε : ℝ, 0 < t ∧ (ε = 1 ∨ ε = -1) ∧ Ray m t ε (observe w))) ∧
  (∀ t ε : ℝ, 0 < t → (ε = 1 ∨ ε = -1) →
    (∃ w, Ray m t ε (observe w)) ∧
    ∀ w, Ray m t ε (observe w) → (∀ e ∈ (K2m m).edgeSet, 0 < observe w e) ∧
      lambda2 (K2m m) (observe w) = t ∧ totalRes (K2m m) (observe w) = sharpConstant m / t ∧
      FullSpectrum m (observe w) t) ∧
  (¬ ∃ (t s : ℝ) (w : Original.Weights m),
    0 < t ∧ 0 < s ∧ Ray m t 1 (observe w) ∧ Ray m s (-1) (observe w)) ∧
  (∀ (t ε : ℝ) (w : Original.Weights m),
    Ray m t ε (observe w) → Ray m t (-ε) (observe (exchangeWeights m w))) ∧
  (∀ w w' : Original.Weights m, (∀ e ∈ (K2m m).edgeSet, observe w e = observe w' e) →
    lambda2 (K2m m) (observe w) = lambda2 (K2m m) (observe w') ∧
    totalRes (K2m m) (observe w) = totalRes (K2m m) (observe w'))

abbrev arena : Arena where
  signature := Original.signature
  Law R := ∀ (m : ℕ), 3 ≤ m → observedClaim m (R.readout () m)

abbrev source := type_of% (@_root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum.result)

theorem source_bridge : source ↔ arena.Law Original.actual := Iff.rfl

theorem actual_positive : arena.Law Original.actual := @_root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum.result

theorem rejected_law : ¬ arena.Law Original.rejected := by
  intro h
  obtain ⟨w,hw⟩ := ((h 3 (by norm_num)).2.2.1 1 1 (by norm_num) (Or.inl rfl)).1
  have hh := (hw (⟨0, by omega⟩ : Fin 3)).1
  change (0 : ℝ) = 1 / 2 * (1 + 1 * splitRatio 3) at hh
  have hr := (splitRatio_facts (m := 3) (by norm_num)).1
  nlinarith

def family : Registration arena source where
  actual := Original.actual
  bridge := source_bridge
  variation := ⟨actual_positive, Original.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨Original.rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨3, (0 : Original.Weights 3), (1 : Original.Weights 3), ?_⟩
    intro he
    have hh := congrFun he s((0 : Fin (2+3)), (2 : Fin (2+3)))
    change (0 : ℝ) = 1 at hh
    norm_num at hh

noncomputable def sourceRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0} (@_root_.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum.result)
      (Realization Original.signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize Original.signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
      name := `D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum.SharpProductClaim
      path := #[] }
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mSharpSpectrum
