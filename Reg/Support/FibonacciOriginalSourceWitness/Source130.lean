import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces

namespace Reg.Support.FibonacciOriginalSourceWitness.Source130
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → Guard) (fun _ => Guard)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ path => path 0) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => Guard.G1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length)
    (B : Finset ℝ) (P2 : OriginalPiece B s)
    (selection : ({z : ℝ | ∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W} ∩ (piece_carrier P2)).Nonempty)
    (paths : ∀ zs : List Bool, OriginalPiecePath B (Q++choiceBlocks (fun _ => V) zs) s P2),
    ∃ (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      r.readout () () path = s ∧ x 0 ∈ (piece_carrier P2) ∧
      (∀ p, nextGuard (path p) (tail p) = some (path (p+1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (tail p) (x (p+1))) ∧
      (∀ n, (compose V)^[n] (x 0) ∈ CompetingT o θ s Q V h W) ∧
      ∀ zs : List Bool, ∃ (beta : ℕ → Label) (X : ℕ → ℝ) (q : ℕ → Guard),
        q 0 = .G0 ∧
        (∀ p, nextGuard (q p) (beta p) = some (q (p+1))) ∧
        (∀ p, InSupport (q p) (X p)) ∧
        (∀ p, X p = branch (beta p) (X (p+1))) ∧
        (∀ p (hp : p < (Q++choiceBlocks (fun _ => V) zs).length),
          beta p = (Q++choiceBlocks (fun _ => V) zs)[p]) ∧
        (∀ p, beta ((Q++choiceBlocks (fun _ => V) zs).length+p) = tail p ∧
          X ((Q++choiceBlocks (fun _ => V) zs).length+p) = x p ∧
          q ((Q++choiceBlocks (fun _ => V) zs).length+p) = path p) ∧
        (∀ p, p ≤ (Q++choiceBlocks (fun _ => V) zs).length →
          X p ∈ (piece_carrier ((paths zs).pieces p)) ∧ q p = (paths zs).guards p) ∧
        OperationRecord o θ .closed beta (recordWithOmegaTail o (h++choiceBlocks W zs) x)

theorem zero_supported : InSupport .G0 0 := by
  refine ⟨by norm_num, ?_⟩
  change (0 : ℝ) ≤ phi
  have hp := tail_arithmetic.2.1
  dsimp [phi]
  linarith

def zeroPiece : OriginalPiece ({0} : Finset ℝ) .G0 where
  lo := 0
  hi := 0
  lo_mem := by simp
  hi_mem := by simp
  ordered := le_rfl
  lo_support := zero_supported
  hi_support := zero_supported
  consecutive := by intro z hz; simp at hz; subst z; simp

theorem nil_choices (zs : List Bool) : choiceBlocks (fun _ => ([] : List Label)) zs = [] := by
  induction zs with
  | nil => rfl
  | cons i zs ih => simp [choiceBlocks,ih]

def nilPath (zs : List Bool) : OriginalPiecePath ({0} : Finset ℝ)
    ([]++choiceBlocks (fun _ => []) zs) .G0 zeroPiece where
  guards := fun _ => .G0
  pieces := fun _ => zeroPiece
  initial_guard := rfl
  terminal_guard := rfl
  terminal_piece := rfl
  edges := by intro p hp; simp [nil_choices] at hp

theorem zero_selection :
    ({z : ℝ | ∀ n, (compose [])^[n] z ∈ CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => [])}
      ∩ piece_carrier zeroPiece).Nonempty := by
  refine ⟨0, ?_, ?_⟩
  · intro n
    change (id^[n]) (0 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => [])
    simpa only [Function.iterate_id, id_eq] using
      (show (0 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => []) from
        ⟨zero_supported,by intro p hp; simp at hp,by intro i p hp; simp at hp⟩)
  · simp [piece_carrier,zeroPiece]

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro law
  obtain ⟨tail,x,path,bad,rest⟩ := law (fun _ => false) 0 le_rfl .G0 [] [] [] (fun _ => [])
    rfl rfl rfl (fun _ => rfl) {0} zeroPiece zero_selection nilPath
  cases bad

theorem dependence : ObservationalDependence observationSignature actual := by
  intro i
  refine ⟨(), (fun _ => .G0), (fun _ => .G1), ?_⟩
  simp [actual,realize]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces.selected_original_piece_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.OriginalPieces.selected_original_piece_tail, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

end
end Reg.Support.FibonacciOriginalSourceWitness.Source130
