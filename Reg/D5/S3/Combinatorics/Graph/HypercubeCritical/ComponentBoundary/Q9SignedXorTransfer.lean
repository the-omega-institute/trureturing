import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer
import Reg.Support.SingleDependentReadout

/-! The observation pairs two cell traces via the ordered signed XOR action. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer

noncomputable section

open scoped Matrix
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q gamma)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord (gamma_square)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells (parityPart)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private abbrev Vec := Q 9 → ℝ
private abbrev Parameters := Σ _ : Fin 9, Fin 9

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => Vec × Vec) (fun _ => ℝ)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ (I : Finset (Fin 9)) (a b : Fin 9) (hab : a ≠ b) (hI : I.card = 3)
    (ha : a ∉ I) (hb : b ∉ I) (p q : Bool) (f g : Vec)
    (hf : maskOperator I f + gamma a f = (2 : ℝ) • f)
    (hg : maskOperator I g + gamma b g = (2 : ℝ) • g),
    let B := maskOperator I
    let f₀ := cellPart a b p q f
    let g₀ := cellPart a b p q g
    let f₁ := cellPart a b (!p) q f
    let g₁ := cellPart a b p (!q) g
    let pair := r.readout () ⟨a, b⟩ (f₁, g₁)
    let S := fun t => parityPart t f₀ ⬝ᵥ parityPart t g₀
    let D := fun t => signedXorPair a b (parityPart t f₁, parityPart t g₁)
    let L := f₀ ⬝ᵥ B g₀
    f₁ = gamma a ((2 : ℝ) • f₀ - B f₀) ∧
    g₁ = gamma b ((2 : ℝ) • g₀ - B g₀) ∧
    pair = f₀ ⬝ᵥ ((7 : ℝ) • g₀ - (4 : ℝ) • B g₀) ∧
    (∀ t, D t = 3 * S t + 4 * S (!t) - 2 * L) ∧
    D false - D true = S true - S false

private def actual : Realization signature :=
  realize signature (fun _ p fg => signedXorPair p.1 p.2 fg) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) Empty.elim

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law {0, 1, 2} 3 4 (by decide) (by decide) (by decide) (by decide)
    false false 0 0 (by simp) (by simp)).2.2.1
  have : (1 : ℝ) = 0 := by simpa [rejected, realize] using h
  exact one_ne_zero this

def sourceEvidence : Registration arena (type_of% @overlapping_mask_signed_xor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨overlapping_mask_signed_xor, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    let u : Vec := fun _ => 1
    refine ⟨⟨0, 1⟩, (0, 0), (u, gamma 1 (gamma 0 u)), ?_⟩
    change signedXorPair 0 1 (0, 0) ≠ signedXorPair 0 1 (u, gamma 1 (gamma 0 u))
    simp only [signedXorPair, Prod.fst, Prod.snd, gamma_square, zero_dotProduct]
    exact ne_of_lt (Finset.sum_pos (fun x _ => by norm_num [u]) Finset.univ_nonempty)

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@overlapping_mask_signed_xor) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer.overlapping_mask_signed_xor.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p fg => signedXorPair p.1 p.2 fg) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer
