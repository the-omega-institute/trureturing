import D5.S3.Factorization.Collinear.SlopeFilteredTripleFixedPoints
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Factorization.Collinear.SlopeFilteredTripleFixedPoints

open _root_.D5.S3.Factorization.Collinear.SlopeFilteredTripleFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ n : ℕ, ZMod n
  State p := ZMod p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p t => Nat.card (AddAction.fixedBy (SlopeTriple p.1 p.2) t))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) [NeZero n] (a t : ZMod n), t ≠ 0 →
    r.readout () ⟨n, a⟩ t =
      if 3 • t = 0 ∧ a * t ≠ 0 then n / 3 else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 3 (1 : ZMod 3) (1 : ZMod 3) (by decide)
  have hcase : 3 • (1 : ZMod 3) = 0 ∧
      (1 : ZMod 3) * (1 : ZMod 3) ≠ 0 := by decide
  change (0 : ℕ) = if 3 • (1 : ZMod 3) = 0 ∧
    (1 : ZMod 3) * (1 : ZMod 3) ≠ 0 then 3 / 3 else 0 at hbad
  rw [if_pos hcase] at hbad
  norm_num at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro n _ a t ht0
    simpa [arena, actual, realize] using card_fixedBy_nonzero n a t ht0,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨4, (1 : ZMod 4)⟩, (0 : ZMod 4), (1 : ZMod 4), ?_⟩
    have hthree : 3 • (1 : ZMod 4) ≠ 0 := by decide
    have hzero : Nat.card (AddAction.fixedBy (SlopeTriple 4 1) (1 : ZMod 4)) = 0 := by
      have h := card_fixedBy_nonzero 4 1 1 (by decide)
      rw [if_neg (by intro hcase; exact hthree hcase.1)] at h
      exact h
    let X : SlopeTriple 4 1 := ⟨{0, 1, 2}, by decide, by decide⟩
    have hpositive : 0 < Nat.card (AddAction.fixedBy (SlopeTriple 4 1) (0 : ZMod 4)) :=
      Nat.card_pos_iff.mpr ⟨⟨X, by simp [AddAction.mem_fixedBy]⟩, inferInstance⟩
    change Nat.card (AddAction.fixedBy (SlopeTriple 4 1) (0 : ZMod 4)) ≠
      Nat.card (AddAction.fixedBy (SlopeTriple 4 1) (1 : ZMod 4))
    rw [hzero]
    omega

register_information_theorem card_fixedBy_nonzero in arena
  readout via (realize signature
    (fun _ p t => Nat.card (AddAction.fixedBy (SlopeTriple p.1 p.2) t))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Collinear.SlopeFilteredTripleFixedPoints
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Factorization.Collinear.SlopeFilteredTripleFixedPoints
