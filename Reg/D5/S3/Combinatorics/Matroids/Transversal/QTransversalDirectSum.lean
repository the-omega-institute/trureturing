import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.Transversal.QTransversalDirectSum

/-! The concatenated rank as a source observation on the combined subspace. -/

namespace Reg.D5.S3.Combinatorics.Matroids.Transversal.QTransversalDirectSum

open LeanInformationAudit Module Submodule
open _root_.D5.S3.Combinatorics.Matroids.QTransversalRepresentability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev signature : Signature where
  Params := Σ F : Type, Σ _f : Field F, Σ _m : ℕ, Σ _n : ℕ, Σ _k : ℕ, Σ _l : ℕ,
    Σ _X : Fin _k → Submodule F (Fin _m → F), Fin _l → Submodule F (Fin _n → F)
  State := fun ⟨F, _f, m, n, _, _, _⟩ => Submodule F (Fin (m + n) → F)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ⟨F, f, m, n, k, l, X, Y⟩ U =>
    @qTransversalRank F f (m + n) (k + l) (@concatenatedPresentation F f m n k l X Y) U)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {F : Type} [f : Field F] [Fintype F] {m n k l : ℕ}
    (X : Fin k → Submodule F (Fin m → F)) (Y : Fin l → Submodule F (Fin n → F))
    (U : Submodule F (Fin (m + n) → F)),
    r.readout () ⟨F, f, m, n, k, l, X, Y⟩ U =
      sInf {d | ∃ W ≤ U, d = qTransversalRank X (W.map firstProjection) +
        qTransversalRank Y (W.map secondProjection) + (finrank F U - finrank F W)}

private theorem rank_bot {F : Type} [Field F] [Fintype F] {m k : ℕ}
    (X : Fin k → Submodule F (Fin m → F)) : qTransversalRank X ⊥ = 0 := by
  classical
  rw [presentation_rank_eq_hallMinimum]
  apply Nat.eq_zero_of_le_zero
  refine Nat.sInf_le ⟨Finset.univ, ?_⟩
  simp

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h (F := ZMod 2) (m := 0) (n := 0) (k := 0) (l := 0)
    (fun _ => ⊥) (fun _ => ⊥) ⊥
  have hactual := fulcher_conjecture_4_8 (F := ZMod 2) (m := 0) (n := 0) (k := 0) (ℓ := 0)
    (fun _ => ⊥) (fun _ => ⊥) ⊥
  rw [rank_bot] at hactual
  exact Nat.one_ne_zero (hzero.trans hactual.symm)

private def sampleX : Fin 1 → Submodule (ZMod 2) (Fin 1 → ZMod 2) := fun _ => ⊥
private def sampleY : Fin 0 → Submodule (ZMod 2) (Fin 0 → ZMod 2) := fun _ => ⊥

private theorem sample_slot (i : Fin (1 + 0)) : concatenatedPresentation sampleX sampleY i = ⊥ := by
  refine Fin.addCases ?_ (fun j => Fin.elim0 j) i
  intro j
  rw [concatenatedPresentation, Fin.append_left]
  change (⊥ : Submodule (ZMod 2) (Fin 1 → ZMod 2)).comap firstProjection = ⊥
  rw [Submodule.comap_bot]
  apply LinearMap.ker_eq_bot.mpr
  intro v w hvw
  apply (splitCoordinates (F := ZMod 2) (m := 1) (n := 0)).injective
  exact Prod.ext hvw (Subsingleton.elim _ _)

private theorem sample_rank :
    qTransversalRank (concatenatedPresentation sampleX sampleY) ⊤ = 1 := by
  classical
  rw [presentation_rank_eq_hallMinimum]
  apply le_antisymm
  · refine Nat.sInf_le ⟨∅, ?_⟩
    simp
  · apply le_csInf
    · exact Set.range_nonempty _
    rintro d ⟨J, rfl⟩
    by_cases h : J.Nonempty
    · obtain ⟨i, hi⟩ := h
      have hInf : (⨅ j : {j : Fin (1 + 0) // j ∈ J},
          concatenatedPresentation sampleX sampleY j.1) = ⊥ :=
        bot_unique ((iInf_le _ ⟨i, hi⟩).trans_eq (sample_slot i))
      dsimp only
      rw [hInf, inf_bot_eq, finrank_bot, Nat.sub_zero]
      simp
    · have hJ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [hJ]

def source_registration : Registration arena (type_of% (@fulcher_conjecture_4_8)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fulcher_conjecture_4_8, rejected, rejected_law⟩
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
    refine ⟨⟨ZMod 2, inferInstance, 1, 0, 1, 0, sampleX, sampleY⟩, ⊥, ⊤, ?_⟩
    change qTransversalRank (concatenatedPresentation sampleX sampleY) ⊥ ≠
      qTransversalRank (concatenatedPresentation sampleX sampleY) ⊤
    rw [rank_bot, sample_rank]
    exact Nat.zero_ne_one

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fulcher_conjecture_4_8) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.QTransversalRepresentability.fulcher_conjecture_4_8.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.Transversal.QTransversalDirectSum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.Transversal.QTransversalDirectSum
    definition := none
    coordinates := #[0, 3, 4, 5, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.Transversal.QTransversalDirectSum
