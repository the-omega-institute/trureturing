import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.LowDegreeFaithfulExtension

/-! The final distance readout is varied on its actual Euclidean domain;
the full source telescope and every fixed-placement condition are retained. -/

noncomputable section
set_option maxHeartbeats 1000000

open _root_.D5.S3.Geometry.LowDegreeFaithfulExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.LowDegreeFaithfulExtension

universe u
local notation "E₅" => EuclideanSpace ℝ (Fin 5)

abbrev signature : Signature where
  Params := Unit
  State _ := E₅
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := E₅ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => dist x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (B s : Finset V) (hBs : B ⊆ s) (p : s → E₅),
    Function.Injective p →
    (∀ u v : s, G.Adj u.val v.val ↔ dist (p u) (p v) = 1) →
    (∀ (b : V) (hb : b ∈ B) (c : V) (hc : c ∈ B), b ≠ c →
      dist (p ⟨b, hBs hb⟩) (p ⟨c, hBs hc⟩) < 2) →
    (∀ a ∉ s, G.neighborFinset a ⊆ B) →
    (∀ a ∉ s, G.degree a ≤ 2) →
    ∃ P : V → E₅, Function.Injective P ∧
      (∀ u v : V, G.Adj u v ↔ R.readout () () (P u) (P v) = 1) ∧
      ∀ u : s, P u.val = p u

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let v₀ : ULift.{u} (Fin 2) := ⟨0⟩
  let v₁ : ULift.{u} (Fin 2) := ⟨1⟩
  obtain ⟨P, _, hP, _⟩ := h (V := ULift.{u} (Fin 2)) ⊤ {v₁} {v₁}
    Finset.Subset.rfl (fun _ => 0)
    (by
      intro a b _
      exact Subtype.ext ((Finset.mem_singleton.mp a.property).trans
        (Finset.mem_singleton.mp b.property).symm))
    (by
      intro a b
      have hab : a.val = b.val := (Finset.mem_singleton.mp a.property).trans
        (Finset.mem_singleton.mp b.property).symm
      simp [hab])
    (by intros; norm_num)
    (by
      intro a ha b hb
      have hab : b ≠ a := by simpa using hb
      have ha1 : a ≠ v₁ := by simpa using ha
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      fin_cases a <;> fin_cases b <;> simp_all [v₁])
    (by
      intro a _
      have hh := (⊤ : SimpleGraph (ULift.{u} (Fin 2))).degree_lt_card_verts a
      have hc : Fintype.card (ULift.{u} (Fin 2)) = 2 := by simp
      omega)
  have hh := (hP v₀ v₁).mp (by simp [v₀, v₁])
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨e, he⟩ := exists_norm_eq E₅ (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨(), 0, e, ?_⟩
  intro hh
  have h := congrFun hh 0
  change dist (0 : E₅) 0 = dist e 0 at h
  rw [dist_self, dist_zero_right, he] at h
  norm_num at h

def family : Registration arena.{u} (type_of% (@exists_faithful_extension.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_faithful_extension.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

end Reg.D5.S3.Geometry.LowDegreeFaithfulExtension
