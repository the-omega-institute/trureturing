/- GID: D5/S3/ConceptDynamics/Coding/EssentialWordRealization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/EssentialWordRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Essential finite directed multigraphs admit an actual Int-indexed legal history containing every edge of every positive legal finite word. -/

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.EssentialWordRealization

universe u v

structure DirectedMultigraph (V : Type u) (E : Type v) where
  source : E → V
  target : E → V

structure Essential {V : Type u} {E : Type v} (G : DirectedMultigraph V E) : Prop where
  outgoing : ∀ v, ∃ e, G.source e = v
  incoming : ∀ v, ∃ e, G.target e = v

structure LegalWord {V : Type u} {E : Type v} (G : DirectedMultigraph V E) (n : ℕ) where
  edge : Fin n → E
  legal : ∀ (i : Fin n) (hi : i.val + 1 < n),
    G.target (edge i) = G.source (edge ⟨i.val + 1, hi⟩)

abbrev History {V : Type u} {E : Type v} (G : DirectedMultigraph V E) :=
  {x : ℤ → E // ∀ i : ℤ, G.target (x i) = G.source (x (i + 1))}

variable {V : Type u} {E : Type v}
  [Fintype V] [Fintype E] [DecidableEq V]

noncomputable def outgoingChoice (G : DirectedMultigraph V E) (h : Essential G) (v : V) : E :=
  Classical.choose (h.outgoing v)

theorem outgoingChoice_source (G : DirectedMultigraph V E) (h : Essential G) (v : V) :
    G.source (outgoingChoice G h v) = v :=
  Classical.choose_spec (h.outgoing v)

noncomputable def incomingChoice (G : DirectedMultigraph V E) (h : Essential G) (v : V) : E :=
  Classical.choose (h.incoming v)

theorem incomingChoice_target (G : DirectedMultigraph V E) (h : Essential G) (v : V) :
    G.target (incomingChoice G h v) = v :=
  Classical.choose_spec (h.incoming v)

noncomputable def forwardStep (G : DirectedMultigraph V E) (h : Essential G) (e : E) : E :=
  outgoingChoice G h (G.target e)

theorem forwardStep_source (G : DirectedMultigraph V E) (h : Essential G) (e : E) :
    G.source (forwardStep G h e) = G.target e :=
  outgoingChoice_source G h _

noncomputable def backwardStep (G : DirectedMultigraph V E) (h : Essential G) (e : E) : E :=
  incomingChoice G h (G.source e)

theorem backwardStep_target (G : DirectedMultigraph V E) (h : Essential G) (e : E) :
    G.target (backwardStep G h e) = G.source e :=
  incomingChoice_target G h _

noncomputable def forwardTail (G : DirectedMultigraph V E) (h : Essential G) (e : E) : ℕ → E :=
  fun n => (forwardStep G h)^[n] e

noncomputable def backwardTail (G : DirectedMultigraph V E) (h : Essential G) (e : E) : ℕ → E :=
  fun n => (backwardStep G h)^[n] e

theorem forwardTail_succ (G : DirectedMultigraph V E) (h : Essential G) (e : E) (n : ℕ) :
    forwardTail G h e (n + 1) = forwardStep G h (forwardTail G h e n) := by
  simp [forwardTail, Function.iterate_succ_apply']

theorem forwardTail_seam (G : DirectedMultigraph V E) (h : Essential G) (e : E) (n : ℕ) :
    G.target (forwardTail G h e n) = G.source (forwardTail G h e (n + 1)) := by
  rw [forwardTail_succ]
  exact (forwardStep_source G h _).symm

theorem backwardTail_succ (G : DirectedMultigraph V E) (h : Essential G) (e : E) (n : ℕ) :
    backwardTail G h e (n + 1) = backwardStep G h (backwardTail G h e n) := by
  simp [backwardTail, Function.iterate_succ_apply']

theorem backwardTail_seam (G : DirectedMultigraph V E) (h : Essential G) (e : E) (n : ℕ) :
    G.target (backwardTail G h e (n + 1)) = G.source (backwardTail G h e n) := by
  rw [backwardTail_succ]
  exact backwardStep_target G h _

noncomputable def realized (G : DirectedMultigraph V E) (h : Essential G)
    {n : ℕ} (w : LegalWord G n) (hn : 0 < n) : ℤ → E :=
  fun z => match z with
  | Int.negSucc k => backwardTail G h (w.edge ⟨0, hn⟩) (k + 1)
  | Int.ofNat k =>
      if hk : k < n then w.edge ⟨k, hk⟩
      else forwardTail G h (w.edge ⟨n - 1, by omega⟩) (k - n + 1)

theorem realized_contains (G : DirectedMultigraph V E) (h : Essential G)
    {n : ℕ} (w : LegalWord G n) (hn : 0 < n) (i : Fin n) :
    realized G h w hn (i : ℤ) = w.edge i := by
  simp [realized, i.isLt]

theorem realized_legal (G : DirectedMultigraph V E) (h : Essential G)
    {n : ℕ} (w : LegalWord G n) (hn : 0 < n) :
    ∀ i : ℤ, G.target (realized G h w hn i) =
      G.source (realized G h w hn (i + 1)) := by
  intro i
  cases i with
  | negSucc k =>
      cases k with
      | zero =>
          have hz : (0 : ℕ) < n := hn
          have hi : (Int.negSucc 0 : ℤ) + 1 = 0 := by decide
          rw [hi]
          simp only [realized]
          rw [dif_pos hz]
          simpa [backwardTail] using (backwardTail_seam G h (w.edge ⟨0, hn⟩) 0)
      | succ k =>
          have hi : (Int.negSucc (k + 1) : ℤ) + 1 = Int.negSucc k := by omega
          rw [hi]
          simp only [realized]
          rw [backwardTail_seam]
  | ofNat k =>
      by_cases hk : k + 1 < n
      · have hk0 : k < n := by omega
        have hi : (Int.ofNat k : ℤ) + 1 = Int.ofNat (k + 1) := by simp
        rw [hi]
        simp only [realized, dif_pos hk0, dif_pos hk]
        exact w.legal ⟨k, hk0⟩ hk
      · by_cases hkn : k < n
        · have hlast : k = n - 1 := by omega
          subst k
          have h₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
          have hnat : n - 1 + 1 = n := Nat.sub_add_cancel h₁
          have hi : (Int.ofNat (n - 1) : ℤ) + 1 = Int.ofNat n := by
            change (↑(n - 1) : Int) + (↑(1 : ℕ) : Int) = ↑n
            rw [← Int.natCast_add]
            exact_mod_cast hnat
          rw [hi]
          have hA : n - 1 < n := by omega
          have hB : ¬ n < n := by omega
          simpa [realized, hA, hB, forwardTail] using
            (forwardStep_source G h (w.edge ⟨n - 1, by omega⟩)).symm
        · have hkn' : ¬ k + 1 < n := by omega
          have hi : (Int.ofNat k : ℤ) + 1 = Int.ofNat (k + 1) := by simp
          rw [hi]
          simp only [realized, dif_neg hkn, dif_neg (by omega)]
          have hshift : k + 1 - n + 1 = (k - n + 1) + 1 := by omega
          simpa [Nat.add_assoc, hshift] using
            (show G.target (forwardTail G h (w.edge ⟨n - 1, by omega⟩) (k - n + 1)) =
              G.source (forwardTail G h (w.edge ⟨n - 1, by omega⟩) (k - n + 1 + 1)) by
              exact forwardTail_seam G h (w.edge ⟨n - 1, by omega⟩) (k - n + 1))

theorem exists_history_containing (G : DirectedMultigraph V E) (h : Essential G)
    {n : ℕ} (w : LegalWord G n) (hn : 0 < n) :
    ∃ x : History G, ∀ i : Fin n, x.1 (i : ℤ) = w.edge i := by
  refine ⟨⟨realized G h w hn, realized_legal G h w hn⟩, ?_⟩
  exact realized_contains G h w hn

theorem every_prescribed_word_has_actual_history (G : DirectedMultigraph V E)
    (h : Essential G) {n : ℕ} (w : LegalWord G n) (hn : 0 < n) :
    ∃ x : History G, ∀ i : Fin n, x.1 (i : ℤ) = w.edge i :=
  exists_history_containing G h w hn

end D5.S3.ConceptDynamics.Coding.EssentialWordRealization
