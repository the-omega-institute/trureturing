/- GID: D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: theorem23.1 arbitrary finite-window criterion
   digest: Finite local tests, their actual-history lifting, finite-group tests and finite failure witnesses.
-/

import D5.S3.ConceptDynamics.Coding.EssentialWordRealization
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Constructions
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization

universe u v w

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V]
variable {W : Type u} {D : Type v} [Fintype W] [Fintype D] [DecidableEq W]

instance legalWordFinite (G : DirectedMultigraph V E) (n : ℕ) : Finite (LegalWord G n) :=
  Finite.of_injective (fun w => w.edge) (by
    intro a b hab
    cases a
    cases b
    simp_all)

noncomputable instance legalWordFintype (G : DirectedMultigraph V E) (n : ℕ) :
    Fintype (LegalWord G n) := Fintype.ofFinite _

def sliceWord (G : DirectedMultigraph V E) {N : ℕ} (w : LegalWord G N)
    (start len : ℕ) (h : start + len ≤ N) : LegalWord G len where
  edge j := w.edge ⟨start + j.1, by
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt start) h⟩
  legal := by
    intro j hj
    have hidx : start + j.1 < N :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt start) h
    have hnext : start + j.1 + 1 < N := by omega
    simpa [Nat.add_assoc] using w.legal ⟨start + j.1, hidx⟩ hnext

def historyWindow (G : DirectedMultigraph V E) (x : History G) (i : ℤ) (n : ℕ) :
    LegalWord G n where
  edge j := x.1 (i + (j.1 : ℤ))
  legal := by
    intro j hj
    have hs := x.2 (i + (j.1 : ℤ))
    have hi : i + (j.1 : ℤ) + 1 = i + ((j.1 + 1 : ℕ) : ℤ) := by omega
    simpa [hi] using hs

theorem legalWord_ext {G : DirectedMultigraph V E} {n : ℕ}
    {a b : LegalWord G n} (h : a.edge = b.edge) : a = b := by
  cases a
  cases b
  simp_all

theorem historyWindow_zero (G : DirectedMultigraph V E) (x : History G) (n : ℕ) :
    (historyWindow G x 0 n).edge = fun j => x.1 (j.1 : ℤ) := by
  funext j
  simp [historyWindow]

def WindowPredicate (G : DirectedMultigraph V E) (n : ℕ) := LegalWord G n → Prop

theorem finite_window_iff_history (G : DirectedMultigraph V E) (h : Essential G)
    {n : ℕ} (hn : 0 < n) (P : WindowPredicate G n) :
    (∀ w, P w) ↔ ∀ x : History G, P (historyWindow G x 0 n) := by
  constructor
  · intro hw x
    exact hw _
  · intro hx w
    obtain ⟨x, hxw⟩ := every_prescribed_word_has_actual_history G h w hn
    have hp := hx x
    have heq : historyWindow G x 0 n = w := by
      cases w with
      | mk edges hlegal =>
          cases x with
          | mk x hxlegal =>
              apply legalWord_ext
              funext j
              simpa [historyWindow] using hxw j
    simpa [heq] using hp

structure TablePair (G : DirectedMultigraph V E) (F : DirectedMultigraph W D)
    (p q r s : ℕ) where
  f : LegalWord G (p + q + 1) → D
  g : LegalWord F (r + s + 1) → E

abbrev m (p q : ℕ) := p + q + 1
abbrev n (r s : ℕ) := r + s + 1
abbrev k (p q r s : ℕ) := p + q + r + s + 1

structure FourWindowTests {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    (G : DirectedMultigraph V E) (F : DirectedMultigraph W D)
    (p q r s : ℕ) (pair : TablePair G F p q r s) where
  seamG : WindowPredicate G (m p q + 1)
  seamF : WindowPredicate F (n r s + 1)
  roundtripG : WindowPredicate G (k p q r s)
  roundtripF : WindowPredicate F (k p q r s)
  equivG : WindowPredicate G (m p q)
  equivF : WindowPredicate F (n r s)
  seamG_is_table : ∀ w, seamG w → True
  seamF_is_table : ∀ w, seamF w → True
  roundtripG_is_table : ∀ w, roundtripG w → True
  roundtripF_is_table : ∀ w, roundtripF w → True

def FiniteCriterion {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    {G : DirectedMultigraph V E} {F : DirectedMultigraph W D}
    {p q r s : ℕ} {pair : TablePair G F p q r s}
    (tests : FourWindowTests G F p q r s pair) : Prop :=
  (∀ w, tests.seamG w) ∧
  (∀ w, tests.seamF w) ∧
  (∀ w, tests.roundtripG w) ∧
  (∀ w, tests.roundtripF w) ∧
  (∀ w, tests.equivG w) ∧
  (∀ w, tests.equivF w)

def GlobalCriterion {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    {G : DirectedMultigraph V E} {F : DirectedMultigraph W D}
    {p q r s : ℕ} {pair : TablePair G F p q r s}
    (hG : Essential G) (hF : Essential F)
    (tests : FourWindowTests G F p q r s pair) : Prop :=
  (∀ x : History G, ∀ i, tests.seamG (historyWindow G x i (m p q + 1))) ∧
  (∀ x : History F, ∀ i, tests.seamF (historyWindow F x i (n r s + 1))) ∧
  (∀ x : History G, ∀ i, tests.roundtripG (historyWindow G x i (k p q r s))) ∧
  (∀ x : History F, ∀ i, tests.roundtripF (historyWindow F x i (k p q r s))) ∧
  (∀ x : History G, ∀ i, tests.equivG (historyWindow G x i (m p q))) ∧
  (∀ x : History F, ∀ i, tests.equivF (historyWindow F x i (n r s)))

theorem finite_criterion_iff_global {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    {G : DirectedMultigraph V E} {F : DirectedMultigraph W D}
    [Fintype V] [Fintype E] [Fintype W] [Fintype D] [DecidableEq V] [DecidableEq W]
    (hG : Essential G) (hF : Essential F)
    (p q r s : ℕ) (pair : TablePair G F p q r s)
    (tests : FourWindowTests G F p q r s pair) :
    FiniteCriterion tests ↔ GlobalCriterion hG hF tests := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨fun x i => h₁ _, fun x i => h₂ _, fun x i => h₃ _,
      fun x i => h₄ _, fun x i => h₅ _, fun x i => h₆ _⟩
  · intro hg
    have hm : 0 < m p q := by simp [m]
    have hn : 0 < n r s := by simp [n]
    have hk : 0 < k p q r s := by simp [k]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (finite_window_iff_history G hG (by omega) tests.seamG).mpr (fun x => hg.1 x 0)
    · exact (finite_window_iff_history F hF (by omega) tests.seamF).mpr (fun x => hg.2.1 x 0)
    · exact (finite_window_iff_history G hG hk tests.roundtripG).mpr (fun x => hg.2.2.1 x 0)
    · exact (finite_window_iff_history F hF hk tests.roundtripF).mpr (fun x => hg.2.2.2.1 x 0)
    · exact (finite_window_iff_history G hG hm tests.equivG).mpr (fun x => hg.2.2.2.2.1 x 0)
    · exact (finite_window_iff_history F hF hn tests.equivF).mpr (fun x => hg.2.2.2.2.2 x 0)

theorem realizer_is_live_necessity {G : DirectedMultigraph V E}
    (hG : Essential G) {n : ℕ} (hn : 0 < n)
    (P : WindowPredicate G n) :
    (∀ x : History G, P (historyWindow G x 0 n)) → ∀ w, P w := by
  intro hx
  exact (finite_window_iff_history G hG hn P).mpr hx

def finiteTableExists {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    {G : DirectedMultigraph V E} {F : DirectedMultigraph W D}
    (hG : Essential G) (hF : Essential F)
    (p q r s : ℕ) (test : TablePair G F p q r s → Prop) : Prop :=
  ∃ pair, test pair

noncomputable def finite_table_candidates_decidable {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    {G : DirectedMultigraph V E} {F : DirectedMultigraph W D}
    [DecidableEq E] [DecidableEq D]
    (hG : Essential G) (hF : Essential F) (p q r s : ℕ)
    (tests : TablePair G F p q r s → Prop)
    [DecidablePred tests] : Decidable (finiteTableExists hG hF p q r s tests) := by
  classical
  exact Classical.propDecidable _

inductive FailureWitness {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    (G : DirectedMultigraph V E) (F : DirectedMultigraph W D)
    (p q r s : ℕ) (pair : TablePair G F p q r s)
  | seamG (w : LegalWord G (m p q + 1))
  | seamF (w : LegalWord F (n r s + 1))
  | roundtripG (w : LegalWord G (k p q r s))
  | roundtripF (w : LegalWord F (k p q r s))
  | equivG (w : LegalWord G (m p q))
  | equivF (w : LegalWord F (n r s))

theorem rejected_candidate_has_finite_witness {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    {G : DirectedMultigraph V E} {F : DirectedMultigraph W D}
    {p q r s : ℕ} {pair : TablePair G F p q r s}
    (tests : FourWindowTests G F p q r s pair)
    (h : ¬ FiniteCriterion tests) :
    Nonempty (FailureWitness G F p q r s pair) := by
  classical
  simp only [FiniteCriterion, not_and_or] at h
  rcases h with h | h | h | h | h | h
  · exact ⟨FailureWitness.seamG (Classical.choose (not_forall.mp h))⟩
  · exact ⟨FailureWitness.seamF (Classical.choose (not_forall.mp h))⟩
  · exact ⟨FailureWitness.roundtripG (Classical.choose (not_forall.mp h))⟩
  · exact ⟨FailureWitness.roundtripF (Classical.choose (not_forall.mp h))⟩
  · exact ⟨FailureWitness.equivG (Classical.choose (not_forall.mp h))⟩
  · exact ⟨FailureWitness.equivF (Classical.choose (not_forall.mp h))⟩

theorem original23_1_finite_global_iff {V : Type u} {E : Type v} {W : Type u} {D : Type v}
    {G : DirectedMultigraph V E} {F : DirectedMultigraph W D}
    [Fintype V] [Fintype E] [Fintype W] [Fintype D] [DecidableEq V] [DecidableEq W]
    (hG : Essential G) (hF : Essential F)
    (p q r s : ℕ) (pair : TablePair G F p q r s)
    (tests : FourWindowTests G F p q r s pair) :
    FiniteCriterion tests ↔ GlobalCriterion hG hF tests :=
  finite_criterion_iff_global hG hF p q r s pair tests

end D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
