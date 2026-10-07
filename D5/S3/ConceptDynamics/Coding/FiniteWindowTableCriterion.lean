/- GID: D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.originalExistenceDecidable; instance=D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion.orderedD8Input
   digest: Concrete seam and center tests characterize the same two continuous shift-commuting table maps on all actual histories. -/

import D5.S3.ConceptDynamics.Coding.EssentialWordRealization
import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Constructions
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization

universe u v w z

variable {V : Type u} {E : Type v} {W : Type w} {D : Type z}
variable (G : DirectedMultigraph V E) (F : DirectedMultigraph W D)

@[ext] theorem legalWord_ext {G : DirectedMultigraph V E} {n : ℕ}
    {a b : LegalWord G n} (h : a.edge = b.edge) : a = b := by
  cases a
  cases b
  simp_all

def wordEquiv (n : ℕ) : LegalWord G n ≃
    {e : Fin n → E // ∀ i : Fin n, ∀ hi : i.val + 1 < n,
      G.target (e i) = G.source (e ⟨i.val + 1, hi⟩)} where
  toFun w := ⟨w.edge, w.legal⟩
  invFun w := ⟨w.val, w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance legalWordFintype [Fintype E] [DecidableEq V] (n : ℕ) :
    Fintype (LegalWord G n) := Fintype.ofEquiv _ (wordEquiv G n).symm

instance legalWordDecidableEq [DecidableEq E] (n : ℕ) :
    DecidableEq (LegalWord G n) := fun a b =>
  decidable_of_iff (a.edge = b.edge) ⟨legalWord_ext, congrArg LegalWord.edge⟩

def sliceWord {N : ℕ} (w : LegalWord G N)
    (start len : ℕ) (h : start + len ≤ N) : LegalWord G len where
  edge j := w.edge ⟨start + j.val, by omega⟩
  legal := by
    intro j hj
    have hidx : start + j.val < N := by omega
    have hnxt : start + j.val + 1 < N := by omega
    simpa [Nat.add_assoc] using w.legal ⟨start + j.val, hidx⟩ hnxt

def historyWindow (x : History G) (i : ℤ) (n : ℕ) : LegalWord G n where
  edge j := x.val (i + (j.val : ℤ))
  legal := by
    intro j hj
    simpa [Int.natCast_add, add_assoc] using x.property (i + (j.val : ℤ))

theorem slice_slice {N : ℕ} (w : LegalWord G N)
    (a L b M : ℕ) (h : a + L ≤ N) (h' : b + M ≤ L) :
    sliceWord G (sliceWord G w a L h) b M h' =
      sliceWord G w (a + b) M (by omega) := by
  apply legalWord_ext
  funext j
  change w.edge ⟨a + (b + j.val), _⟩ = w.edge ⟨a + b + j.val, _⟩
  apply congrArg w.edge
  apply Fin.ext
  dsimp
  omega

theorem slice_historyWindow (x : History G) (i : ℤ)
    (N a L : ℕ) (h : a + L ≤ N) :
    sliceWord G (historyWindow G x i N) a L h =
      historyWindow G x (i + (a : ℤ)) L := by
  apply legalWord_ext
  funext j
  simp [sliceWord, historyWindow, Int.natCast_add, add_assoc]

theorem window_of_contains {N : ℕ} (w : LegalWord G N) (x : History G)
    (hx : ∀ j : Fin N, x.val (j.val : ℤ) = w.edge j)
    (a L : ℕ) (h : a + L ≤ N) :
    historyWindow G x (a : ℤ) L = sliceWord G w a L h := by
  apply legalWord_ext
  funext j
  simpa [historyWindow, sliceWord, Int.natCast_add] using hx ⟨a + j.val, by omega⟩

def Seam {M : ℕ} (f : LegalWord G M → D) : Prop :=
  ∀ w : LegalWord G (M + 1),
    F.target (f (sliceWord G w 0 M (by omega))) =
      F.source (f (sliceWord G w 1 M (by omega)))

def mapBlock {M N L : ℕ} (f : LegalWord G M → D)
    (hf : Seam G F f) (w : LegalWord G N)
    (hm : 0 < M) (h : M + L ≤ N + 1) : LegalWord F L where
  edge j := f (sliceWord G w j.val M (by omega))
  legal := by
    intro j hj
    have hs := hf (sliceWord G w j.val (M + 1) (by omega))
    simpa only [slice_slice, Nat.add_zero, Nat.add_assoc] using hs

structure TablePair (p q r s : ℕ) where
  f : LegalWord G (p + q + 1) → D
  g : LegalWord F (r + s + 1) → E

variable {G F}

structure LocalCriterion {p q r s : ℕ} (pair : TablePair G F p q r s) : Prop where
  seamG : Seam G F pair.f
  seamF : Seam F G pair.g
  roundtripG : ∀ w : LegalWord G (p + q + r + s + 1),
    pair.g (mapBlock G F pair.f seamG w (by omega) (by omega)) =
      w.edge ⟨p + r, by omega⟩
  roundtripF : ∀ w : LegalWord F (p + q + r + s + 1),
    pair.f (mapBlock F G pair.g seamF w (by omega) (by omega)) =
      w.edge ⟨p + r, by omega⟩

variable (G F)

def applyTable {a b : ℕ} (f : LegalWord G (a + b + 1) → D)
    (hf : Seam G F f) (x : History G) : History F where
  val i := f (historyWindow G x (i - (a : ℤ)) (a + b + 1))
  property i := by
    have hs := hf (historyWindow G x (i - (a : ℤ)) (a + b + 1 + 1))
    simpa only [slice_historyWindow, Int.natCast_zero, Int.natCast_one,
      add_zero, sub_add_eq_add_sub] using hs

def shift (x : History G) : History G :=
  ⟨fun i => x.val (i + 1), fun i => by simpa [add_assoc] using x.property (i + 1)⟩

theorem applyTable_shift {a b : ℕ} (f : LegalWord G (a + b + 1) → D)
    (hf : Seam G F f) (x : History G) :
    applyTable G F f hf (shift G x) = shift F (applyTable G F f hf x) := by
  apply Subtype.ext
  funext i
  change f (historyWindow G (shift G x) (i - (a : ℤ)) _) =
    f (historyWindow G x (i + 1 - (a : ℤ)) _)
  congr 1
  apply legalWord_ext
  funext j
  change x.val (i - (a : ℤ) + (j.val : ℤ) + 1) =
    x.val (i + 1 - (a : ℤ) + (j.val : ℤ))
  apply congrArg x.val
  omega

instance wordTopology [TopologicalSpace E] (n : ℕ) : TopologicalSpace (LegalWord G n) :=
  TopologicalSpace.induced LegalWord.edge inferInstance

instance wordDiscrete [TopologicalSpace E] [DiscreteTopology E] (n : ℕ) :
    DiscreteTopology (LegalWord G n) :=
  DiscreteTopology.of_continuous_injective continuous_induced_dom
    (fun _ _ h => legalWord_ext h)

theorem historyWindow_continuous [TopologicalSpace E] (i : ℤ) (n : ℕ) :
    Continuous (fun x : History G => historyWindow G x i n) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro j
  exact (continuous_apply (i + (j.val : ℤ))).comp continuous_subtype_val

theorem applyTable_continuous [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] {a b : ℕ} (f : LegalWord G (a + b + 1) → D)
    (hf : Seam G F f) : Continuous (applyTable G F f hf) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous f).comp
    (historyWindow_continuous G (i - (a : ℤ)) _)

variable {G F}

theorem mapBlock_window {p q r s : ℕ} (pair : TablePair G F p q r s)
    (hf : Seam G F pair.f) (x : History G) (i : ℤ) :
    mapBlock G F pair.f hf
      (historyWindow G x (i - ((p + r : ℕ) : ℤ)) (p + q + r + s + 1))
      (by omega) (by omega) =
    historyWindow F (applyTable G F pair.f hf x) (i - (r : ℤ)) (r + s + 1) := by
  apply legalWord_ext
  funext j
  change pair.f (sliceWord G
    (historyWindow G x (i - ((p + r : ℕ) : ℤ)) _) j.val _ _) =
    pair.f (historyWindow G x (i - (r : ℤ) + (j.val : ℤ) - (p : ℤ)) _)
  rw [slice_historyWindow]
  congr 1
  apply legalWord_ext
  funext k
  change x.val (i - ((p + r : ℕ) : ℤ) + (j.val : ℤ) + (k.val : ℤ)) =
    x.val (i - (r : ℤ) + (j.val : ℤ) - (p : ℤ) + (k.val : ℤ))
  apply congrArg x.val
  omega

theorem inverse_of_local {p q r s : ℕ} (pair : TablePair G F p q r s)
    (h : LocalCriterion pair) :
    (∀ x, applyTable F G pair.g h.seamF (applyTable G F pair.f h.seamG x) = x) ∧
    (∀ y, applyTable G F pair.f h.seamG (applyTable F G pair.g h.seamF y) = y) := by
  constructor
  · intro x
    apply Subtype.ext
    funext i
    have ht := h.roundtripG
      (historyWindow G x (i - ((p + r : ℕ) : ℤ)) (p + q + r + s + 1))
    rw [mapBlock_window pair h.seamG] at ht
    simpa [applyTable, historyWindow] using ht
  · intro y
    apply Subtype.ext
    funext i
    have ht := h.roundtripF
      (historyWindow F y (i - ((p + r : ℕ) : ℤ)) (p + q + r + s + 1))
    have heq : mapBlock F G pair.g h.seamF
        (historyWindow F y (i - ((p + r : ℕ) : ℤ)) (p + q + r + s + 1))
        (by omega) (by omega) =
        historyWindow G (applyTable F G pair.g h.seamF y) (i - (p : ℤ)) (p + q + 1) := by
      apply legalWord_ext
      funext j
      change pair.g (sliceWord F
        (historyWindow F y (i - ((p + r : ℕ) : ℤ)) _) j.val _ _) =
        pair.g (historyWindow F y (i - (p : ℤ) + (j.val : ℤ) - (r : ℤ)) _)
      rw [slice_historyWindow]
      congr 1
      apply legalWord_ext
      funext k
      change y.val (i - ((p + r : ℕ) : ℤ) + (j.val : ℤ) + (k.val : ℤ)) =
        y.val (i - (p : ℤ) + (j.val : ℤ) - (r : ℤ) + (k.val : ℤ))
      apply congrArg y.val
      omega
    rw [heq] at ht
    simpa [applyTable, historyWindow] using ht

structure SameTableConjugacy [TopologicalSpace E] [TopologicalSpace D]
    {p q r s : ℕ} (pair : TablePair G F p q r s) where
  forward : History G → History F
  backward : History F → History G
  forward_table : ∀ x i, (forward x).val i =
    pair.f (historyWindow G x (i - (p : ℤ)) (p + q + 1))
  backward_table : ∀ y i, (backward y).val i =
    pair.g (historyWindow F y (i - (r : ℤ)) (r + s + 1))
  left_inverse : ∀ x, backward (forward x) = x
  right_inverse : ∀ y, forward (backward y) = y
  continuous_forward : Continuous forward
  continuous_backward : Continuous backward
  shift_forward : ∀ x, forward (shift G x) = shift F (forward x)
  shift_backward : ∀ y, backward (shift F y) = shift G (backward y)

variable [Fintype V] [Fintype E] [DecidableEq V]
variable [Fintype W] [Fintype D] [DecidableEq W]

theorem seam_of_map {a b : ℕ} (hG : Essential G)
    (f : LegalWord G (a + b + 1) → D) (phi : History G → History F)
    (hphi : ∀ x i, (phi x).val i = f (historyWindow G x (i - (a : ℤ)) _)) :
    Seam G F f := by
  intro w
  obtain ⟨x, hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
  have hs := (phi x).property (a : ℤ)
  rw [hphi, hphi] at hs
  have h0 := window_of_contains G w x hx 0 (a + b + 1) (by omega)
  have h1 := window_of_contains G w x hx 1 (a + b + 1) (by omega)
  simp only [sub_self, add_sub_cancel_left] at hs
  simp only [Int.natCast_zero] at h0
  simp only [Int.natCast_one] at h1
  rw [h0, h1] at hs
  exact hs

theorem local_of_conjugacy [TopologicalSpace E] [TopologicalSpace D]
    {p q r s : ℕ} (hG : Essential G) (hF : Essential F)
    (pair : TablePair G F p q r s) (c : SameTableConjugacy pair) : LocalCriterion pair := by
  have hf := seam_of_map hG pair.f c.forward c.forward_table
  have hg := seam_of_map hF pair.g c.backward c.backward_table
  have hp : ∀ x, c.forward x = applyTable G F pair.f hf x := by
    intro x
    apply Subtype.ext
    funext i
    exact c.forward_table x i
  have hq : ∀ y, c.backward y = applyTable F G pair.g hg y := by
    intro y
    apply Subtype.ext
    funext i
    exact c.backward_table y i
  refine ⟨hf, hg, ?_, ?_⟩
  · intro w
    obtain ⟨x, hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
    have hw : historyWindow G x 0 (p + q + r + s + 1) = w := by
      apply legalWord_ext
      funext j
      simpa [historyWindow] using hx j
    have hi := congrArg (fun t : History G => t.val ((p + r : ℕ) : ℤ)) (c.left_inverse x)
    rw [hq, hp] at hi
    have hb := mapBlock_window pair hf x ((p + r : ℕ) : ℤ)
    simp only [sub_self, hw] at hb
    change pair.g (historyWindow F (applyTable G F pair.f hf x)
      (((p + r : ℕ) : ℤ) - (r : ℤ)) (r + s + 1)) = _ at hi
    rw [← hb] at hi
    exact hi.trans (hx ⟨p + r, by omega⟩)
  · intro w
    obtain ⟨y, hy⟩ := every_prescribed_word_has_actual_history F hF w (by omega)
    have hw : historyWindow F y 0 (p + q + r + s + 1) = w := by
      apply legalWord_ext
      funext j
      simpa [historyWindow] using hy j
    have hi := congrArg (fun t : History F => t.val ((p + r : ℕ) : ℤ)) (c.right_inverse y)
    rw [hp, hq] at hi
    change pair.f (historyWindow G (applyTable F G pair.g hg y)
      (((p + r : ℕ) : ℤ) - (p : ℤ)) (p + q + 1)) = _ at hi
    -- The outer forward window begins at r, while inner g uses left radius r.
    have hb' : mapBlock F G pair.g hg w (by omega) (by omega) =
        historyWindow G (applyTable F G pair.g hg y) (r : ℤ) (p + q + 1) := by
      apply legalWord_ext
      funext j
      change pair.g (sliceWord F w j.val _ _) = pair.g (historyWindow F y _ _)
      congr 1
      have hj : (r : ℤ) + (j.val : ℤ) - (r : ℤ) = (j.val : ℤ) := by omega
      rw [hj]
      exact (window_of_contains F w y hy j.val (r + s + 1) (by omega)).symm
    have hc : ((p + r : ℕ) : ℤ) - (p : ℤ) = (r : ℤ) := by omega
    rw [hc, ← hb'] at hi
    exact hi.trans (hy ⟨p + r, by omega⟩)

theorem original23_1 [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D]
    [Nonempty V] [Nonempty W] {p q r s : ℕ}
    (hG : Essential G) (hF : Essential F) (pair : TablePair G F p q r s) :
    LocalCriterion pair ↔ Nonempty (SameTableConjugacy pair) := by
  constructor
  · intro h
    have hi := inverse_of_local pair h
    exact ⟨{
      forward := applyTable G F pair.f h.seamG
      backward := applyTable F G pair.g h.seamF
      forward_table := fun _ _ => rfl
      backward_table := fun _ _ => rfl
      left_inverse := hi.1
      right_inverse := hi.2
      continuous_forward := applyTable_continuous G F pair.f h.seamG
      continuous_backward := applyTable_continuous F G pair.g h.seamF
      shift_forward := applyTable_shift G F pair.f h.seamG
      shift_backward := applyTable_shift F G pair.g h.seamF }⟩
  · rintro ⟨c⟩
    exact local_of_conjugacy hG hF pair c


section GroupAction

variable {Γ : Type*} [Group Γ]
variable [MulAction Γ V] [MulAction Γ E] [MulAction Γ W] [MulAction Γ D]

structure GraphAction (G : DirectedMultigraph V E) : Prop where
  source_smul : ∀ a : Γ, ∀ e, G.source (a • e) = a • G.source e
  target_smul : ∀ a : Γ, ∀ e, G.target (a • e) = a • G.target e

variable (AG : GraphAction (Γ := Γ) G) (AF : GraphAction (Γ := Γ) F)

def actWord (a : Γ) {n : ℕ} (w : LegalWord G n) : LegalWord G n where
  edge j := a • w.edge j
  legal j hj := by rw [AG.target_smul, AG.source_smul, w.legal j hj]

def actHistory (a : Γ) (x : History G) : History G :=
  ⟨fun i => a • x.val i, fun i => by
    rw [AG.target_smul, AG.source_smul, x.property i]⟩

def LocalEquivariant {M : ℕ} (f : LegalWord G M → D) : Prop :=
  ∀ a : Γ, ∀ w, f (actWord AG a w) = a • f w

def GlobalEquivariant (phi : History G → History F) : Prop :=
  ∀ a : Γ, ∀ x, phi (actHistory AG a x) = actHistory AF a (phi x)

theorem table_equivariance_iff {left right : ℕ} (hG : Essential G)
    (f : LegalWord G (left + right + 1) → D) (hf : Seam G F f) :
    LocalEquivariant AG f ↔ GlobalEquivariant AG AF (applyTable G F f hf) := by
  constructor
  · intro he a x
    apply Subtype.ext
    funext i
    change f (historyWindow G (actHistory AG a x) (i - (left : ℤ)) _) =
      a • f (historyWindow G x (i - (left : ℤ)) _)
    have hw : historyWindow G (actHistory AG a x) (i - (left : ℤ)) (left + right + 1) =
        actWord AG a (historyWindow G x (i - (left : ℤ)) (left + right + 1)) := rfl
    rw [hw]
    exact he a _
  · intro he a w
    obtain ⟨x, hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
    have hw : historyWindow G x 0 (left + right + 1) = w := by
      apply legalWord_ext
      funext j
      simpa [historyWindow] using hx j
    have ha : historyWindow G (actHistory AG a x) 0 (left + right + 1) = actWord AG a w := by
      apply legalWord_ext
      funext j
      simpa [historyWindow, actHistory, actWord] using congrArg (fun e : E => a • e) (hx j)
    have hi := congrArg (fun y : History F => y.val (left : ℤ)) (he a x)
    change f (historyWindow G (actHistory AG a x)
      ((left : ℤ) - (left : ℤ)) (left + right + 1)) =
      a • f (historyWindow G x ((left : ℤ) - (left : ℤ)) (left + right + 1)) at hi
    simp only [sub_self] at hi
    rw [ha, hw] at hi
    exact hi


theorem sameTable_equivariance_iff [TopologicalSpace E] [TopologicalSpace D]
    {p q r s : ℕ} (hG : Essential G) (hF : Essential F)
    (pair : TablePair G F p q r s) (c : SameTableConjugacy pair) :
    (LocalEquivariant AG pair.f ∧ LocalEquivariant AF pair.g) ↔
    (GlobalEquivariant AG AF c.forward ∧ GlobalEquivariant AF AG c.backward) := by
  have hf := seam_of_map hG pair.f c.forward c.forward_table
  have hg := seam_of_map hF pair.g c.backward c.backward_table
  have hp : c.forward = applyTable G F pair.f hf := by
    funext x
    apply Subtype.ext
    funext i
    exact c.forward_table x i
  have hq : c.backward = applyTable F G pair.g hg := by
    funext x
    apply Subtype.ext
    funext i
    exact c.backward_table x i
  rw [hp, hq]
  exact and_congr (table_equivariance_iff AG AF hG pair.f hf)
    (table_equivariance_iff AF AG hF pair.g hg)

theorem original23_1_equivariant [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D] [Nonempty V] [Nonempty W]
    {p q r s : ℕ} (hG : Essential G) (hF : Essential F)
    (pair : TablePair G F p q r s) :
    (LocalCriterion pair ∧ LocalEquivariant AG pair.f ∧ LocalEquivariant AF pair.g) ↔
    ∃ c : SameTableConjugacy pair,
      GlobalEquivariant AG AF c.forward ∧ GlobalEquivariant AF AG c.backward := by
  constructor
  · rintro ⟨h, he⟩
    obtain ⟨c⟩ := (original23_1 hG hF pair).mp h
    exact ⟨c, (sameTable_equivariance_iff AG AF hG hF pair c).mp he⟩
  · rintro ⟨c, he⟩
    exact ⟨local_of_conjugacy hG hF pair c,
      (sameTable_equivariance_iff AG AF hG hF pair c).mpr he⟩

end GroupAction

section FiniteAlgorithm

variable [DecidableEq E] [DecidableEq D]

instance seamDecidable {M : ℕ} (f : LegalWord G M → D) : Decidable (Seam G F f) := by
  unfold Seam
  infer_instance

instance localCriterionDecidable {p q r s : ℕ} (pair : TablePair G F p q r s) :
    Decidable (LocalCriterion pair) :=
  if hf : Seam G F pair.f then
    if hg : Seam F G pair.g then
      if hrG : ∀ w : LegalWord G (p + q + r + s + 1),
          pair.g (mapBlock G F pair.f hf w (by omega) (by omega)) =
            w.edge ⟨p + r, by omega⟩ then
        if hrF : ∀ w : LegalWord F (p + q + r + s + 1),
            pair.f (mapBlock F G pair.g hg w (by omega) (by omega)) =
              w.edge ⟨p + r, by omega⟩ then
          isTrue ⟨hf, hg, hrG, hrF⟩
        else isFalse (fun h => hrF h.roundtripF)
      else isFalse (fun h => hrG h.roundtripG)
    else isFalse (fun h => hg h.seamF)
  else isFalse (fun h => hf h.seamG)

def tableEquiv (p q r s : ℕ) : TablePair G F p q r s ≃
    ((LegalWord G (p + q + 1) → D) × (LegalWord F (r + s + 1) → E)) where
  toFun t := (t.f, t.g)
  invFun t := ⟨t.1, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance tablePairFintype (p q r s : ℕ) : Fintype (TablePair G F p q r s) :=
  Fintype.ofEquiv _ (tableEquiv p q r s).symm

def finiteTableExists (p q r s : ℕ) : Bool :=
  decide (∃ pair : TablePair G F p q r s, LocalCriterion pair)

-- Explicit lists are used for witness extraction; no arbitrary classical decider is used.
def tupleWords (edges : List E) : (n : ℕ) → List (Fin n → E)
  | 0 => [Fin.elim0]
  | n + 1 => edges.flatMap fun e => (tupleWords edges n).map (Fin.cases e)

theorem tupleWords_complete (edges : List E) (he : ∀ e, e ∈ edges)
    (n : ℕ) (f : Fin n → E) : f ∈ tupleWords edges n := by
  induction n with
  | zero =>
    have hf : f = Fin.elim0 := by funext j; exact Fin.elim0 j
    simp [tupleWords, hf]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, he _, List.mem_map.mpr ?_⟩
    refine ⟨fun j => f j.succ, ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

def enumerateWords (G : DirectedMultigraph V E) (edges : List E) (n : ℕ) :
    List (LegalWord G n) :=
  (tupleWords edges n).filterMap fun e =>
    if h : ∀ j : Fin n, ∀ hj : j.val + 1 < n,
        G.target (e j) = G.source (e ⟨j.val + 1, hj⟩) then some ⟨e, h⟩ else none

theorem enumerateWords_complete (edges : List E) (he : ∀ e, e ∈ edges)
    (n : ℕ) (w : LegalWord G n) : w ∈ enumerateWords G edges n := by
  apply List.mem_filterMap.mpr
  refine ⟨w.edge, tupleWords_complete edges he n w.edge, ?_⟩
  rw [dif_pos w.legal]

inductive FailureWitness {p q r s : ℕ} (pair : TablePair G F p q r s) where
  | seamG (w : LegalWord G (p + q + 1 + 1))
      (failed : F.target (pair.f (sliceWord G w 0 _ (by omega))) ≠
        F.source (pair.f (sliceWord G w 1 _ (by omega))))
  | seamF (w : LegalWord F (r + s + 1 + 1))
      (failed : G.target (pair.g (sliceWord F w 0 _ (by omega))) ≠
        G.source (pair.g (sliceWord F w 1 _ (by omega))))
  | roundtripG (hf : Seam G F pair.f) (hg : Seam F G pair.g)
      (w : LegalWord G (p + q + r + s + 1))
      (failed : pair.g (mapBlock G F pair.f hf w (by omega) (by omega)) ≠
        w.edge ⟨p + r, by omega⟩)
  | roundtripF (hf : Seam G F pair.f) (hg : Seam F G pair.g)
      (w : LegalWord F (p + q + r + s + 1))
      (failed : pair.f (mapBlock F G pair.g hg w (by omega) (by omega)) ≠
        w.edge ⟨p + r, by omega⟩)

def listCounterexample {α : Type*} (xs : List α) (hx : ∀ x, x ∈ xs)
    (P : α → Prop) [DecidablePred P] (h : ¬ ∀ x, P x) : {x // ¬ P x} :=
  let hb : ∃ x, x ∈ xs ∧ ¬ P x := by
    classical
    obtain ⟨x, hx'⟩ := not_forall.mp h
    exact ⟨x, hx x, hx'⟩
  ⟨List.choose (fun x => ¬ P x) xs hb, List.choose_property _ _ hb⟩

def inspectPair {p q r s : ℕ} (pair : TablePair G F p q r s)
    (edgesG : List E) (edgesF : List D)
    (hG : ∀ e, e ∈ edgesG) (hF : ∀ e, e ∈ edgesF) :
    Sum (PLift (LocalCriterion pair)) (FailureWitness pair) :=
  if hf : Seam G F pair.f then
    if hg : Seam F G pair.g then
      if hrG : ∀ w : LegalWord G (p + q + r + s + 1),
          pair.g (mapBlock G F pair.f hf w (by omega) (by omega)) =
            w.edge ⟨p + r, by omega⟩ then
        if hrF : ∀ w : LegalWord F (p + q + r + s + 1),
            pair.f (mapBlock F G pair.g hg w (by omega) (by omega)) =
              w.edge ⟨p + r, by omega⟩ then
          Sum.inl ⟨⟨hf, hg, hrG, hrF⟩⟩
        else
          let w := listCounterexample (enumerateWords F edgesF _)
            (enumerateWords_complete edgesF hF _) _ hrF
          Sum.inr (.roundtripF hf hg w.val w.property)
      else
        let w := listCounterexample (enumerateWords G edgesG _)
          (enumerateWords_complete edgesG hG _) _ hrG
        Sum.inr (.roundtripG hf hg w.val w.property)
    else
      let w := listCounterexample (enumerateWords F edgesF _)
        (enumerateWords_complete edgesF hF _) _ hg
      Sum.inr (.seamF w.val w.property)
  else
    let w := listCounterexample (enumerateWords G edgesG _)
      (enumerateWords_complete edgesG hG _) _ hf
    Sum.inr (.seamG w.val w.property)

theorem failure_refutes {p q r s : ℕ} {pair : TablePair G F p q r s}
    (bad : FailureWitness pair) : ¬ LocalCriterion pair := by
  intro h
  cases bad with
  | seamG w hf => exact hf (h.seamG w)
  | seamF w hf => exact hf (h.seamF w)
  | roundtripG hf hg w hb => exact hb (h.roundtripG w)
  | roundtripF hf hg w hb => exact hb (h.roundtripF w)


def FailureExposure {p q r s : ℕ} {pair : TablePair G F p q r s}
    (bad : FailureWitness pair) : Prop :=
  match bad with
  | .seamG w _ => ∃ x : History G,
      (∀ j : Fin (p + q + 1 + 1), x.val (j.val : ℤ) = w.edge j) ∧
      F.target (pair.f (historyWindow G x 0 (p + q + 1))) ≠
        F.source (pair.f (historyWindow G x 1 (p + q + 1)))
  | .seamF w _ => ∃ y : History F,
      (∀ j : Fin (r + s + 1 + 1), y.val (j.val : ℤ) = w.edge j) ∧
      G.target (pair.g (historyWindow F y 0 (r + s + 1))) ≠
        G.source (pair.g (historyWindow F y 1 (r + s + 1)))
  | .roundtripG hf hg w _ => ∃ x : History G,
      (∀ j : Fin (p + q + r + s + 1), x.val (j.val : ℤ) = w.edge j) ∧
      (applyTable F G pair.g hg (applyTable G F pair.f hf x)).val ((p + r : ℕ) : ℤ) ≠
        x.val ((p + r : ℕ) : ℤ)
  | .roundtripF hf hg w _ => ∃ y : History F,
      (∀ j : Fin (p + q + r + s + 1), y.val (j.val : ℤ) = w.edge j) ∧
      (applyTable G F pair.f hf (applyTable F G pair.g hg y)).val ((p + r : ℕ) : ℤ) ≠
        y.val ((p + r : ℕ) : ℤ)

theorem failure_exposes_history {p q r s : ℕ} {pair : TablePair G F p q r s}
    (hG : Essential G) (hF : Essential F) (bad : FailureWitness pair) :
    FailureExposure bad := by
  cases bad with
  | seamG w hb =>
    obtain ⟨x, hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
    refine ⟨x, hx, ?_⟩
    have h0 := window_of_contains G w x hx 0 (p + q + 1) (by omega)
    have h1 := window_of_contains G w x hx 1 (p + q + 1) (by omega)
    simp only [Int.natCast_zero] at h0
    simp only [Int.natCast_one] at h1
    simpa only [h0, h1] using hb
  | seamF w hb =>
    obtain ⟨y, hy⟩ := every_prescribed_word_has_actual_history F hF w (by omega)
    refine ⟨y, hy, ?_⟩
    have h0 := window_of_contains F w y hy 0 (r + s + 1) (by omega)
    have h1 := window_of_contains F w y hy 1 (r + s + 1) (by omega)
    simp only [Int.natCast_zero] at h0
    simp only [Int.natCast_one] at h1
    simpa only [h0, h1] using hb
  | roundtripG hf hg w hb =>
    obtain ⟨x, hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
    refine ⟨x, hx, ?_⟩
    have hw : historyWindow G x 0 (p + q + r + s + 1) = w := by
      apply legalWord_ext
      funext j
      simpa [historyWindow] using hx j
    have hi := mapBlock_window pair hf x ((p + r : ℕ) : ℤ)
    simp only [sub_self, hw] at hi
    change pair.g (historyWindow F (applyTable G F pair.f hf x)
      (((p + r : ℕ) : ℤ) - (r : ℤ)) _) ≠ _
    rw [← hi, hx ⟨p + r, by omega⟩]
    exact hb
  | roundtripF hf hg w hb =>
    obtain ⟨y, hy⟩ := every_prescribed_word_has_actual_history F hF w (by omega)
    refine ⟨y, hy, ?_⟩
    have hi : mapBlock F G pair.g hg w (by omega) (by omega) =
        historyWindow G (applyTable F G pair.g hg y) (r : ℤ) (p + q + 1) := by
      apply legalWord_ext
      funext j
      change pair.g (sliceWord F w j.val _ _) = pair.g (historyWindow F y _ _)
      congr 1
      have hj : (r : ℤ) + (j.val : ℤ) - (r : ℤ) = (j.val : ℤ) := by omega
      rw [hj]
      exact (window_of_contains F w y hy j.val (r + s + 1) (by omega)).symm
    change pair.f (historyWindow G (applyTable F G pair.g hg y)
      (((p + r : ℕ) : ℤ) - (p : ℤ)) _) ≠ _
    have hc : ((p + r : ℕ) : ℤ) - (p : ℤ) = (r : ℤ) := by omega
    rw [hc, ← hi, hy ⟨p + r, by omega⟩]
    exact hb

theorem finiteTableExists_correct [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D] [Nonempty V] [Nonempty W]
    (hG : Essential G) (hF : Essential F) (p q r s : ℕ) :
    finiteTableExists (G := G) (F := F) p q r s = true ↔
      ∃ pair : TablePair G F p q r s, Nonempty (SameTableConjugacy pair) := by
  simp only [finiteTableExists, decide_eq_true_eq]
  exact exists_congr (fun pair => original23_1 hG hF pair)



theorem rejected_candidate_has_finite_witness {p q r s : ℕ}
    (pair : TablePair G F p q r s) (edgesG : List E) (edgesF : List D)
    (hG : ∀ e, e ∈ edgesG) (hF : ∀ e, e ∈ edgesF)
    (essentialG : Essential G) (essentialF : Essential F) :
    (¬ LocalCriterion pair) ↔ ∃ bad : FailureWitness pair, FailureExposure bad := by
  constructor
  · intro h
    cases inspectPair pair edgesG edgesF hG hF with
    | inl good => exact False.elim (h good.down)
    | inr bad => exact ⟨bad, failure_exposes_history essentialG essentialF bad⟩
  · rintro ⟨bad, _⟩
    exact failure_refutes bad


def originalExistenceDecidable [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D] [Nonempty V] [Nonempty W]
    (hG : Essential G) (hF : Essential F) (p q r s : ℕ) :
    Decidable (∃ pair : TablePair G F p q r s, Nonempty (SameTableConjugacy pair)) :=
  decidable_of_iff (finiteTableExists (G := G) (F := F) p q r s = true)
    (finiteTableExists_correct hG hF p q r s)

section EquivariantAlgorithm

variable {Γ : Type*} [Group Γ] [Fintype Γ]
variable [MulAction Γ V] [MulAction Γ E] [MulAction Γ W] [MulAction Γ D]
variable (AG : GraphAction (Γ := Γ) G) (AF : GraphAction (Γ := Γ) F)

instance localEquivariantDecidable {M : ℕ} (f : LegalWord G M → D) :
    Decidable (LocalEquivariant AG f) := by
  unfold LocalEquivariant
  infer_instance

def finiteEquivariantTableExists (p q r s : ℕ) : Bool :=
  decide (∃ pair : TablePair G F p q r s,
    LocalCriterion pair ∧ LocalEquivariant AG pair.f ∧ LocalEquivariant AF pair.g)

inductive EquivariantFailure {p q r s : ℕ} (pair : TablePair G F p q r s) where
  | wordFailure (bad : FailureWitness pair)
  | equivG (a : Γ) (w : LegalWord G (p + q + 1))
      (failed : pair.f (actWord AG a w) ≠ a • pair.f w)
  | equivF (a : Γ) (w : LegalWord F (r + s + 1))
      (failed : pair.g (actWord AF a w) ≠ a • pair.g w)

def inspectEquivariantPair {p q r s : ℕ} (pair : TablePair G F p q r s)
    (edgesG : List E) (edgesF : List D) (groups : List Γ)
    (hG : ∀ e, e ∈ edgesG) (hF : ∀ e, e ∈ edgesF) (hΓ : ∀ a, a ∈ groups) :
    Sum (PLift (LocalCriterion pair ∧ LocalEquivariant AG pair.f ∧ LocalEquivariant AF pair.g))
      (EquivariantFailure AG AF pair) :=
  match inspectPair pair edgesG edgesF hG hF with
  | .inr bad => .inr (.wordFailure bad)
  | .inl h =>
    if hf : LocalEquivariant AG pair.f then
      if hg : LocalEquivariant AF pair.g then .inl ⟨h.down, hf, hg⟩
      else
        let a := listCounterexample groups hΓ _ hg
        let w := listCounterexample (enumerateWords F edgesF _)
          (enumerateWords_complete edgesF hF _) _ a.property
        .inr (.equivF a.val w.val w.property)
    else
      let a := listCounterexample groups hΓ _ hf
      let w := listCounterexample (enumerateWords G edgesG _)
        (enumerateWords_complete edgesG hG _) _ a.property
      .inr (.equivG a.val w.val w.property)

theorem equivariantFailure_refutes {p q r s : ℕ} {pair : TablePair G F p q r s}
    (bad : EquivariantFailure AG AF pair) :
    ¬ (LocalCriterion pair ∧ LocalEquivariant AG pair.f ∧ LocalEquivariant AF pair.g) := by
  rintro ⟨h, hf, hg⟩
  cases bad with
  | wordFailure hb => exact failure_refutes hb h
  | equivG a w hb => exact hb (hf a w)
  | equivF a w hb => exact hb (hg a w)

theorem equivariance_failure_exposed {left right : ℕ} (hG : Essential G)
    (f : LegalWord G (left + right + 1) → D) (a : Γ)
    (w : LegalWord G (left + right + 1)) (hb : f (actWord AG a w) ≠ a • f w) :
    ∃ x : History G,
      (∀ j, x.val (j.val : ℤ) = w.edge j) ∧
      f (historyWindow G (actHistory AG a x) 0 (left + right + 1)) ≠
        a • f (historyWindow G x 0 (left + right + 1)) := by
  obtain ⟨x, hx⟩ := every_prescribed_word_has_actual_history G hG w (by omega)
  refine ⟨x, hx, ?_⟩
  have hw : historyWindow G x 0 (left + right + 1) = w := by
    apply legalWord_ext
    funext j
    simpa [historyWindow] using hx j
  have ha : historyWindow G (actHistory AG a x) 0 (left + right + 1) = actWord AG a w := by
    apply legalWord_ext
    funext j
    simpa [historyWindow, actHistory, actWord] using congrArg (fun e : E => a • e) (hx j)
  rw [hw, ha]
  exact hb

theorem finiteEquivariantTableExists_correct [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D] [Nonempty V] [Nonempty W]
    (hG : Essential G) (hF : Essential F) (p q r s : ℕ) :
    finiteEquivariantTableExists AG AF p q r s = true ↔
      ∃ pair : TablePair G F p q r s, ∃ c : SameTableConjugacy pair,
        GlobalEquivariant AG AF c.forward ∧ GlobalEquivariant AF AG c.backward := by
  simp only [finiteEquivariantTableExists, decide_eq_true_eq]
  exact exists_congr (fun pair => original23_1_equivariant AG AF hG hF pair)


def EquivariantFailureExposure {p q r s : ℕ} {pair : TablePair G F p q r s}
    (bad : EquivariantFailure AG AF pair) : Prop :=
  match bad with
  | .wordFailure hb => FailureExposure hb
  | .equivG a w _ => ∃ x : History G,
      (∀ j, x.val (j.val : ℤ) = w.edge j) ∧
      pair.f (historyWindow G (actHistory AG a x) 0 (p + q + 1)) ≠
        a • pair.f (historyWindow G x 0 (p + q + 1))
  | .equivF a w _ => ∃ y : History F,
      (∀ j, y.val (j.val : ℤ) = w.edge j) ∧
      pair.g (historyWindow F (actHistory AF a y) 0 (r + s + 1)) ≠
        a • pair.g (historyWindow F y 0 (r + s + 1))

theorem equivariantFailure_exposes_history {p q r s : ℕ}
    {pair : TablePair G F p q r s} (hG : Essential G) (hF : Essential F)
    (bad : EquivariantFailure AG AF pair) : EquivariantFailureExposure AG AF bad := by
  cases bad with
  | wordFailure hb => exact failure_exposes_history hG hF hb
  | equivG a w hb => exact equivariance_failure_exposed AG hG pair.f a w hb
  | equivF a w hb => exact equivariance_failure_exposed AF hF pair.g a w hb

theorem rejected_equivariant_candidate_has_finite_witness {p q r s : ℕ}
    (pair : TablePair G F p q r s) (edgesG : List E) (edgesF : List D) (groups : List Γ)
    (hG : ∀ e, e ∈ edgesG) (hF : ∀ e, e ∈ edgesF) (hΓ : ∀ a, a ∈ groups)
    (essentialG : Essential G) (essentialF : Essential F) :
    (¬ (LocalCriterion pair ∧ LocalEquivariant AG pair.f ∧ LocalEquivariant AF pair.g)) ↔
    ∃ bad : EquivariantFailure AG AF pair, EquivariantFailureExposure AG AF bad := by
  constructor
  · intro h
    cases inspectEquivariantPair AG AF pair edgesG edgesF groups hG hF hΓ with
    | inl good => exact False.elim (h good.down)
    | inr bad => exact ⟨bad, equivariantFailure_exposes_history AG AF essentialG essentialF bad⟩
  · rintro ⟨bad, _⟩
    exact equivariantFailure_refutes AG AF bad


def originalEquivariantExistenceDecidable [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D] [Nonempty V] [Nonempty W]
    (hG : Essential G) (hF : Essential F) (p q r s : ℕ) :
    Decidable (∃ pair : TablePair G F p q r s, ∃ c : SameTableConjugacy pair,
      GlobalEquivariant AG AF c.forward ∧ GlobalEquivariant AF AG c.backward) :=
  decidable_of_iff (finiteEquivariantTableExists AG AF p q r s = true)
    (finiteEquivariantTableExists_correct AG AF hG hF p q r s)

end EquivariantAlgorithm

end FiniteAlgorithm

section OrderedInput
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
variable {H : Type*} [Group H] [Fintype H] [LinearOrder H] {n m : ℕ}

/-- Actual free expansion; definitionally the existing expandedGraph. -/
def countedExpansion (A : GroupMat H n n) :
    DirectedMultigraph (Fin n × H) (Edge A × H) :=
  ⟨fun e => (e.1.source,e.2),fun e => (e.1.target,e.2*e.1.label)⟩

/-- The forward boundary crosses the actual first U half-edge. -/
noncomputable def orderedForward (U : GroupMat H n m) (V : GroupMat H m n)
    (w : LegalWord (countedExpansion (U*V)) 2) : Edge (V*U) × H :=
  let a := orderedSplit U V (w.edge 0).1
  let b := orderedSplit U V (w.edge 1).1
  (orderedJoin V U a.2 b.1 (congrArg Prod.fst (w.legal 0 (by decide))),
    (w.edge 0).2*a.1.label)

/-- Preceding and central output share U; the coordinate is the central one. -/
noncomputable def orderedBackward (U : GroupMat H n m) (V : GroupMat H m n)
    (w : LegalWord (countedExpansion (V*U)) 2) : Edge (U*V) × H :=
  let a := orderedSplit V U (w.edge 0).1
  let b := orderedSplit V U (w.edge 1).1
  (orderedJoin U V a.2 b.1 (congrArg Prod.fst (w.legal 0 (by decide))),
    (w.edge 1).2*a.2.label⁻¹)

/-- Raw ordered UV/VU tables at the original asymmetric radii. -/
noncomputable def orderedOverlapInput (U : GroupMat H n m) (V : GroupMat H m n) :
    TablePair (countedExpansion (U*V)) (countedExpansion (V*U)) 0 1 1 0 :=
  ⟨orderedForward U V,orderedBackward U V⟩
end OrderedInput

open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap

/-- The source order e,r,r²,r³,s,rs,r²s,r³s, using sr j = s*r^j. -/
def d8Rank : DihedralGroup 4 → ℕ
  | .r i => i.val
  | .sr i => 4 + (-i).val

private theorem d8Rank_injective : Function.Injective d8Rank := by
  rintro (a | a) (b | b) h
  · exact congrArg DihedralGroup.r (ZMod.val_injective 4 h)
  · have ha := ZMod.val_lt a
    have hb := ZMod.val_lt (-b)
    simp only [d8Rank] at h
    omega
  · have ha := ZMod.val_lt (-a)
    have hb := ZMod.val_lt b
    simp only [d8Rank] at h
    omega
  · apply congrArg DihedralGroup.sr
    have hn := ZMod.val_injective 4 (by simpa [d8Rank] using h : (-a).val = (-b).val)
    exact neg_injective hn

instance d8Order : LinearOrder (DihedralGroup 4) := LinearOrder.lift' d8Rank d8Rank_injective

/-- The original two scalar natural group-ring factors. -/
noncomputable def d8P : GroupMat (DihedralGroup 4) 1 1 := fun _ _ =>
  MonoidAlgebra.single (DihedralGroup.r (n := 4) 0) 1 + MonoidAlgebra.single (DihedralGroup.r (n := 4) 1) 2 + MonoidAlgebra.single (DihedralGroup.r (n := 4) 2) 1 +
  MonoidAlgebra.single (DihedralGroup.r (n := 4) 3) 1 + MonoidAlgebra.single (DihedralGroup.sr (n := 4) 0) 1 + MonoidAlgebra.single (DihedralGroup.sr (n := 4) 3) 1 +
  MonoidAlgebra.single (DihedralGroup.sr (n := 4) 2) 1

noncomputable def d8Q : GroupMat (DihedralGroup 4) 1 1 := fun _ _ =>
  MonoidAlgebra.single (DihedralGroup.r (n := 4) 0) 1 + MonoidAlgebra.single (DihedralGroup.sr (n := 4) 0) 1

/-- Raw first input only: no assertion of checker acceptance is stored here. -/
noncomputable def orderedD8Input :
    TablePair (countedExpansion (d8P*d8Q)) (countedExpansion (d8Q*d8P)) 0 1 1 0 :=
  orderedOverlapInput d8P d8Q

/-- Complete group dictionary in the source order. -/
def d8Groups : List (DihedralGroup 4) :=
  [.r 0,.r 1,.r 2,.r 3,.sr 0,.sr 3,.sr 2,.sr 1]

/-- Complete edge dictionary in group-coordinate, label, then copy order. -/
noncomputable def orderedEdges {H : Type*} [Group H] [Fintype H] [LinearOrder H]
    {n : ℕ} (A : GroupMat H n n) : List (Edge A × H) :=
  (Finset.univ.sort (· ≤ ·) : List H).flatMap fun h =>
    (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
      (Finset.univ.sort (· ≤ ·) : List H).flatMap fun g =>
        (List.finRange ((A i j).coeff g)).map fun c => (⟨i,j,g,c⟩,h)

end D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
