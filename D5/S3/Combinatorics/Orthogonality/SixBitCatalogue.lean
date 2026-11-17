/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogue
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.chromatic_number_six; instance=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.catalogue_proper
   digest: Supplied exact six-bit orthogonality catalogue and complete proof transfer. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/- Binary vectors are the six low bits of an integer. Addition is XOR;
   zero-containing XOR-closed sets are exactly the subspaces over F_2. -/
namespace BinaryOrthogonality

abbrev Vector := Fin 64

def add (x y : Vector) : Vector := ⟨(x.val ^^^ y.val) % 64, Nat.mod_lt _ (by decide)⟩

def dot (x y : Vector) : Nat :=
  ((List.range 6).map (fun i => (x.val / 2^i % 2) * (y.val / 2^i % 2))).sum % 2

theorem add_cancel (x y : Vector) : add (add x y) y = x := by
  revert x y
  decide +kernel

theorem dot_symm (x y : Vector) : dot x y = dot y x := by
  simp only [dot, Nat.mul_comm]

def IsSpace (U : Finset Vector) : Prop :=
  0 ∈ U ∧ (∀ x ∈ U, ∀ y ∈ U, add x y ∈ U)

abbrev Vertex := {U : Finset Vector // IsSpace U ∧ U ≠ {0}}

def graph : SimpleGraph Vertex where
  Adj U W := U ≠ W ∧ ∀ u ∈ U.val, ∀ w ∈ W.val, dot u w = 0
  symm := ⟨by
    intro U W h
    exact ⟨h.1.symm, fun w hw u hu => (dot_symm w u).trans (h.2 u hu w hw)⟩⟩
  loopless := ⟨fun U h => h.1 rfl⟩

def carrier (mask : Nat) : Finset Vector := Finset.univ.filter fun x => mask.testBit x.val

@[simp] theorem mem_carrier (m : Nat) (v : Vector) :
    v ∈ carrier m ↔ m.testBit v.val = true := by simp [carrier]

theorem zero_carrier : carrier 1 = {0} := by decide +kernel

theorem mask_subset {a b : Nat} (ha : a < 2^64) (h : carrier a ⊆ carrier b) :
    a &&& b = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 64
  · have hh := h (x := (⟨i, hi⟩ : Vector))
    simp only [mem_carrier] at hh
    cases hai : a.testBit i <;> simp_all
  · have hz : a.testBit i = false := Nat.testBit_lt_two_pow (by
      exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hz]

structure Catalogue where
  count : Nat
  positive : 0 < count
  masks : Nat → Nat
  perps : Nat → Nat
  colors : Nat → Nat
  extensions : Nat → Nat

def Catalogue.mask (D : Catalogue) (i : Fin D.count) := D.masks i.val
def Catalogue.perp (D : Catalogue) (i : Fin D.count) := D.perps i.val
def Catalogue.color (D : Catalogue) (i : Fin D.count) := D.colors i.val
def Catalogue.space (D : Catalogue) (i : Fin D.count) := carrier (D.mask i)
def Catalogue.step (D : Catalogue) (i : Fin D.count) (v : Vector) : Fin D.count :=
  ⟨D.extensions (i.val * 64 + v.val) % D.count, Nat.mod_lt _ D.positive⟩
def Catalogue.zero (D : Catalogue) : Fin D.count := ⟨0, D.positive⟩

def Catalogue.Covers (D : Catalogue) : Prop :=
  D.space D.zero = {0} ∧
  ∀ (i : Fin D.count) (v : Vector),
    D.space i ⊆ D.space (D.step i v) ∧ v ∈ D.space (D.step i v) ∧
    ∀ x ∈ D.space (D.step i v), x ∈ D.space i ∨ add x v ∈ D.space i

instance (D : Catalogue) : Decidable D.Covers := inferInstanceAs (Decidable (_ ∧ _))

theorem Catalogue.complete (D : Catalogue) (hc : D.Covers)
    (U : Finset Vector) (hU : IsSpace U) : ∃ i, D.space i = U := by
  have cover (S : Finset Vector) (hs : S ⊆ U) : ∃ i, S ⊆ D.space i ∧ D.space i ⊆ U := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨D.zero, Finset.empty_subset _, ?_⟩
      rw [hc.1]
      exact Finset.singleton_subset_iff.mpr hU.1
    | @insert v S hv ih =>
      obtain ⟨i, hsi, hiu⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hs)
      refine ⟨D.step i v, Finset.insert_subset (hc.2 i v).2.1
        (hsi.trans (hc.2 i v).1), ?_⟩
      intro x hx
      rcases (hc.2 i v).2.2 x hx with h | h
      · exact hiu h
      · have hh := hU.2 (add x v) (hiu h) v (hs (Finset.mem_insert_self _ _))
        simpa only [add_cancel] using hh
  obtain ⟨i, h1, h2⟩ := cover U (Finset.Subset.refl U)
  exact ⟨i, Finset.Subset.antisymm h2 h1⟩

def Catalogue.Proper (D : Catalogue) : Prop :=
  (∀ i, D.mask i < 2^64 ∧ D.color i < 15) ∧
  (∀ (i : Fin D.count) (v : Vector),
    v ∈ carrier (D.perp i) ↔ ∀ u ∈ D.space i, dot u v = 0) ∧
  (∀ i j, i ≠ D.zero → j ≠ D.zero → D.mask i ≠ D.mask j →
    D.mask j &&& D.perp i = D.mask j → D.color i ≠ D.color j)

instance (D : Catalogue) : Decidable D.Proper := inferInstanceAs (Decidable (_ ∧ _))

noncomputable def Catalogue.index (D : Catalogue) (hc : D.Covers) (U : Vertex) : Fin D.count :=
  (D.complete hc U.val U.property.1).choose

theorem Catalogue.index_spec (D : Catalogue) (hc : D.Covers) (U : Vertex) :
    D.space (D.index hc U) = U.val := (D.complete hc U.val U.property.1).choose_spec

theorem Catalogue.colorable (D : Catalogue) (hc : D.Covers) (hp : D.Proper) :
    graph.Colorable 15 := by
  classical
  let idx := D.index hc
  refine ⟨{ toFun := fun U => ⟨D.color (idx U), (hp.1 _).2⟩, map_rel' := ?_ }⟩
  intro U W hUW
  change (⟨D.color (idx U), (hp.1 _).2⟩ : Fin 15) ≠ ⟨D.color (idx W), (hp.1 _).2⟩
  intro h
  have nezero (V : Vertex) : idx V ≠ D.zero := by
    intro h
    apply V.property.2
    rw [← D.index_spec hc V]
    change D.space (idx V) = {0}
    rw [h, hc.1]
  have distinct : D.mask (idx U) ≠ D.mask (idx W) := by
    intro heq
    apply hUW.1
    apply Subtype.ext
    rw [← D.index_spec hc U, ← D.index_spec hc W]
    exact congrArg carrier heq
  have sub : D.space (idx W) ⊆ carrier (D.perp (idx U)) := by
    intro w hw
    apply (hp.2.1 _ w).mpr
    intro u hu
    rw [D.index_spec hc W] at hw
    rw [D.index_spec hc U] at hu
    exact hUW.2 u hu w hw
  exact hp.2.2 _ _ (nezero U) (nezero W) distinct
    (mask_subset (hp.1 _).1 sub) (congrArg Fin.val h)

/-- The exact covering obligation as direct bit tests, before materializing finite sets. -/
def Catalogue.CoverBitRow (D : Catalogue) (i : Fin D.count) : Prop :=
  ∀ v : Vector,
    D.mask i &&& D.mask (D.step i v) = D.mask i ∧
    (D.mask (D.step i v)).testBit v.val = true ∧
    ∀ x : Vector, (D.mask (D.step i v)).testBit x.val = true →
      (D.mask i).testBit x.val = true ∨ (D.mask i).testBit (add x v).val = true

instance (D : Catalogue) (i : Fin D.count) : Decidable (D.CoverBitRow i) :=
  by unfold Catalogue.CoverBitRow; infer_instance

/-- Direct bit rows prove the unchanged full finite-set covering statement. -/
theorem Catalogue.covers_of_bit_rows (D : Catalogue)
    (hz : D.mask D.zero = 1) (h : ∀ i, D.CoverBitRow i) : D.Covers := by
  constructor
  · change carrier (D.mask D.zero) = {0}
    rw [hz, zero_carrier]
  · intro i v
    obtain ⟨hs, hv, hx⟩ := h i v
    refine ⟨?_, (mem_carrier _ _).mpr hv, ?_⟩
    · intro x hi
      have hix : (D.mask i).testBit x.val = true := (mem_carrier _ _).mp hi
      have he := congrArg (fun m => m.testBit x.val) hs
      rw [Nat.testBit_and, hix] at he
      exact (mem_carrier _ _).mpr (by simpa using he)
    · intro x hstep
      exact (hx x ((mem_carrier _ _).mp hstep)).imp
        ((mem_carrier _ _).mpr) ((mem_carrier _ _).mpr)

/-- Exact orthogonal-complement bits for one complete catalogue row. -/
def Catalogue.PerpBitRow (D : Catalogue) (i : Fin D.count) : Prop :=
  ∀ v : Vector, (D.perp i).testBit v.val = true ↔
    ∀ u : Vector, (D.mask i).testBit u.val = true → dot u v = 0

instance (D : Catalogue) (i : Fin D.count) : Decidable (D.PerpBitRow i) :=
  by unfold Catalogue.PerpBitRow; infer_instance

/-- Equivalent order of the full pair test: compare colors before evaluating orthogonality. -/
def Catalogue.ColorBitRow (D : Catalogue) (i : Fin D.count) : Prop :=
  ∀ j : Fin D.count, D.color i ≠ D.color j ∨ i = D.zero ∨ j = D.zero ∨
    D.mask i = D.mask j ∨ D.mask j &&& D.perp i ≠ D.mask j

instance (D : Catalogue) (i : Fin D.count) : Decidable (D.ColorBitRow i) :=
  by unfold Catalogue.ColorBitRow; infer_instance

/-- The bit verifier entails every original bound, perp and proper-coloring obligation. -/
theorem Catalogue.proper_of_bit_rows (D : Catalogue)
    (hb : ∀ i, D.mask i < 2^64 ∧ D.color i < 15)
    (hp : ∀ i, D.PerpBitRow i) (hc : ∀ i, D.ColorBitRow i) : D.Proper := by
  refine ⟨hb, ?_, ?_⟩
  · intro i v
    simpa only [Catalogue.space, mem_carrier] using hp i v
  · intro i j hi hj hm ho
    rcases hc i j with h | h | h | h | h
    · exact h
    · exact (hi h).elim
    · exact (hj h).elim
    · exact (hm h).elim
    · exact (h ho).elim

/-- A proof-free Boolean traversal; its specification retains every index. -/
def checkAll : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => checkAll n f && f n

theorem checkAll_spec (n : Nat) (f : Nat → Bool) :
    checkAll n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [checkAll]
  | succ n ih =>
    simp only [checkAll, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self _)⟩

def Catalogue.coverCheck (D : Catalogue) (i : Nat) : Bool :=
  checkAll 64 fun v =>
    let m := D.masks i
    let e := D.masks (D.extensions (i * 64 + v) % D.count)
    (m &&& e == m) && e.testBit v &&
      checkAll 64 (fun x => !e.testBit x || m.testBit x ||
        m.testBit ((x ^^^ v) % 64))

theorem Catalogue.coverCheck_sound (D : Catalogue) (i : Fin D.count)
    (h : D.coverCheck i.val = true) : D.CoverBitRow i := by
  intro v
  have hv := (checkAll_spec _ _).mp h v.val v.isLt
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  refine ⟨hv.1.1, hv.1.2, ?_⟩
  intro x hx
  have hh := (checkAll_spec _ _).mp hv.2 x.val x.isLt
  change (D.masks (D.extensions (i.val * 64 + v.val) % D.count)).testBit x.val = true at hx
  simpa [Catalogue.mask, Catalogue.step, add, hx] using hh

def Catalogue.perpCheck (D : Catalogue) (i : Nat) : Bool :=
  checkAll 64 fun v =>
    (D.perps i).testBit v ==
      checkAll 64 (fun u => !(D.masks i).testBit u ||
        (((List.range 6).map (fun k => (u / 2^k % 2) * (v / 2^k % 2))).sum % 2 == 0))

theorem Catalogue.perpCheck_sound (D : Catalogue) (i : Fin D.count)
    (h : D.perpCheck i.val = true) : D.PerpBitRow i := by
  intro v
  have hv := (checkAll_spec _ _).mp h v.val v.isLt
  simp only [beq_iff_eq] at hv
  change (D.perps i.val).testBit v.val = true ↔ _
  rw [hv, checkAll_spec]
  constructor
  · intro hh u hu
    have hx := hh u.val u.isLt
    change (D.masks i.val).testBit u.val = true at hu
    simpa [hu, dot, Catalogue.space, Catalogue.mask] using hx
  · intro hh u hu
    by_cases hm : (D.masks i.val).testBit u = true
    · have hx := hh (⟨u,hu⟩ : Vector) hm
      simpa [hm, dot] using hx
    · simp [hm]

def Catalogue.colorCheck (D : Catalogue) (i : Nat) : Bool :=
  checkAll D.count fun j =>
    (!(D.colors i == D.colors j)) || (i == 0) || (j == 0) ||
      (D.masks i == D.masks j) || (!(D.masks j &&& D.perps i == D.masks j))

theorem Catalogue.colorCheck_sound (D : Catalogue) (i : Fin D.count)
    (h : D.colorCheck i.val = true) : D.ColorBitRow i := by
  intro j
  have hh := (checkAll_spec _ _).mp h j.val j.isLt
  simpa [Catalogue.color, Catalogue.mask, Catalogue.perp, Catalogue.zero,
    Fin.ext_iff, or_assoc] using hh

/-- A row retains all covering, perp, pair-color and range obligations. -/
def Catalogue.rowCheck (D : Catalogue) (i : Nat) : Bool :=
  decide (D.masks i < 2^64) && decide (D.colors i < 15) &&
    D.coverCheck i && D.perpCheck i && D.colorCheck i

theorem Catalogue.rowCheck_sound (D : Catalogue) (i : Fin D.count)
    (h : D.rowCheck i.val = true) :
    D.mask i < 2^64 ∧ D.color i < 15 ∧
      D.CoverBitRow i ∧ D.PerpBitRow i ∧ D.ColorBitRow i := by
  simp only [Catalogue.rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1,h.1.1.1.2,D.coverCheck_sound i h.1.1.2,
    D.perpCheck_sound i h.1.2,D.colorCheck_sound i h.2⟩

end BinaryOrthogonality
