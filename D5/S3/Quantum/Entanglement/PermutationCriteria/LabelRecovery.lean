/- GID: D5/S3/Quantum/Entanglement/PermutationCriteria/LabelRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PermutationCriteria/LabelRecovery
   mirror-E: none(waiver:combinatorial reconstruction)
   anchors: []
   utility: none
   digest: Paired Boolean labels are reconstructed from their sectors and pair distances. -/

import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery

universe u

/-- The two labels at a site belong to the same matrix side. -/
def sameSide (x : Bool × Bool) : Prop := x.1 = x.2

/-- The number of coordinate disagreements between two paired labels. -/
def pairDistance (x y : Bool × Bool) : ℕ :=
  (if x.1 = y.1 then 0 else 1) + (if x.2 = y.2 then 0 else 1)

/-- Exchange the coordinates when requested, then complement both when requested. -/
def transform (swap complement : Bool) (x : Bool × Bool) : Bool × Bool :=
  if swap then (Bool.xor x.2 complement, Bool.xor x.1 complement)
  else (Bool.xor x.1 complement, Bool.xor x.2 complement)

private theorem binary_labels {ι : Type u} (p : ι → Prop) (a b : ι → Bool)
    (h : ∀ i j, p i → p j → (a i = a j ↔ b i = b j)) :
    ∃ c : Bool, ∀ i, p i → b i = Bool.xor (a i) c := by
  classical
  by_cases hp : ∃ i, p i
  · obtain ⟨k, hk⟩ := hp
    refine ⟨Bool.xor (a k) (b k), ?_⟩
    intro i hi
    have hh := h i k hi hk
    cases ha : a i <;> cases hb : b i <;>
      cases hak : a k <;> cases hbk : b k <;> simp_all
  · exact ⟨false, fun i hi => (hp ⟨i, hi⟩).elim⟩

private theorem sector_kernel : ∀ x y z w : Bool × Bool,
    (sameSide x ↔ sameSide z) → (sameSide y ↔ sameSide w) →
    (sameSide x ↔ sameSide y) → pairDistance x y = pairDistance z w →
    (x.1 = y.1 ↔ z.1 = w.1) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨g, h⟩
  unfold sameSide pairDistance
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

private theorem sector_transform : ∀ (x y : Bool × Bool) (cD cO : Bool),
    (sameSide x ↔ sameSide y) →
    (sameSide x → y.1 = Bool.xor x.1 cD) →
    (¬ sameSide x → y.1 = Bool.xor x.1 cO) →
    y = transform (Bool.xor cD cO) cD x := by
  unfold sameSide transform
  decide

/-- Sector membership and all pair distances determine paired Boolean labels up to
one global coordinate exchange and one global simultaneous complementation. -/
theorem recover_labels {ι : Type u} (f g : ι → Bool × Bool)
    (hside : ∀ i, sameSide (f i) ↔ sameSide (g i))
    (hdist : ∀ i j, pairDistance (f i) (f j) = pairDistance (g i) (g j)) :
    ∃ swap complement : Bool, ∀ i, g i = transform swap complement (f i) := by
  obtain ⟨cD, hD⟩ := binary_labels (fun i => sameSide (f i))
    (fun i => (f i).1) (fun i => (g i).1) (by
      intro i j hi hj
      exact sector_kernel (f i) (f j) (g i) (g j) (hside i) (hside j)
        (iff_of_true hi hj) (hdist i j))
  obtain ⟨cO, hO⟩ := binary_labels (fun i => ¬ sameSide (f i))
    (fun i => (f i).1) (fun i => (g i).1) (by
      intro i j hi hj
      exact sector_kernel (f i) (f j) (g i) (g j) (hside i) (hside j)
        (iff_of_false hi hj) (hdist i j))
  exact ⟨Bool.xor cD cO, cD, fun i =>
    sector_transform (f i) (g i) cD cO (hside i) (hD i) (hO i)⟩

#print axioms recover_labels

end D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery
