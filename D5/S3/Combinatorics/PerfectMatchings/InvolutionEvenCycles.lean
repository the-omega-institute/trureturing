/- GID: D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [library/Combinatorics/egecioglu1990pfaffian]
   utility: none
   digest: Rooted interlacing of ordered perfect matchings and even permutation cycles. -/

import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import D5.S3.Zeros.Convolution.PerfectMatchingCount

/-! Ordered matching edges interlace from the least vertex of each full component. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles

open Equiv
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open InvolutionOrbitSplit

variable {X : Type*} [Fintype X] [LinearOrder X]

private theorem connected_comm (s t : Perm X) (x y : X) :
    Connected s t x y ↔ Connected t s x y := by
  constructor <;> intro h <;> induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.tail hab.symm

private theorem connected_symm (s t : FixedPointFreeInvolution X) {x y : X}
    (h : Connected s.val t.val x y) : Connected s.val t.val y x := by
  induction h with
  | refl => exact .refl
  | @tail a b h hab ih =>
    apply Relation.ReflTransGen.trans _ ih
    apply Relation.ReflTransGen.single
    rcases hab with h | h
    · left; rw [← h]; exact s.property.1 a
    · right; rw [← h]; exact t.property.1 a

private def component (s t : FixedPointFreeInvolution X) (x : X) : Finset X :=
  Finset.univ.filter fun y => (t.val * s.val).SameCycle x y ∨
    (t.val * s.val).SameCycle (t.val x) y

private theorem mem_component (s t : FixedPointFreeInvolution X) (x y : X) :
    y ∈ component s t x ↔ Connected s.val t.val x y := by
  simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (connected_iff_rotation_orbits t.val s.val t.property.1 s.property.1 x y).symm.trans
    (connected_comm t.val s.val x y)

private theorem component_nonempty (s t : FixedPointFreeInvolution X) (x : X) :
    (component s t x).Nonempty := ⟨x, (mem_component s t x x).mpr .refl⟩

/-- The least vertex of the actual two-colored matching component through x. -/
def componentRoot (s t : FixedPointFreeInvolution X) (x : X) : X :=
  (component s t x).min' (component_nonempty s t x)

private theorem root_mem (s t : FixedPointFreeInvolution X) (x : X) :
    Connected s.val t.val x (componentRoot s t x) :=
  (mem_component s t x _).mp (Finset.min'_mem _ _)

private theorem root_eq (s t : FixedPointFreeInvolution X) {x y : X}
    (h : Connected s.val t.val x y) : componentRoot s t x = componentRoot s t y := by
  have he : component s t x = component s t y := by
    ext z
    rw [mem_component, mem_component]
    exact ⟨fun hz => (connected_symm s t h).trans hz, fun hz => h.trans hz⟩
  apply le_antisymm
  · exact Finset.min'_le _ _ (he.symm ▸ Finset.min'_mem _ _)
  · exact Finset.min'_le _ _ (he ▸ Finset.min'_mem _ _)

private theorem root_left (s t : FixedPointFreeInvolution X) (x : X) :
    componentRoot s t (s.val x) = componentRoot s t x :=
  (root_eq s t (Relation.ReflTransGen.single (Or.inl rfl))).symm

private theorem root_right (s t : FixedPointFreeInvolution X) (x : X) :
    componentRoot s t (t.val x) = componentRoot s t x :=
  (root_eq s t (Relation.ReflTransGen.single (Or.inr rfl))).symm

/-- The product orbit containing the least vertex is the s-first phase. -/
def firstPhase (s t : FixedPointFreeInvolution X) (x : X) : Prop :=
  (t.val * s.val).SameCycle (componentRoot s t x) x

instance (s t : FixedPointFreeInvolution X) (x : X) : Decidable (firstPhase s t x) :=
  inferInstanceAs (Decidable ((t.val * s.val).SameCycle (componentRoot s t x) x))

private theorem exchange (A B : Set X) (f : Perm X) (hf : Function.Involutive f)
    (hd : Disjoint A B) (hi : f '' A = B) {x : X} (hx : x ∈ A ∪ B) :
    f x ∈ A ↔ x ∉ A := by
  have him {z : X} (hz : z ∈ A) : f z ∈ B := hi ▸ Set.mem_image_of_mem f hz
  constructor
  · intro h hxa
    exact Set.disjoint_left.mp hd h (him hxa)
  · intro hn
    obtain ⟨z, hz, hzx⟩ := (hi ▸ (hx.resolve_left hn) : x ∈ f '' A)
    simpa only [← hzx, hf z] using hz

private theorem phase_left (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (s.val x) ↔ ¬ firstPhase s t x := by
  rw [firstPhase, root_left]
  let m := componentRoot s t x
  have hc := component_split t.val s.val t.property.1 s.property.1
    t.property.2 s.property.2 m
  apply exchange _ _ s.val s.property.1 hc.1 hc.2.2.2.2.2
  rw [← hc.2.2.2.1]
  exact (connected_comm s.val t.val m x).mp (connected_symm s t (root_mem s t x))

private theorem phase_right (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (t.val x) ↔ ¬ firstPhase s t x := by
  rw [firstPhase, root_right]
  let m := componentRoot s t x
  have hc := component_split t.val s.val t.property.1 s.property.1
    t.property.2 s.property.2 m
  apply exchange _ _ t.val t.property.1 hc.1 hc.2.2.2.2.1
  rw [← hc.2.2.2.1]
  exact (connected_comm s.val t.val m x).mp (connected_symm s t (root_mem s t x))

/-- Interlace the two product orbits, following s first at each component minimum. -/
def interlace (s t : FixedPointFreeInvolution X) : Perm X where
  toFun x := if firstPhase s t x then s.val x else t.val x
  invFun x := if firstPhase s t x then t.val x else s.val x
  left_inv x := by
    by_cases h : firstPhase s t x
    · simp only [ite_eq_left h, ite_eq_right ((phase_left s t x).not.mpr (not_not.mpr h)),
        s.property.1 x]
    · simp only [ite_eq_right h, ite_eq_left ((phase_right s t x).mpr h), t.property.1 x]
  right_inv x := by
    by_cases h : firstPhase s t x
    · simp only [ite_eq_left h, ite_eq_right ((phase_right s t x).not.mpr (not_not.mpr h)),
        t.property.1 x]
    · simp only [ite_eq_right h, ite_eq_left ((phase_left s t x).mpr h), s.property.1 x]

private theorem interlace_apply (s t : FixedPointFreeInvolution X) (x : X) :
    interlace s t x = if firstPhase s t x then s.val x else t.val x := rfl

private theorem interlace_flip (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (interlace s t x) ↔ ¬ firstPhase s t x := by
  rw [interlace_apply]
  split_ifs <;> first | exact phase_left s t x | exact phase_right s t x

private theorem interlace_free (s t : FixedPointFreeInvolution X) (x : X) :
    interlace s t x ≠ x := by
  rw [interlace_apply]
  split_ifs <;> first | exact s.property.2 x | exact t.property.2 x

private theorem phase_of_rotation (s t : FixedPointFreeInvolution X) {x y : X}
    (h : (t.val * s.val).SameCycle x y) : firstPhase s t x ↔ firstPhase s t y := by
  have hc : Connected s.val t.val x y := (connected_comm t.val s.val x y).mp
    ((connected_iff_rotation_orbits t.val s.val t.property.1 s.property.1 x y).mpr
      (Or.inl h))
  unfold firstPhase
  rw [← root_eq s t hc]
  exact ⟨fun hx => hx.trans h, fun hy => hy.trans h.symm⟩

private theorem phase_root (s t : FixedPointFreeInvolution X) (x : X) :
    firstPhase s t (componentRoot s t x) := by
  unfold firstPhase
  rw [← root_eq s t (root_mem s t x)]
  exact Perm.SameCycle.refl _ _

private theorem interlace_powers (s t : FixedPointFreeInvolution X) (x : X)
    (hx : firstPhase s t x) (k : ℕ) :
    (interlace s t ^ (2*k)) x = ((t.val * s.val)^k) x ∧
    (interlace s t ^ (2*k+1)) x = s.val (((t.val * s.val)^k) x) := by
  have hp (n : ℕ) : firstPhase s t (((t.val * s.val)^n) x) :=
    (phase_of_rotation s t (Perm.SameCycle.refl _ x).pow_right).mp hx
  have he : ∀ n : ℕ, (interlace s t ^ (2*n)) x = ((t.val * s.val)^n) x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn : 2*(n+1) = 1+(1+2*n) := by omega
      rw [hn, pow_add, pow_add, pow_one, Perm.mul_apply, Perm.mul_apply, ih,
        interlace_apply, ite_eq_left (hp n), interlace_apply,
        ite_eq_right ((phase_left s t _).not.mpr (not_not.mpr (hp n))),
        pow_succ', Perm.mul_apply, Perm.mul_apply]
  refine ⟨he k, ?_⟩
  rw [pow_succ', Perm.mul_apply, he k, interlace_apply, ite_eq_left (hp k)]

private theorem interlace_connected (s t : FixedPointFreeInvolution X) (x y : X) :
    (interlace s t).SameCycle x y ↔ Connected s.val t.val x y := by
  have hedge (z : X) : Connected s.val t.val z (interlace s t z) := by
    rw [interlace_apply]
    split_ifs
    · exact .single (Or.inl rfl)
    · exact .single (Or.inr rfl)
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => exact .refl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hedge _)
  · intro h
    let m := componentRoot s t x
    have hp := interlace_powers s t m (phase_root s t x)
    have hc := component_split t.val s.val t.property.1 s.property.1
      t.property.2 s.property.2 m
    have hreach (z : X) (hz : Connected s.val t.val m z) :
        (interlace s t).SameCycle m z := by
      have hz' : z ∈ RotationOrbit (t.val * s.val) m ∪
          RotationOrbit (t.val * s.val) (t.val m) := by
        rw [← hc.2.2.2.1]
        exact (connected_comm s.val t.val m z).mp hz
      rcases hz' with hz' | hz'
      · obtain ⟨k, hk⟩ := hz'.exists_nat_pow_eq
        exact ⟨(2*k : ℕ), by simpa only [zpow_natCast] using (hp k).1.trans hk⟩
      · rw [← hc.2.2.2.2.2] at hz'
        obtain ⟨w, hw, rfl⟩ := hz'
        obtain ⟨k, hk⟩ := hw.exists_nat_pow_eq
        exact ⟨(2*k+1 : ℕ), by
          simpa only [zpow_natCast, hk] using (hp k).2⟩
    have hm := connected_symm s t (root_mem s t x)
    exact (hreach x hm).symm.trans (hreach y (hm.trans h))

private theorem parity_along (q : Perm X) (P : X → Prop)
    (hf : ∀ x, P (q x) ↔ ¬ P x) (x : X) (n : ℕ) :
    P ((q^n) x) ↔ (Even n ↔ P x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, hf, ih, Nat.even_add_one, Nat.odd_iff_not_even]
    tauto

private theorem interlace_even_cycles (s t : FixedPointFreeInvolution X)
    (c : Perm X) (hc : c ∈ (interlace s t).cycleFactorsFinset) :
    Even c.support.card := by
  obtain ⟨x, hx⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
  have he := (Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc).pow_card_apply hx
  have hp := parity_along (interlace s t) (firstPhase s t) (interlace_flip s t)
    x c.support.card
  rw [he] at hp
  tauto

/-- The forward map retains the actual permutation, including common transpositions. -/
def forward (p : FixedPointFreeInvolution X × FixedPointFreeInvolution X) :
    {q : Perm X // (∀ x, q x ≠ x) ∧
      ∀ c ∈ q.cycleFactorsFinset, Even c.support.card} :=
  ⟨interlace p.1 p.2, interlace_free p.1 p.2, interlace_even_cycles p.1 p.2⟩

end D5.S3.Combinatorics.PerfectMatchings.InvolutionEvenCycles
