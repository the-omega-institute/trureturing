/- GID: D5/S3/Combinatorics/Graph/TripartiteH1Repair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/TripartiteH1Repair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete-tripartite H1 exactness and sharp degree-one repair on the octahedron. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.TripartiteH1Repair

abbrev Edge (A B C : Type*) :=
  (A → B → ZMod 2) × (A → C → ZMod 2) × (B → C → ZMod 2)

abbrev Potential (A B C : Type*) :=
  (A → ZMod 2) × (B → ZMod 2) × (C → ZMod 2)

def d0 {A B C : Type*} (g : Potential A B C) : Edge A B C :=
  (fun a b => g.1 a + g.2.1 b,
   fun a c => g.1 a + g.2.2 c,
   fun b c => g.2.1 b + g.2.2 c)

def d1 {A B C : Type*} (f : Edge A B C) (a : A) (b : B) (c : C) : ZMod 2 :=
  f.1 a b + f.2.1 a c + f.2.2 b c

/-- The complete tripartite complex has degree-one kernel equal to the image of d0.
The reverse implication constructs one potential from three anchored edge rows. -/
theorem ker_d1_eq_im_d0 {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C]
    (f : Edge A B C) :
    (∀ a b c, d1 f a b c = 0) ↔ ∃ g : Potential A B C, d0 g = f := by
  constructor
  · intro h
    let a0 : A := Classical.choice inferInstance
    let b0 : B := Classical.choice inferInstance
    let c0 : C := Classical.choice inferInstance
    refine ⟨(fun a => f.1 a b0,
      fun b => f.1 a0 b + f.1 a0 b0,
      fun c => f.2.1 a0 c + f.1 a0 b0), ?_⟩
    apply Prod.ext
    · funext a b
      have h1 := h a b c0
      have h2 := h a b0 c0
      have h3 := h a0 b c0
      have h4 := h a0 b0 c0
      simp only [d1] at h1 h2 h3 h4
      simp only [d0]
      have hs :
          (f.1 a b + f.2.1 a c0 + f.2.2 b c0) +
          (f.1 a b0 + f.2.1 a c0 + f.2.2 b0 c0) +
          (f.1 a0 b + f.2.1 a0 c0 + f.2.2 b c0) +
          (f.1 a0 b0 + f.2.1 a0 c0 + f.2.2 b0 c0) = 0 := by
        rw [h1, h2, h3, h4]
        simp
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      simpa [CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm] using hs
    · apply Prod.ext
      · funext a c
        have h1 := h a b0 c
        have h2 := h a0 b0 c
        simp only [d1] at h1 h2
        simp only [d0]
        have hs :
            (f.1 a b0 + f.2.1 a c + f.2.2 b0 c) +
            (f.1 a0 b0 + f.2.1 a0 c + f.2.2 b0 c) = 0 := by
          rw [h1, h2]
          simp
        apply sub_eq_zero.mp
        rw [CharTwo.sub_eq_add]
        simpa [CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm] using hs
      · funext b c
        have h1 := h a0 b c
        simp only [d1] at h1
        simp only [d0]
        apply sub_eq_zero.mp
        rw [CharTwo.sub_eq_add]
        convert h1 using 1
        ring_nf
        simp [show (2 : ZMod 2) = 0 by decide]
  · rintro ⟨g, rfl⟩ a b c
    simp [d1, d0, CharTwo.add_self_eq_zero, add_assoc, add_left_comm, add_comm]

abbrev BitEdge := Edge Bool Bool Bool
abbrev BitPotential := Potential Bool Bool Bool

def weight (f : BitEdge) : ℕ :=
  (∑ a : Bool, ∑ b : Bool, if f.1 a b ≠ 0 then 1 else 0) +
  (∑ a : Bool, ∑ c : Bool, if f.2.1 a c ≠ 0 then 1 else 0) +
  (∑ b : Bool, ∑ c : Bool, if f.2.2 b c ≠ 0 then 1 else 0)

def defects (f : BitEdge) : ℕ :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
    if d1 f a b c ≠ 0 then 1 else 0

def witness : BitEdge :=
  (fun a b => if a = false ∧ b = true then 1 else 0,
   fun a c => if a = false ∧ c = false then 1 else 0,
   fun b c => if b = false ∧ c = false then 1 else 0)

abbrev Cube := Bool × Bool × Bool

def antipode (x : Cube) : Cube := (!x.1, !x.2.1, !x.2.2)

/-- A dual path changes the A, B, then C coordinate, omitting stationary steps. -/
def cubePath (x y : Cube) : BitEdge :=
  (fun a b => if x.2.2 ≠ y.2.2 ∧ a = y.1 ∧ b = y.2.1 then 1 else 0,
   fun a c => if x.2.1 ≠ y.2.1 ∧ a = y.1 ∧ c = x.2.2 then 1 else 0,
   fun b c => if x.1 ≠ y.1 ∧ b = x.2.1 ∧ c = x.2.2 then 1 else 0)

/-- Pairing the vertices of an even defect set gives a dual chain of cost at most
three per pair. The induction is on the set, not on all edge cochains. -/
private theorem even_defect_filling (s : Finset Cube) (hs : (s.card : ZMod 2) = 0) :
    ∃ h : BitEdge,
      (∀ a b c, d1 h a b c = if (a, b, c) ∈ s then 1 else 0) ∧
      2 * weight h ≤ 3 * s.card := by
  classical
  -- Only the explicit three-step path's local boundary and length are evaluated.
  have path_data : ∀ x y : Cube,
      (∀ a b c, d1 (cubePath x y) a b c =
        (if (a, b, c) = x then 1 else 0) + (if (a, b, c) = y then 1 else 0)) ∧
      weight (cubePath x y) ≤ 3 := by
    decide +kernel
  have subadd (h k : BitEdge) : weight (h + k) ≤ weight h + weight k := by
    have point : ∀ x y : ZMod 2,
        (if x + y ≠ 0 then (1 : ℕ) else 0) ≤
          (if x ≠ 0 then 1 else 0) + (if y ≠ 0 then 1 else 0) := by
      decide +kernel
    have family (u v : Bool → Bool → ZMod 2) :
        (∑ a, ∑ b, if u a b + v a b ≠ 0 then 1 else 0) ≤
          (∑ a, ∑ b, if u a b ≠ 0 then 1 else 0) +
          (∑ a, ∑ b, if v a b ≠ 0 then 1 else 0) := by
      simp_rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => point _ _
    have hAB := family h.1 k.1
    have hAC := family h.2.1 k.2.1
    have hBC := family h.2.2 k.2.2
    simp only [weight, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    omega
  revert hs
  refine s.strongInductionOn ?_
  · intro s ih hs
    by_cases he : s = ∅
    · subst s
      exact ⟨0, by simp [d1], by simp [weight]⟩
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hxcard := Finset.card_erase_add_one hx
    have hyexists : (s.erase x).Nonempty := by
      by_contra hn
      have hz := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [hz] at hxcard
      have hcard : s.card = 1 := by simpa using hxcard.symm
      rw [hcard] at hs
      exact (by decide : (1 : ZMod 2) ≠ 0) hs
    obtain ⟨y, hy⟩ := hyexists
    have hycard := Finset.card_erase_add_one hy
    have hcard : ((s.erase x).erase y).card + 2 = s.card := by omega
    have hseven : (((s.erase x).erase y).card : ZMod 2) = 0 := by
      have hz := congrArg (fun n : ℕ => (n : ZMod 2)) hcard
      simpa [hs, show (2 : ZMod 2) = 0 by decide] using hz
    have hsub : (s.erase x).erase y ⊂ s :=
      Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) (Finset.erase_ssubset hx)
    obtain ⟨h, hh, hweight⟩ := ih _ hsub hseven
    refine ⟨h + cubePath x y, ?_, ?_⟩
    · intro a b c
      have hxy : y ≠ x := (Finset.mem_erase.mp hy).1
      have hymem : y ∈ s := (Finset.mem_erase.mp hy).2
      have hd := (path_data x y).1 a b c
      calc
        d1 (h + cubePath x y) a b c = d1 h a b c + d1 (cubePath x y) a b c := by
          simp [d1]; ring
        _ = (if (a, b, c) ∈ (s.erase x).erase y then 1 else 0) +
            ((if (a, b, c) = x then 1 else 0) + (if (a, b, c) = y then 1 else 0)) := by
          rw [hh, hd]
        _ = if (a, b, c) ∈ s then 1 else 0 := by
          by_cases htx : (a, b, c) = x
          · simp [htx, hx, Ne.symm hxy]
          by_cases hty : (a, b, c) = y
          · simp [hty, hymem, hxy]
          · simp [htx, hty]
    · have hp := (path_data x y).2
      have ha := subadd h (cubePath x y)
      omega

/-- Antipodal defect fibers have explicit three-edge minima; the named witness
has the stated literal support, defects, and minimum repair weight. -/
theorem sharp_three_edge_witness :
    (∀ (f : BitEdge) (x : Cube),
      (∀ a b c, d1 f a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) →
      let w := cubePath x (antipode x)
      (∀ g : BitPotential, 3 ≤ weight (f + d0 g)) ∧
      (∃ g : BitPotential, f + d0 g = w) ∧
      (∀ a b, w.1 a b ≠ 0 ↔ a = !x.1 ∧ b = !x.2.1) ∧
      (∀ a c, w.2.1 a c ≠ 0 ↔ a = !x.1 ∧ c = x.2.2) ∧
      (∀ b c, w.2.2 b c ≠ 0 ↔ b = x.2.1 ∧ c = x.2.2) ∧
      (∀ a b c, d1 w a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) ∧
      weight w = 3 ∧ defects w = 2) ∧
    (∀ a b, witness.1 a b ≠ 0 ↔ a = false ∧ b = true) ∧
    (∀ a c, witness.2.1 a c ≠ 0 ↔ a = false ∧ c = false) ∧
    (∀ b c, witness.2.2 b c ≠ 0 ↔ b = false ∧ c = false) ∧
    (∀ a b c, d1 witness a b c ≠ 0 ↔
      (a, b, c) = (false, true, true) ∨
      (a, b, c) = (true, false, false)) ∧
    weight witness = 3 ∧ defects witness = 2 ∧
    (∀ g : BitPotential, 3 ≤ weight (witness + d0 g)) := by
  have fiber : ∀ (f : BitEdge) (x : Cube),
      (∀ a b c, d1 f a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) →
      let w := cubePath x (antipode x)
      (∀ g : BitPotential, 3 ≤ weight (f + d0 g)) ∧
      (∃ g : BitPotential, f + d0 g = w) ∧
      (∀ a b, w.1 a b ≠ 0 ↔ a = !x.1 ∧ b = !x.2.1) ∧
      (∀ a c, w.2.1 a c ≠ 0 ↔ a = !x.1 ∧ c = x.2.2) ∧
      (∀ b c, w.2.2 b c ≠ 0 ↔ b = x.2.1 ∧ c = x.2.2) ∧
      (∀ a b c, d1 w a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) ∧
      weight w = 3 ∧ defects w = 2 := by
    intro f x hf
    let w := cubePath x (antipode x)
    have bit_value : ∀ z : ZMod 2, (if z ≠ 0 then 1 else 0) = z := by decide +kernel
    have value (a b c : Bool) : d1 f a b c =
        if (a, b, c) = x ∨ (a, b, c) = antipode x then 1 else 0 := by
      simpa only [hf] using (bit_value (d1 f a b c)).symm
    have lower (g : BitPotential) : 3 ≤ weight (f + d0 g) := by
      let h : BitEdge := f + d0 g
      have defect (a b c : Bool) : d1 h a b c = d1 f a b c := by
        simp [h, d1, d0]
        ring_nf
        simp [show (2 : ZMod 2) = 0 by decide]
      have cutA : (∑ b, ∑ c, d1 h x.1 b c) = ∑ b, ∑ c, h.2.2 b c := by
        simp [d1]; ring_nf; simp [show (2 : ZMod 2) = 0 by decide]
      have cutB : (∑ a, ∑ c, d1 h a x.2.1 c) = ∑ a, ∑ c, h.2.1 a c := by
        simp [d1]; ring_nf; simp [show (2 : ZMod 2) = 0 by decide]
      have cutC : (∑ a, ∑ b, d1 h a b x.2.2) = ∑ a, ∑ b, h.1 a b := by
        simp [d1]; ring_nf; simp [show (2 : ZMod 2) = 0 by decide]
      have ha : (∑ b, ∑ c, h.2.2 b c) = 1 := by
        rw [← cutA]; simp_rw [defect, value]
        rcases x with ⟨a, b, c⟩
        cases a <;> cases b <;> cases c <;> decide +kernel
      have hb : (∑ a, ∑ c, h.2.1 a c) = 1 := by
        rw [← cutB]; simp_rw [defect, value]
        rcases x with ⟨a, b, c⟩
        cases a <;> cases b <;> cases c <;> decide +kernel
      have hc : (∑ a, ∑ b, h.1 a b) = 1 := by
        rw [← cutC]; simp_rw [defect, value]
        rcases x with ⟨a, b, c⟩
        cases a <;> cases b <;> cases c <;> decide +kernel
      have family (v : Bool → Bool → ZMod 2)
          (hv : (∑ a, ∑ b, v a b) = 1) :
          1 ≤ ∑ a, ∑ b, if v a b ≠ 0 then 1 else 0 := by
        have hn : ∃ a b, v a b ≠ 0 := by
          by_contra hn
          push Not at hn
          simp [hn] at hv
        obtain ⟨a, b, hab⟩ := hn
        have hs := Finset.single_le_sum (s := (Finset.univ : Finset Bool))
          (f := fun b => if v a b ≠ 0 then (1 : ℕ) else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
        have ht := Finset.single_le_sum (s := (Finset.univ : Finset Bool))
          (f := fun a => ∑ b : Bool, if v a b ≠ 0 then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        have hs' : 1 ≤ ∑ b : Bool, if v a b ≠ 0 then 1 else 0 := by simpa [hab] using hs
        omega
      have hAB := family h.1 hc
      have hAC := family h.2.1 hb
      have hBC := family h.2.2 ha
      change 3 ≤ weight h
      dsimp only [weight]
      omega
    have data :
        (∀ a b, w.1 a b ≠ 0 ↔ a = !x.1 ∧ b = !x.2.1) ∧
        (∀ a c, w.2.1 a c ≠ 0 ↔ a = !x.1 ∧ c = x.2.2) ∧
        (∀ b c, w.2.2 b c ≠ 0 ↔ b = x.2.1 ∧ c = x.2.2) ∧
        (∀ a b c, d1 w a b c ≠ 0 ↔
          (a, b, c) = x ∨ (a, b, c) = antipode x) ∧
        weight w = 3 ∧ defects w = 2 := by
      rcases x with ⟨a, b, c⟩
      cases a <;> cases b <;> cases c <;> decide +kernel
    have same (a b c : Bool) : d1 w a b c = d1 f a b c := by
      rw [← bit_value (d1 w a b c), ← bit_value (d1 f a b c)]
      simp only [hf, data.2.2.2.1]
    have hz : ∀ a b c, d1 (f + w) a b c = 0 := by
      intro a b c
      calc
        d1 (f + w) a b c = d1 f a b c + d1 w a b c := by simp [d1]; ring
        _ = 0 := by rw [same, CharTwo.add_self_eq_zero]
    obtain ⟨g, hg⟩ := (ker_d1_eq_im_d0 (f + w)).mp hz
    refine ⟨lower, ⟨g, ?_⟩, data⟩
    rw [hg]
    apply Prod.ext
    · funext a b; exact CharTwo.add_cancel_left _ _
    · apply Prod.ext
      · funext a c; exact CharTwo.add_cancel_left _ _
      · funext b c; exact CharTwo.add_cancel_left _ _
  refine ⟨fiber, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro g
    have hw : ∀ a b c, d1 witness a b c ≠ 0 ↔
        (a, b, c) = (true, false, false) ∨
        (a, b, c) = antipode (true, false, false) := by decide +kernel
    exact (fiber witness (true, false, false) hw).1 g

/-- Exact unnormalized expansion: a rational repair coefficient p/q is valid
precisely when it is at least 3/2 (the formulation also covers q = 0).
The upper direction is the n=3, k=1 estimate of Dotterrer--Kahle, Proposition 5.5;
the antipodal cut barrier supplies the sharp converse. -/
theorem universal_repair (p q : ℕ) :
    (∀ f : BitEdge, ∃ g : BitPotential,
      q * weight (f + d0 g) ≤ p * defects f) ↔ 3 * q ≤ 2 * p := by
  have upper (f : BitEdge) :
      ∃ g : BitPotential, 2 * weight (f + d0 g) ≤ 3 * defects f := by
    classical
    let s : Finset Cube := Finset.univ.filter fun t => d1 f t.1 t.2.1 t.2.2 ≠ 0
    have bit_value : ∀ z : ZMod 2, (if z ≠ 0 then 1 else 0) = z := by decide +kernel
    have hs : (s.card : ZMod 2) = 0 := by
      calc
        (s.card : ZMod 2) = ∑ t : Cube, d1 f t.1 t.2.1 t.2.2 := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          simp only [Nat.cast_one, s, Finset.sum_filter]
          exact Finset.sum_congr rfl fun t _ => bit_value _
        _ = 0 := by
          simp [Fintype.sum_prod_type, d1]
          ring_nf
          simp [show (2 : ZMod 2) = 0 by decide]
    have hcard : s.card = defects f := by
      simp only [s, defects, Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_prod_type]
    obtain ⟨h, hh, hb⟩ := even_defect_filling s hs
    have same (a b c : Bool) : d1 h a b c = d1 f a b c := by
      rw [hh]
      simpa [s] using bit_value (d1 f a b c)
    have hz : ∀ a b c, d1 (f + h) a b c = 0 := by
      intro a b c
      calc
        d1 (f + h) a b c = d1 f a b c + d1 h a b c := by simp [d1]; ring
        _ = 0 := by rw [same, CharTwo.add_self_eq_zero]
    obtain ⟨g, hg⟩ := (ker_d1_eq_im_d0 (f + h)).mp hz
    refine ⟨g, ?_⟩
    have heq : f + d0 g = h := by
      rw [hg]
      apply Prod.ext
      · funext a b; exact CharTwo.add_cancel_left _ _
      · apply Prod.ext
        · funext a c; exact CharTwo.add_cancel_left _ _
        · funext b c; exact CharTwo.add_cancel_left _ _
    rw [heq]
    simpa [hcard] using hb
  constructor
  · intro h
    obtain ⟨g, hg⟩ := h witness
    rcases sharp_three_edge_witness with ⟨_, _, _, _, _, _, ht, hmin⟩
    have hl := hmin g
    calc
      3 * q = q * 3 := Nat.mul_comm _ _
      _ ≤ q * weight (witness + d0 g) := Nat.mul_le_mul_left q hl
      _ ≤ 2 * p := by simpa [ht, Nat.mul_comm] using hg
  · intro hp f
    obtain ⟨g, hg⟩ := upper f
    refine ⟨g, ?_⟩
    have h₁ := Nat.mul_le_mul_left q hg
    have h₂ := Nat.mul_le_mul_right (defects f) hp
    nlinarith

#print axioms ker_d1_eq_im_d0
#print axioms sharp_three_edge_witness
#print axioms universal_repair

end D5.S3.Combinatorics.Graph.TripartiteH1Repair
