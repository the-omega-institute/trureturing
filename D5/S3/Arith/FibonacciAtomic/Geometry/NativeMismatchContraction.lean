/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Two-step contraction of native first-disagreement mass. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction

open GenealogicalFiberTransport (Source substitution)
open ActualImageAlphaSeparation (frontier)
open scoped BigOperators

/-- Rational discount mass of the existing first-disagreement frontier. -/
def mass (q : ℚ) (s t : Source) : ℚ :=
  ∑ p ∈ frontier s t, q ^ p.length

private theorem mass_self (q : ℚ) (s : Source) : mass q s s = 0 := by
  cases s <;> simp [mass, ActualImageAlphaSeparation.frontier]

theorem mass_of_of (q : ℚ) (b c : Bool) (h : b ≠ c) :
    mass q (.of b) (.of c) = 1 := by
  have hn : (FreeMagma.of b : Source) ≠ .of c := by
    intro he
    injection he with he
    exact h he
  simp [mass, ActualImageAlphaSeparation.frontier, hn]

private theorem mass_of_mul (q : ℚ) (b : Bool) (u v : Source) :
    mass q (.of b) (.mul u v) = 1 := by
  simp [mass, ActualImageAlphaSeparation.frontier]

private theorem mass_mul_of (q : ℚ) (u v : Source) (b : Bool) :
    mass q (.mul u v) (.of b) = 1 := by
  simp [mass, ActualImageAlphaSeparation.frontier]

private theorem mass_mul_mul (q : ℚ) (s u t v : Source) :
    mass q (.mul s u) (.mul t v) = q * (mass q s t + mass q u v) := by
  by_cases he : (.mul s u : Source) = .mul t v
  · injection he with hs hu
    subst t
    subst v
    rw [mass_self, mass_self, mass_self]
    ring
  · have hd : Disjoint ((frontier s t).image (List.cons false))
        ((frontier u v).image (List.cons true)) := by
      simp only [Finset.disjoint_left, Finset.mem_image]
      rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩
      cases hb
    simp only [mass, ActualImageAlphaSeparation.frontier, if_neg he]
    rw [Finset.sum_union hd,
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
      Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
    simp only [List.length_cons, pow_succ, ← Finset.sum_mul]
    ring

private theorem mass_le_one (q : ℚ) (hq : 0 < q) (hhalf : q ≤ 1 / 2)
    (s t : Source) : mass q s t ≤ 1 := by
  induction s generalizing t with
  | of b =>
    cases t with
    | of c =>
      by_cases h : b = c
      · subst c
        rw [mass_self]
        norm_num
      · rw [mass_of_of q b c h]
    | mul u v => rw [mass_of_mul]
  | mul s u hs hu =>
    cases t with
    | of c => rw [mass_mul_of]
    | mul t v =>
      rw [mass_mul_mul]
      calc
        q * (mass q s t + mass q u v) ≤ q * (1 + 1) :=
          mul_le_mul_of_nonneg_left (add_le_add (hs t) (hu v)) hq.le
        _ ≤ 1 := by linarith

private theorem even_mul (s t : Source) :
    substitution^[2] (.mul s t) = .mul (substitution^[2] s) (substitution^[2] t) :=
  Function.Semiconj₂.iterate
    (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
      fun s t => substitution.map_mul s t) 2 s t

private theorem even_root (s : Source) :
    ∃ u v : Source, substitution^[2] s = .mul u v := by
  cases s with
  | of b =>
    cases b
    · exact ⟨.mul (.of false) (.of true), .of false, rfl⟩
    · exact ⟨.of false, .of true, rfl⟩
  | mul s t => exact ⟨substitution^[2] s, substitution^[2] t, even_mul s t⟩

/-- Equal, distinct-leaf, mixed-root and common-branch cases after two steps. -/
theorem root_cases (q : ℚ) (hq : 0 < q) (hhalf : q ≤ 1 / 2) :
    (∀ s t : Source, s = t → mass q (substitution^[2] s) (substitution^[2] t) = 0) ∧
    (∀ b c : Bool, b ≠ c →
      mass q (substitution^[2] (.of b)) (substitution^[2] (.of c)) = 2 * q) ∧
    (∀ (b : Bool) (u v : Source),
      mass q (substitution^[2] (.of b)) (substitution^[2] (.mul u v)) ≤ 2 * q ∧
      mass q (substitution^[2] (.mul u v)) (substitution^[2] (.of b)) ≤ 2 * q) ∧
    (∀ s u t v : Source,
      mass q (substitution^[2] (.mul s u)) (substitution^[2] (.mul t v)) =
        q * (mass q (substitution^[2] s) (substitution^[2] t) +
          mass q (substitution^[2] u) (substitution^[2] v))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t h
    subst t
    exact mass_self q _
  · intro b c h
    cases b <;> cases c
    · exact False.elim (h rfl)
    · change mass q (.mul (.mul (.of false) (.of true)) (.of false))
        (.mul (.of false) (.of true)) = 2 * q
      rw [mass_mul_mul, mass_mul_of, mass_of_of q false true (by decide)]
      ring
    · change mass q (.mul (.of false) (.of true))
        (.mul (.mul (.of false) (.of true)) (.of false)) = 2 * q
      rw [mass_mul_mul, mass_of_mul, mass_of_of q true false (by decide)]
      ring
    · exact False.elim (h rfl)
  · intro b u v
    obtain ⟨a, c, he⟩ := even_root (.of b)
    rw [he, even_mul, mass_mul_mul, mass_mul_mul]
    constructor
    · calc
        q * (mass q a (substitution^[2] u) + mass q c (substitution^[2] v)) ≤
            q * (1 + 1) := mul_le_mul_of_nonneg_left
          (add_le_add (mass_le_one q hq hhalf _ _) (mass_le_one q hq hhalf _ _)) hq.le
        _ = 2 * q := by ring
    · calc
        q * (mass q (substitution^[2] u) a + mass q (substitution^[2] v) c) ≤
            q * (1 + 1) := mul_le_mul_of_nonneg_left
          (add_le_add (mass_le_one q hq hhalf _ _) (mass_le_one q hq hhalf _ _)) hq.le
        _ = 2 * q := by ring
  · intro s u t v
    rw [even_mul, even_mul, mass_mul_mul]

/-- Two native substitution steps contract every finite source pair by at most 2q. -/
theorem two_step_contraction (q : ℚ) (hq : 0 < q) (hhalf : q ≤ 1 / 2)
    (s t : Source) :
    mass q (substitution^[2] s) (substitution^[2] t) ≤ 2 * q * mass q s t := by
  have roots := root_cases q hq hhalf
  induction s generalizing t with
  | of b =>
    cases t with
    | of c =>
      by_cases h : b = c
      · subst c
        rw [roots.1 _ _ rfl, mass_self]
        norm_num
      · rw [roots.2.1 b c h, mass_of_of q b c h, mul_one]
    | mul u v =>
      rw [mass_of_mul, mul_one]
      exact (roots.2.2.1 b u v).1
  | mul s u hs hu =>
    cases t with
    | of b =>
      rw [mass_mul_of, mul_one]
      exact (roots.2.2.1 b s u).2
    | mul t v =>
      rw [roots.2.2.2, mass_mul_mul]
      calc
        q * (mass q (substitution^[2] s) (substitution^[2] t) +
            mass q (substitution^[2] u) (substitution^[2] v)) ≤
            q * (2 * q * mass q s t + 2 * q * mass q u v) :=
          mul_le_mul_of_nonneg_left (add_le_add (hs t) (hu v)) hq.le
        _ = 2 * q * (q * (mass q s t + mass q u v)) := by ring

/-- The uniform contraction iterates over all even times, including time zero. -/
theorem even_iterates (q : ℚ) (hq : 0 < q) (hhalf : q ≤ 1 / 2)
    (n : ℕ) (s t : Source) :
    mass q (substitution^[2 * n] s) (substitution^[2 * n] t) ≤
      (2 * q) ^ n * mass q s t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2 * n) 2,
      Function.iterate_add_apply, Function.iterate_add_apply]
    calc
      mass q (substitution^[2] (substitution^[2 * n] s))
          (substitution^[2] (substitution^[2 * n] t)) ≤
          2 * q * mass q (substitution^[2 * n] s) (substitution^[2 * n] t) :=
        two_step_contraction q hq hhalf _ _
      _ ≤ 2 * q * ((2 * q) ^ n * mass q s t) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (2 * q) ^ (n + 1) * mass q s t := by ring

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeMismatchContraction
