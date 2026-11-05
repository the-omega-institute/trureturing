/- GID: D5/S3/Combinatorics/Circle/DyadicResetBlocks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/DyadicResetBlocks
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Every legal reset word decomposes into positive exact-height blocks. -/
module
public import D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
import all D5.S3.Combinatorics.Circle.ThreeBitSource

/-! Reset decomposition retains the original lists of physical occurrences. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.DyadicResetBlocks
open SourceWidth ExpandingSourcePath MixedSuffixEnergy

/-- Concatenate each positive segment and its actual resetting occurrence. -/
def packets {α : Type*} (P : List (List α × α)) : List α :=
  P.flatMap (fun p => p.1 ++ [p.2])

def Positive {α : Type*} (f : α → ℤ) (L : List α) : Prop :=
  ∀ a ∈ L, 0 < f a

def Complete {α : Type*} (f : α → ℤ) (M : ℤ) (P : List (List α × α)) : Prop :=
  ∀ p ∈ P, Positive f p.1 ∧ mass f p.1 = M ∧ f p.2 = -M

theorem complete_mass {α : Type*} {f : α → ℤ} {M : ℤ}
    {P : List (List α × α)} (hP : Complete f M P) : mass f (packets P) = 0 := by
  induction P with
  | nil => simp [packets, mass]
  | cons p P ih =>
    obtain ⟨_, hp, hz⟩ := hP p (by simp)
    have ht := ih (fun q hq => hP q (by simp [hq]))
    change mass f ((p.1 ++ [p.2]) ++ packets P) = 0
    simp only [mass, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, add_zero]
    change mass f p.1 + f p.2 + mass f (packets P) = 0
    rw [hp, hz, ht]; ring

/-- Positive monotonicity controls every interior prefix of every complete
packet, and each actual reset returns its endpoint to zero. -/
theorem complete_strip {α : Type*} {f : α → ℤ} {M : ℤ}
    {P : List (List α × α)} (hM : 0 ≤ M) (hP : Complete f M P) :
    InStrip f M 0 (packets P) := by
  induction P with
  | nil => simpa [packets, InStrip] using hM
  | cons p P ih =>
    obtain ⟨hpos, hmass, hneg⟩ := hP p (by simp)
    have ht := ih (fun q hq => hP q (by simp [hq]))
    have hs : InStrip f M 0 p.1 := ThreeBitSource.positive_block_strip
      (fun a ha => le_of_lt (hpos a ha)) (le_refl 0) (by simpa [mass] using le_of_eq hmass)
    have hsz : InStrip f M (0 + mass f p.1) [p.2] := by
      rw [hmass]
      simpa [InStrip, hneg] using hM
    have hblock := inStrip_append hs hsz
    change InStrip f M 0 ((p.1 ++ [p.2]) ++ packets P)
    apply inStrip_append hblock
    have hz : mass f (p.1 ++ [p.2]) = 0 := by simp [mass] at hmass ⊢; omega
    change InStrip f M (0 + mass f (p.1 ++ [p.2])) (packets P)
    simpa only [hz, add_zero] using ht

/-- The reset height and every positive block are derived from all-prefix
legality; no placement or arrival hypothesis is assumed. -/
theorem reset_decomposition {α : Type*} (f : α → ℤ) (M : ℤ)
    (steps : ∀ a, 0 < f a ∨ f a = -M) (W : List α)
    (hW : InStrip f M 0 W) :
    ∃ P : List (List α × α), ∃ T : List α,
      W = packets P ++ T ∧ Complete f M P ∧ Positive f T ∧
      0 ≤ mass f T ∧ mass f T ≤ M := by
  induction W using List.reverseRecOn with
  | nil =>
    have h0 := inStrip_prefix hW 0
    refine ⟨[], [], by simp [packets], by simp [Complete], by simp [Positive], ?_⟩
    simpa [mass] using h0
  | append_singleton W a ih =>
    obtain ⟨hprefix, _⟩ := strip_split W [a] hW
    obtain ⟨P, T, heq, hP, hT, hlo, hhi⟩ := ih hprefix
    have hz := complete_mass hP
    have he : mass f W = mass f T := by
      rw [heq]
      simp only [mass, List.map_append, List.sum_append]
      change mass f (packets P) + mass f T = mass f T
      rw [hz]; ring
    have hend := inStrip_prefix hW (W ++ [a]).length
    simp only [List.take_length, List.map_append, mass, List.sum_append,
      List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
      zero_add] at hend
    change 0 ≤ mass f W + f a ∧ mass f W + f a ≤ M at hend
    rw [he] at hend
    rcases steps a with ha | ha
    · refine ⟨P, T ++ [a], ?_, hP, ?_, ?_⟩
      · rw [heq, List.append_assoc]
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hT x hx
        · exact ha
      · simpa [mass] using hend
    · have htM : mass f T = M := by omega
      refine ⟨P ++ [(T, a)], [], ?_, ?_, by simp [Positive], ?_⟩
      · simp [packets, heq, List.flatMap_append, List.append_assoc]
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hP p hp
        · exact ⟨hT, htM, ha⟩
      · simp only [mass, List.map_nil, List.sum_nil, le_refl, true_and]
        omega

/-- Each positive block has at most one top coin. The final block contributes
one only when its endpoint is at least that denomination. -/
theorem reset_top_bound {α : Type*} (f : α → ℤ) (B M : ℤ)
    (hB : 0 < B) (hM : M < 2 * B)
    (steps : ∀ a, 0 < f a ∨ f a = -M) (W : List α)
    (hW : InStrip f M 0 W) :
    (W.countP (fun a => f a = B) : ℤ) ≤
      W.countP (fun a => f a = -M) + if B ≤ mass f W then 1 else 0 := by
  have hM0 : 0 ≤ M := by simpa [mass] using (inStrip_prefix hW 0).2
  have hBM : B ≠ -M := by omega
  induction W using List.reverseRecOn with
  | nil => simp [mass]; omega
  | append_singleton W a ih =>
    obtain ⟨hw, _⟩ := strip_split W [a] hW
    have h := ih hw
    have hend := inStrip_prefix hW (W ++ [a]).length
    simp only [List.take_length, mass, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
      zero_add] at hend
    change 0 ≤ mass f W + f a ∧ mass f W + f a ≤ M at hend
    have hstart := inStrip_prefix hw W.length
    simp only [List.take_length, zero_add] at hstart
    change 0 ≤ mass f W ∧ mass f W ≤ M at hstart
    have hsum : mass f (W ++ [a]) = mass f W + f a := by simp [mass]
    simp only [List.countP_append, List.countP_cons, List.countP_nil, Nat.cast_add,
      hsum]
    rcases steps a with ha | ha
    · have hn : f a ≠ -M := by omega
      by_cases hb : f a = B
      · have hlow : mass f W < B := by omega
        simp only [hb, hn, decide_true, decide_false, ite_true, ite_false,
          Nat.cast_one, Nat.cast_zero, add_zero]
        split_ifs at h ⊢ <;> simp_all <;> omega
      · simp only [hb, hn, decide_false, ite_false, Nat.cast_zero, add_zero]
        split_ifs at h ⊢ <;> simp_all <;> omega
    · have hb : f a ≠ B := by omega
      simp only [ha, hb, hBM, Ne.symm hBM, decide_true, decide_false, ite_true, ite_false,
        Nat.cast_one, Nat.cast_zero, add_zero]
      split_ifs at h ⊢ <;> simp_all <;> omega

end D5.S3.Combinatorics.Circle.DyadicResetBlocks
