/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic
   mirror-E: none(waiver:unbounded-marked-prefix-arithmetic)
   anchors: []
   utility: none
   digest: Separated signed tails have a strict bound and nonempty marked prefixes are positive. -/

/-
proof_shape: content (marked_prefix_tail_bound)
escape_witness: Bounded signed-list evaluation and the first geometric summand force strict positivity.
admission_basis: escape-witness
Direct frozen dependencies: none; imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

def markedPowers (m p : ℕ) : ℕ := ∑ s ∈ Finset.range m, 2^(p+3*s)
def markedPrefix (n m p : ℕ) (T : ℤ) : Prop :=
  (((n+1)/2 : ℕ) : ℤ) = (markedPowers m p : ℤ)+T ∧
  ∃ tail : List ℤ,
    tail.foldr (fun z x => z+2*x) 0 = T ∧
    (∀ z ∈ tail, z=-1 ∨ z=0 ∨ z=1) ∧
    tail.IsChain (fun a b => a=0 ∨ b=0) ∧
    (∀ k : ℕ, tail[k]?.getD 0 ≠ 0 → k+3≤p)

theorem marked_prefix_tail_bound (n m p : ℕ) (T : ℤ) (hm : 0<m)
    (h : markedPrefix n m p T) : |T| < ((2^(p-2) : ℕ) : ℤ) ∧ 0<n := by
  have bound (ds : List ℤ) (k : ℕ) (hc : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1)
      (hs : ∀ i : ℕ, k≤i → ds[i]?.getD 0=0) :
      -((2^k : ℕ) : ℤ) < ds.foldr (fun z x => z+2*x) 0 ∧
      ds.foldr (fun z x => z+2*x) 0 < ((2^k : ℕ) : ℤ) := by
    induction ds generalizing k with
    | nil =>
      have hp : (0:ℤ)<((2^k : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos k
      simpa only [List.foldr_nil] using And.intro (by omega) hp
    | cons d ds ih =>
      have ht : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1 := fun z hz => hc z (by simp [hz])
      have hd:=hc d (by simp)
      cases k with
      | zero =>
        have hd0 : d=0 := by simpa using hs 0 (by omega)
        have hs' : ∀ i : ℕ, 0≤i → ds[i]?.getD 0=0 := by
          intro i _; simpa using hs (i+1) (by omega)
        have hv:=ih 0 ht hs'
        simp only [pow_zero,Int.natCast_one] at hv ⊢
        simp only [List.foldr_cons,hd0];omega
      | succ k =>
        have hs' : ∀ i : ℕ, k≤i → ds[i]?.getD 0=0 := by
          intro i hi;simpa using hs (i+1) (by omega)
        have hv:=ih k ht hs'
        simp only [List.foldr_cons,pow_succ,Int.natCast_mul]
        rcases hd with rfl | rfl | rfl <;> omega
  obtain ⟨he,ds,hv,hc,_,hs⟩:=h
  have support : ∀ i : ℕ, p-2≤i → ds[i]?.getD 0=0 := by
    intro i hi
    by_contra hn
    have hh:=hs i hn
    omega
  have hb:=bound ds (p-2) hc support
  rw [hv] at hb
  have habs : |T|<((2^(p-2) : ℕ) : ℤ) := abs_lt.mpr hb
  have hpow : 2^(p-2) ≤ 2^p := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hl : 2^p ≤ markedPowers m p := by
    have hz : 0∈Finset.range m := by simpa using hm
    have hh:=Finset.single_le_sum (f:=fun s : ℕ => 2^(p+3*s)) (fun _ _ => Nat.zero_le _) hz
    simpa only [markedPowers,Nat.mul_zero,Nat.add_zero] using hh
  refine ⟨habs,?_⟩
  have hpos : (0:ℤ)<(((n+1)/2 : ℕ) : ℤ) := by
    have hl' : ((2^p : ℕ) : ℤ)≤(markedPowers m p : ℤ) := by exact_mod_cast hl
    have hp' : ((2^(p-2) : ℕ) : ℤ)≤((2^p : ℕ) : ℤ) := by exact_mod_cast hpow
    omega
  omega
end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marked_prefix_tail_bound
