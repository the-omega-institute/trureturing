/- GID: D5/S1/Digit/YanevRunCompressionClosedForm
   generality: G
   mirror-B: D5/B/S1/Digit/YanevRunCompressionClosedForm
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Binary run compression satisfies Yanev's closed form for every natural number. -/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.SplitBy

/-! Binary digits are little-endian. Splitting at unequal adjacent digits and
retaining one head per block implements the run compression in OEIS A090079.
The parity term `(1-(-1)^n)/2 = n mod 2` is read in the integers. The formula
is multiplied by 3 to stay in ℕ; its subtraction is natural subtraction.

The definitions specify functions on all naturals, and the proofs use symbolic
list induction and run invariants. No declaration is a bounded enumeration,
checker, numeric reduction, or certified instance; hence `utility: none`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.YanevRunCompressionClosedForm

/-- Number of maximal constant blocks of little-endian binary digits. -/
def runs (n : ℕ) : ℕ := ((Nat.digits 2 n).splitBy (· == ·)).length

/-- Retain the head of every maximal constant block and decode in base two. -/
def a (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (((Nat.digits 2 n).splitBy (· == ·)).map List.head!)

/-- Yanev's formula for the literal binary run compression, including zero. -/
theorem result (n : ℕ) : 3 * a n = 2 ^ (runs n + 1) + n % 2 - 2 := by
  have alternating_value : ∀ (l : List ℕ)
      (hbits : ∀ d ∈ l, d < 2)
      (halt : l.IsChain (· ≠ ·))
      (hlast : l.getLast? = some 1),
      3 * Nat.ofDigits 2 l + 2 = 2 ^ (l.length + 1) + l.head! := by
    intro l hbits halt hlast
    induction l with
    | nil => simp at hlast
    | cons x xs ih =>
        cases xs with
        | nil =>
            have hx : x = 1 := by simpa using hlast
            simp [hx, Nat.ofDigits]
        | cons y ys =>
            have hx : x < 2 := hbits x (by simp)
            have hy : y < 2 := hbits y (by simp)
            have hxy : x + y = 1 := by
              have hne := (List.isChain_cons_cons.mp halt).1
              omega
            have ht : (y :: ys).getLast? = some 1 := by simpa using hlast
            have hi := ih (fun d hd => hbits d (by simp [hd])) halt.tail ht
            simp only [Nat.ofDigits_cons, List.length_cons, List.head!_cons, pow_succ] at hi ⊢
            omega
  by_cases hn : n = 0
  · subst n
    simp [a, runs]
  let bs := (Nat.digits 2 n).splitBy (· == ·)
  let c := bs.map List.head!
  have hd : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hb : bs ≠ [] := List.splitBy_ne_nil.mpr hd
  have hnblk : ∀ s ∈ bs, s ≠ [] := fun _ hs => List.ne_nil_of_mem_splitBy hs
  have hconst : ∀ s ∈ bs, ∀ hs : s ≠ [], s.getLast hs = s.head! := by
    intro s hs hne
    have hsChain : s.IsChain (· = ·) := by
      simpa only [beq_iff_eq] using (List.isChain_of_mem_splitBy hs)
    have hrepl := List.isChain_eq_iff_eq_replicate.mp hsChain s.head!
      (List.head!_mem_head? hne)
    have hm : s.getLast hne ∈ s := List.getLast_mem hne
    have hm' : s.getLast hne ∈ List.replicate s.length s.head! := by
      rwa [← hrepl]
    exact (List.mem_replicate.mp hm').2
  have hbits : ∀ d ∈ c, d < 2 := by
    intro d hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    apply Nat.digits_lt_base (by decide : 1 < 2)
    rw [← List.flatten_splitBy (· == ·) (Nat.digits 2 n)]
    exact List.mem_flatten.mpr ⟨s, hs, List.head!_mem_self (hnblk s hs)⟩
  have halt : c.IsChain (· ≠ ·) := by
    change (bs.map List.head!).IsChain _
    rw [List.isChain_map]
    apply (List.isChain_getLast_head_splitBy (· == ·) (Nat.digits 2 n)).imp_of_mem_imp
    intro s t hs ht hsep
    obtain ⟨hs0, ht0, hne⟩ := hsep
    rw [hconst s hs hs0] at hne
    have hhead : t.head ht0 = t.head! :=
      (List.head!_of_head? (List.head?_eq_some_head ht0)).symm
    rw [hhead] at hne
    simpa using hne
  have hlast : c.getLast? = some 1 := by
    have hdl := Nat.getLast_digit_ne_zero 2 hn
    have hdlBound := Nat.digits_lt_base (by decide : 1 < 2) (List.getLast_mem hd)
    have hone : (Nat.digits 2 n).getLast hd = 1 := by omega
    have hbl : bs.getLast hb ∈ bs := List.getLast_mem hb
    change (bs.map List.head!).getLast? = some 1
    rw [List.getLast?_map, List.getLast?_eq_some_getLast hb]
    simp only [Option.map_some, Option.some.injEq]
    calc
      (bs.getLast hb).head! = (bs.getLast hb).getLast (hnblk _ hbl) :=
        (hconst _ hbl _).symm
      _ = (Nat.digits 2 n).getLast hd := List.getLast_getLast_splitBy _ hd
      _ = 1 := hone
  have hhead : c.head! = n % 2 := by
    have hc : c ≠ [] := by simpa [c] using hb
    calc
      c.head! = c.head hc := List.head!_of_head? (List.head?_eq_some_head hc)
      _ = (bs.head hb).head! := by simp [c]
      _ = (Nat.digits 2 n).head hd := by
        rw [List.head!_of_head? (List.head?_eq_some_head (hnblk _ (List.head_mem hb)))]
        exact List.head_head_splitBy _ hd
      _ = (Nat.digits 2 n).head! :=
        (List.head!_of_head? (List.head?_eq_some_head hd)).symm
      _ = n % 2 := Nat.head!_digits (by decide)
  have hv := alternating_value c hbits halt hlast
  have hlen : c.length = runs n := by simp [c, bs, runs]
  rw [hlen, hhead] at hv
  change 3 * Nat.ofDigits 2 c = 2 ^ (runs n + 1) + n % 2 - 2
  omega


end D5.S1.Digit.YanevRunCompressionClosedForm
