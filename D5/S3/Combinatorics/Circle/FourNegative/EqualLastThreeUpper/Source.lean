/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Source
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Source
   mirror-E: none(waiver:consumed-physical-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact paired source chains for the equal-last-three upper family. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

/-! Exact physical chains with their doubled terminal values. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue chain_values source_totals actual_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private last_double from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

private def rank (a s : ℕ) := a + 3 * s
private def amplitude (a s : ℕ) := 1 + 2 ^ a + 2 ^ (a + s) + 2 ^ (a + 2 * s)
private def delta (q : ℤ) := q ^ 2 + q + 1
private def heads (x q : ℤ) : Fin 4 → ℤ :=
  ![x * delta q + 1, x * (q ^ 2 + q) + q + 1, x * q ^ 2 + delta q, q ^ 3 + delta q]
private def newHeads (x q : ℤ) : Fin 4 → ℤ :=
  ![2 * heads x q 0, 2 * heads x q 1 - 1, 2 * heads x q 2 - 1 - q, 2 * heads x q 3 - delta q]
private def successor (F : Fin 4 → ℤ) : Fin 4 → ℤ := ![F 1, F 2, F 3, F 0]
private def newSuccessor (x q : ℤ) : Fin 4 → ℤ :=
  ![newHeads x q 1, newHeads x q 2, newHeads x q 3, heads x q 0]
private def start (s : ℕ) : Fin 4 → ℕ := ![0, s, 2 * s, 3 * s]
private def length (a s : ℕ) : Fin 4 → ℕ := ![s, s, s, a]
private def f (a s : ℕ) := oldValue a s s s
private def g (a s : ℕ) := newValue a s s s
private def N (a s : ℕ) := sourceMod a s s s

private theorem source (a s : ℕ) (hs : 2 ≤ s) (ha : s ≤ a) :
    let x : ℤ := 2 ^ a
    let q : ℤ := 2 ^ s
    (∀ r : Fin 4, 0 < heads x q r) ∧
    (∀ r : Fin 4, 0 < newHeads x q r) ∧
    (∀ r : Fin 4, ∀ i < length a s r - 1, 
      f a s (start s r + i) = (2:ℤ) ^ i * heads x q r ∧
      g a s (start s r + i) = (2:ℤ) ^ i * newHeads x q r) ∧
    (∀ r : Fin 4, 
      2 * f a s (start s r + length a s r - 1) = successor (heads x q) r - N a s ∧
      2 * g a s (start s r + length a s r - 1) = newSuccessor x q r - (2 * N a s + 1)) ∧
    g a s (rank a s) = heads x q 0 := by
  dsimp only
  have ha2 : 2 ≤ a := by omega
  obtain ⟨hb, hf, hg, he⟩ := chain_values a s s s ha2 hs hs hs
  have eb (r : Fin 4) : base a s s s r = heads ((2:ℤ) ^ a) (2 ^ s) r := by
    fin_cases r <;> dsimp [base, heads, delta] <;> ring
  have eg (r : Fin 4) : newBase a s s s r = newHeads ((2:ℤ) ^ a) (2 ^ s) r := by
    fin_cases r <;> dsimp [newBase, base, charge, newHeads, heads, delta] <;> ring
  have es (r : Fin 4) : chainStart s s s r = start s r := by
    fin_cases r <;> simp [chainStart, start] <;> omega
  have el (r : Fin 4) : chainLength a s s s r = length a s r := by
    fin_cases r <;> rfl
  have en (r : Fin 4) : nextBase a s s s r = successor (heads ((2:ℤ) ^ a) (2 ^ s)) r := by
    fin_cases r <;> simp [nextBase, successor, eb]
  have enn (r : Fin 4) : nextNewBase a s s s r = newSuccessor ((2:ℤ) ^ a) (2 ^ s) r := by
    fin_cases r <;> simp [nextNewBase, newSuccessor, eg, eb]
  have hr (r : Fin 4) : 1 ≤ length a s r := by fin_cases r <;> simp [length] <;> omega
  have rel (r : Fin 4) :
      (2:ℤ) ^ (chainLength a s s s r) * base a s s s r =
        sourceMod a s s s + nextBase a s s s r := by
    fin_cases r <;> dsimp [chainLength, base, sourceMod, nextBase] <;> ring
  have reln (r : Fin 4) :
      (2:ℤ) ^ (chainLength a s s s r) * newBase a s s s r =
        (2 * sourceMod a s s s + 1) + nextNewBase a s s s r := by
    fin_cases r <;> dsimp [chainLength, newBase, base, charge, sourceMod, nextNewBase] <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r; rw [←eb]; have := (hb r).1; omega
  · intro r
    have h := new_base_bounds a s s s ha2 hs hs hs r
    rw [eg] at h
    omega
  · intro r i hi
    have hh := hf r i (by rw [el]; omega)
    have hhn := hg r i (by rw [el]; omega)
    rw [el, ite_eq_left (by omega), eb, es] at hh
    rw [el, ite_eq_left (by omega), eg, es] at hhn
    exact ⟨hh, hhn⟩
  · intro r
    have hr' := hr r
    have hh := hf r (length a s r - 1) (by rw [el]; omega)
    have hhn := hg r (length a s r - 1) (by rw [el]; omega)
    rw [el, ite_eq_right (by omega), es] at hh hhn
    rw [show start s r + length a s r - 1 = start s r + (length a s r - 1) by omega]
    dsimp [f, g, N]
    rw [hh, hhn]
    constructor
    · rw [←en]
      exact last_double _ _ _ _ (by rw [el]; exact hr r) (rel r)
    · rw [←enn]
      exact last_double _ _ _ _ (by rw [el]; exact hr r) (reln r)
  · change newValue a s s s (rank a s) = _
    rw [show rank a s = size a s s s by dsimp [rank, size]; omega, he, eb]

private theorem source_numeric (a s : ℕ) :
    N a s = (2:ℤ) ^ a * ((2:ℤ) ^ s) ^ 3 - 1 ∧
    modulus (rank a s) = N a s ∧
    modulus (rank a s + 1) = 2 * N a s + 1 ∧
    (amplitude a s : ℤ) = heads ((2:ℤ) ^ a) (2 ^ s) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [N, sourceMod]; ring
  · dsimp [modulus, rank, N, sourceMod]
    rw [show a + 3 * s = a + s + s + s by omega]
    simp only [pow_add] <;> ring
  · dsimp [modulus, rank, N, sourceMod]
    rw [show a + 3 * s + 1 = a + s + s + s + 1 by omega]
    simp only [pow_add, pow_one] <;> ring
  · simp only [amplitude, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [show a + 2 * s = a + s + s by omega]
    dsimp [heads, delta]; simp only [pow_add] <;> ring

private theorem totals (a s : ℕ) (hs : 2 ≤ s) (ha : s ≤ a) :
    ((List.range (rank a s)).map (f a s)).sum = 0 ∧
    ((List.range (rank a s)).map (g a s)).sum = -heads ((2:ℤ) ^ a) (2 ^ s) 0 := by
  have ht := source_totals a s s s (by omega) hs hs hs
  have eb : base a s s s 0 = heads ((2:ℤ) ^ a) (2 ^ s) 0 := by
    dsimp [base, heads, delta]; ring
  simpa only [f, g, size, show a + s + s + s = rank a s by dsimp [rank]; omega, eb] using
    And.intro ht.1 ht.2.1

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
