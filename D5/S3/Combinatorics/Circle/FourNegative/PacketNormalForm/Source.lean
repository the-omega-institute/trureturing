/- GID: D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Source
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Source
   mirror-E: none(waiver:consumed-packet-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical signs and geometric weights for four independent gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open SourceWidth PeriodicShortening RunFirstEarTransport
open private source_table from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable

private def size (a b c d : ℕ) : ℕ := a + b + c + d
private def seed (a b c : ℕ) : ℕ := 1 + 2 ^ a + 2 ^ (a+b) + 2 ^ (a+b+c)
private def sourceMod (a b c d : ℕ) : ℤ :=
  (2 : ℤ)^a * 2^b * 2^c * 2^d - 1
private def base (a b c d : ℕ) : Fin 4 → ℤ :=
  ![2^a * 2^b * 2^c + (1 + 2^a + 2^a * 2^b),
    2^d * (1 + 2^a + 2^a * 2^b) + 1,
    2^d * (2^c * (1 + 2^a)) + 1 + 2^c,
    2^d * (2^b * 2^c) + 1 + 2^b + 2^b * 2^c]
private def charge (b c : ℕ) : Fin 4 → ℤ := ![0, 1, 1+2^c, 1+2^b+2^b*2^c]
private def newBase (a b c d : ℕ) (r : Fin 4) : ℤ := 2 * base a b c d r - charge b c r
private def chainLength (a b c d : ℕ) : Fin 4 → ℕ := ![d,c,b,a]
private def chainStart (b c d : ℕ) : Fin 4 → ℕ := ![0,d,d+c,d+c+b]
private def nextBase (a b c d : ℕ) : Fin 4 → ℤ :=
  ![base a b c d 1, base a b c d 2, base a b c d 3, base a b c d 0]
private def nextNewBase (a b c d : ℕ) : Fin 4 → ℤ :=
  ![newBase a b c d 1, newBase a b c d 2, newBase a b c d 3, base a b c d 0]
private def oldValue (a b c d i : ℕ) : ℤ :=
  centered (sourceMod a b c d) ((2 : ℤ)^i * base a b c d 0)
private def newValue (a b c d i : ℕ) : ℤ :=
  centered (2 * sourceMod a b c d + 1) ((2 : ℤ)^i * (2 * base a b c d 0))
private def negatives (a b c d : ℕ) : List ℕ :=
  [d-1,d+c-1,d+c+b-1,size a b c d-1]

private theorem actual_values (a b c d : ℕ) :
    (∀ i : Fin (size a b c d), actualSource (size a b c d) (seed a b c) i =
      oldValue a b c d i.val) ∧
    (∀ i : Fin (size a b c d + 1),
      actualSource (size a b c d + 1) (2 * seed a b c) i = newValue a b c d i.val) := by
  have hN : modulus (size a b c d) = sourceMod a b c d := by
    dsimp [modulus, size, sourceMod]; ring
  have hN' : modulus (size a b c d + 1) = 2 * sourceMod a b c d + 1 := by
    dsimp [modulus, size, sourceMod]; ring
  have hA : (seed a b c : ℤ) = base a b c d 0 := by
    simp only [seed, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [base]; ring
  constructor
  · intro i; simp only [actualSource, hN, hA, oldValue]
  · intro i; simp only [actualSource, hN', Nat.cast_mul, Nat.cast_ofNat, hA, newValue]

private theorem chain_values (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    (∀ r : Fin 4, 1 ≤ base a b c d r ∧ base a b c d r < sourceMod a b c d) ∧
    (∀ r : Fin 4, ∀ i < chainLength a b c d r,
      oldValue a b c d (chainStart b c d r + i) =
        if i+1 < chainLength a b c d r then (2 : ℤ)^i * base a b c d r
        else -(sourceMod a b c d - nextBase a b c d r) / 2) ∧
    (∀ r : Fin 4, ∀ i < chainLength a b c d r,
      newValue a b c d (chainStart b c d r + i) =
        if i+1 < chainLength a b c d r then (2 : ℤ)^i * newBase a b c d r
        else -((2 * sourceMod a b c d + 1) - nextNewBase a b c d r) / 2) ∧
    newValue a b c d (size a b c d) = base a b c d 0 := by
  obtain ⟨hA,hB,hL,hM,hu,hv,hw,hx,hgu,hgv,hgw,hgx,he⟩ :=
    source_table a b c d ha hb hc hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; fin_cases r
    · simpa [base, sourceMod] using hA
    · simpa [base, sourceMod] using hB
    · simpa [base, sourceMod] using hL
    · simpa [base, sourceMod] using hM
  · intro r; fin_cases r
    · simpa [chainLength, chainStart, oldValue, sourceMod, base, nextBase] using hu
    · simpa [chainLength, chainStart, oldValue, sourceMod, base, nextBase] using hv
    · simpa [chainLength, chainStart, oldValue, sourceMod, base, nextBase] using hw
    · simpa [chainLength, chainStart, oldValue, sourceMod, base, nextBase] using hx
  · intro r; fin_cases r
    · simpa [chainLength, chainStart, newValue, sourceMod, base, nextNewBase, newBase, charge] using hgu
    · simpa [chainLength, chainStart, newValue, sourceMod, base, nextNewBase, newBase, charge,
        sub_add_eq_sub_sub] using hgv
    · simpa [chainLength, chainStart, newValue, sourceMod, base, nextNewBase, newBase, charge,
        sub_add_eq_sub_sub] using hgw
    · simpa [chainLength, chainStart, newValue, sourceMod, base, nextNewBase, newBase, charge,
        sub_add_eq_sub_sub] using hgx
  · simpa [newValue, sourceMod, base, size, show d+c+b+a=a+b+c+d by omega] using he

private theorem new_base_bounds (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    ∀ r : Fin 4, 1 ≤ newBase a b c d r ∧
      newBase a b c d r < 2 * sourceMod a b c d + 1 := by
  have h := (chain_values a b c d ha hb hc hd).1
  have hp (n : ℕ) : (0 : ℤ) < 2^n := by positivity
  intro r
  have hF := h r
  have hη : 0 ≤ charge b c r := by fin_cases r <;> simp [charge] <;> positivity
  have hD : 0 < base a b c d r - charge b c r := by
    fin_cases r <;> dsimp [base, charge]
    · positivity
    · ring_nf; positivity
    · ring_nf; positivity
    · ring_nf; positivity
  dsimp [newBase]
  constructor <;> omega

private theorem chain_signs (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (r : Fin 4) (i : ℕ) (hi : i < chainLength a b c d r) :
    if i+1 < chainLength a b c d r then
      0 < oldValue a b c d (chainStart b c d r + i) ∧
      0 < newValue a b c d (chainStart b c d r + i)
    else oldValue a b c d (chainStart b c d r + i) < 0 ∧
      newValue a b c d (chainStart b c d r + i) < 0 := by
  obtain ⟨hF,hf,hg,_⟩ := chain_values a b c d ha hb hc hd
  have hE := new_base_bounds a b c d ha hb hc hd
  rw [hf r i hi, hg r i hi]
  split_ifs with hp
  · exact ⟨mul_pos (by positivity) (by have := (hF r).1; omega),
      mul_pos (by positivity) (by have := (hE r).1; omega)⟩
  · have hnext : nextBase a b c d r < sourceMod a b c d := by
      fin_cases r <;> simpa [nextBase] using (hF _).2
    have hnext' : nextNewBase a b c d r < 2 * sourceMod a b c d + 1 := by
      fin_cases r
      · simpa [nextNewBase] using (hE 1).2
      · simpa [nextNewBase] using (hE 2).2
      · simpa [nextNewBase] using (hE 3).2
      · have hh := hF 0
        have hN : 0 < sourceMod a b c d := lt_of_lt_of_le (by omega) hh.2.le
        simp only [nextNewBase, Matrix.cons_val_succ, Matrix.cons_val_zero]
        omega
    constructor <;> omega

private theorem source_signs (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (i : ℕ) (hi : i < size a b c d) :
    if i ∈ negatives a b c d then oldValue a b c d i < 0 ∧ newValue a b c d i < 0
    else 0 < oldValue a b c d i ∧ 0 < newValue a b c d i := by
  by_cases h0 : i < d
  · have h := chain_signs a b c d ha hb hc hd 0 i (by simpa [chainLength])
    simp only [chainLength, chainStart, Matrix.cons_val_zero, zero_add] at h
    have he : i ∈ negatives a b c d ↔ ¬ i+1 < d := by
      simp only [negatives, List.mem_cons, List.mem_singleton, size]
      omega
    by_cases hp : i+1 < d <;> simpa [he, hp] using h
  · by_cases h1 : i < d+c
    · have h := chain_signs a b c d ha hb hc hd 1 (i-d) (by simp [chainLength]; omega)
      simp only [chainLength, chainStart, Matrix.cons_val_succ, Matrix.cons_val_zero] at h
      rw [show d + (i-d) = i by omega] at h
      have he : i ∈ negatives a b c d ↔ ¬ i-d+1 < c := by
        simp only [negatives, List.mem_cons, List.mem_singleton, size]
        omega
      by_cases hp : i-d+1 < c <;> simpa [he, hp] using h
    · by_cases h2 : i < d+c+b
      · have h := chain_signs a b c d ha hb hc hd 2 (i-(d+c))
          (by simp [chainLength]; omega)
        simp only [chainLength, chainStart, Matrix.cons_val_succ, Matrix.cons_val_zero] at h
        rw [show d+c+(i-(d+c))=i by omega] at h
        have he : i ∈ negatives a b c d ↔ ¬ i-(d+c)+1 < b := by
          simp only [negatives, List.mem_cons, List.mem_singleton, size]
          omega
        by_cases hp : i-(d+c)+1 < b <;> simpa [he, hp] using h
      · have h := chain_signs a b c d ha hb hc hd 3 (i-(d+c+b))
          (by simp [chainLength, size] at *; omega)
        simp only [chainLength, chainStart, Matrix.cons_val_succ, Matrix.cons_val_zero] at h
        rw [show d+c+b+(i-(d+c+b))=i by dsimp [size] at hi; omega] at h
        have he : i ∈ negatives a b c d ↔ ¬ i-(d+c+b)+1 < a := by
          simp only [negatives, List.mem_cons, List.mem_singleton, size]
          dsimp [size] at hi
          omega
        by_cases hp : i-(d+c+b)+1 < a <;> simpa [he, hp] using h

private theorem negatives_nodup (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    (negatives a b c d).Nodup := by
  simp only [negatives, List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, not_false_eq_true, and_true, size]
  omega

private theorem source_totals (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    ((List.range (size a b c d)).map (oldValue a b c d)).sum = 0 ∧
    ((List.range (size a b c d)).map (newValue a b c d)).sum = -base a b c d 0 ∧
    newValue a b c d (size a b c d) = base a b c d 0 := by
  have hN : modulus (size a b c d) = sourceMod a b c d := by
    dsimp [modulus, size, sourceMod]; ring
  have hN' : modulus (size a b c d + 1) = 2 * sourceMod a b c d + 1 := by
    dsimp [modulus, size, sourceMod]; ring
  have hA : (seed a b c : ℤ) = base a b c d 0 := by
    simp only [seed, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [base]; ring
  have hf := ThreeNegativeEqualOuterSourceBridge.source_zero
    (size a b c d) (seed a b c) (by dsimp [size]; omega)
  have hg := ThreeNegativeEqualOuterSourceBridge.source_zero
    (size a b c d + 1) (2 * seed a b c) (by dsimp [size]; omega)
  simp only [hN, hA, ← oldValue] at hf
  simp only [hN', Nat.cast_mul, Nat.cast_ofNat, hA, ← newValue] at hg
  have he := (chain_values a b c d ha hb hc hd).2.2.2
  rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton, he] at hg
  exact ⟨hf, by omega, he⟩

end D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
