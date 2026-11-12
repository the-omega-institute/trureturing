/- GID: D5/S1/Words/Complexity/LyndonFactorTransport
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonFactorTransport
   mirror-E: none(waiver:research-return-assignment-A)
   anchors: []
   utility: none
   digest: Definition-linked factor domains, standard cuts, and actual block transport. -/

import D5.S1.Words.Complexity.LyndonFactorChristoffelMinimumRefutation
import D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization

/-! Assignment-A foundations for actual finite Lyndon factors, standard cuts,
and the concrete block/elementary word carriers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Assignment-A foundations.  The retained 506 module owns the finite
certificate; this file exposes its actual word domain and the reusable proper
cut/block carriers.  The universal block factor-set identity remains open
until the internal-run suffix cases are supplied. -/

namespace D5.S1.Words.Complexity.LyndonFactorTransport

open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.LyndonBrackets.LyndonStandardFactorization
open D5.S1.Words.Complexity.LyndonFactorChristoffelMinimumRefutation

/-! ## Retained finite-index factors: exact domain and nonemptiness -/

@[simp] theorem factor_eq_list_slice {σ n : ℕ} (w : Fin n → Fin σ) (i l : ℕ) :
    factor w i l = (((List.finRange n).map w).drop i).take l := rfl

theorem factor_nonempty {σ n : ℕ} (w : Fin n → Fin σ) {i l : ℕ}
    (hl : 0 < l) (hbound : i + l ≤ n) : factor w i l ≠ [] := by
  intro hzero
  have hlen := congrArg List.length hzero
  simp only [factor, List.length_take, List.length_drop, List.length_map,
    List.length_finRange, List.length_nil] at hlen
  rw [Nat.min_eq_left (by omega)] at hlen
  omega

theorem lyndonOccurrences_mem_iff {σ n : ℕ} (w : Fin n → Fin σ) (i l : ℕ) :
    (i, l) ∈ lyndonOccurrences w ↔
      i + l ≤ n ∧ i < n ∧ 1 ≤ l ∧ l < n + 1 ∧ IsLyndon (factor w i l) := by
  simp only [lyndonOccurrences, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨hi, hl⟩, hpos, hbound, hL⟩
    exact ⟨hbound, hi, hpos, hl, hL⟩
  · rintro ⟨hbound, hi, hpos, hl, hL⟩
    exact ⟨⟨hi, hl⟩, hpos, hbound, hL⟩

theorem factor_domain_exact {σ n : ℕ} (w : Fin n → Fin σ) {i l : ℕ}
    (hl : 0 < l) (hbound : i + l ≤ n) :
    factor w i l ≠ [] ∧ i < n ∧ l < n + 1 := by
  exact ⟨factor_nonempty w hl hbound, by omega, by omega⟩

/-! ## Actual proper cut and right witness -/

theorem standard_factorization_actual {A : Type*} [LinearOrder A]
    (w : List A) (hw : 2 ≤ w.length) (hL : IsLyndon w) :
    IsLyndon (standardLeft w hw) ∧
      IsLyndon (standardRight w hw) ∧
      standardLeft w hw ++ standardRight w hw = w := by
  have hcut := @Nat.find_spec _ (Classical.decPred _)
    (exists_lyndon_suffix_cut w hw)
  have hright : IsLyndon (standardRight w hw) := by
    simpa [standardRight, standardCut] using hcut.2.2
  have hsplit : standardLeft w hw ++ standardRight w hw = w := by
    simpa [standardLeft, standardRight] using
      List.take_append_drop (standardCut w hw) w
  exact ⟨isLyndon_standardLeft w hw hL, hright, hsplit⟩

theorem standard_right_is_proper {A : Type*} [LinearOrder A]
    (w : List A) (hw : 2 ≤ w.length) :
    (standardRight w hw).length < w.length := by
  have hcut := @Nat.find_spec _ (Classical.decPred _)
    (exists_lyndon_suffix_cut w hw)
  simp only [standardRight, List.length_drop]
  exact Nat.sub_lt (by omega) hcut.1

/-! ## Concrete block, elementary, and composite transport -/

def blockLetter (r s : ℕ) (x : Fin 2) : List (Fin 2) :=
  List.replicate r 0 ++ List.replicate (s + if x = 0 then 0 else 1) 1

def mapWord (f : Fin 2 → List (Fin 2)) (w : List (Fin 2)) : List (Fin 2) :=
  w.flatMap f

@[simp] theorem mapWord_nil (f : Fin 2 → List (Fin 2)) : mapWord f [] = [] := rfl

@[simp] theorem mapWord_cons (f : Fin 2 → List (Fin 2)) (a : Fin 2)
    (w : List (Fin 2)) : mapWord f (a :: w) = f a ++ mapWord f w := rfl

theorem blockLetter_zero (r s : ℕ) :
    blockLetter r s 0 = List.replicate r 0 ++ List.replicate s 1 := by
  simp [blockLetter]

theorem blockLetter_one (r s : ℕ) :
    blockLetter r s 1 = List.replicate r 0 ++ List.replicate (s + 1) 1 := by
  simp [blockLetter]

theorem blockLetter_length (r s : ℕ) (x : Fin 2) :
    (blockLetter r s x).length = r + s + if x = 0 then 0 else 1 := by
  simp [blockLetter, Nat.add_assoc]

def elementaryLeft (x : Fin 2) : List (Fin 2) := if x = 0 then [0] else [0, 1]
def elementaryRight (x : Fin 2) : List (Fin 2) := if x = 0 then [0, 1] else [1]

def compositeH : Fin 2 → List (Fin 2) :=
  fun x => mapWord elementaryLeft (mapWord elementaryRight
    (mapWord elementaryLeft (mapWord elementaryRight (blockLetter 2 1 x))))

def Uword : List (Fin 2) := [0, 0, 1, 0, 0, 1, 0, 1]
def Vword : List (Fin 2) := [0, 0, 1, 0, 1]
def Aword : List (Fin 2) := Uword ++ Uword ++ Vword
def Bword : List (Fin 2) := Uword ++ Uword ++ Vword ++ Vword

theorem compositeH_zero : compositeH 0 = Aword := by decide

theorem compositeH_one : compositeH 1 = Bword := by decide

theorem compositeH_length (x : Fin 2) :
    (compositeH x).length = if x = 0 then 21 else 26 := by
  fin_cases x <;> simp [compositeH, mapWord, blockLetter, elementaryLeft,
    elementaryRight, Aword, Bword, Uword, Vword]

end D5.S1.Words.Complexity.LyndonFactorTransport
