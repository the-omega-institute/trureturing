/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCodeCoordinateClass
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCodeCoordinateClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Count equal-evaluation coordinate classes in a binary two-weight code. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! A binary code with only middle-weight nonconstant words has uniform coordinate classes. -/

open scoped BigOperators

namespace BinaryCode

private theorem zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx := ZMod.val_lt x
  have hv : x.val = 0 ∨ x.val = 1 := by omega
  rcases hv with h | h
  · exact Or.inl ((ZMod.val_eq_zero x).mp h)
  · exact Or.inr ((ZMod.val_eq_one (by decide) x).mp h)

private theorem ne_zero_iff_one (x : ZMod 2) : x ≠ 0 ↔ x = 1 := by
  rcases zero_or_one x with h | h <;> simp [h]

/-- Translation by a word taking value one at `b` pairs the two fibers. -/
private theorem twice_card_fibers {ι : Type*} (S : Finset (ι → ZMod 2))
    (b : ι) (d : ι → ZMod 2) (hd : d b = 1)
    (htrans : ∀ c ∈ S, c + d ∈ S) :
    2 * (S.filter (fun c => c b = 0)).card = S.card ∧
      2 * (S.filter (fun c => c b = 1)).card = S.card := by
  classical
  have hinv (c : ι → ZMod 2) : c + d + d = c := by
    funext i
    change (c i + d i) + d i = c i
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hpair : (S.filter (fun c => c b = 0)).card =
      (S.filter (fun c => c b = 1)).card := by
    refine Finset.card_bij' (fun c _ => c + d) (fun c _ => c + d) ?_ ?_ ?_ ?_
    · intro c hc
      rcases Finset.mem_filter.mp hc with ⟨hcS, hc0⟩
      refine Finset.mem_filter.mpr ⟨htrans c hcS, ?_⟩
      change c b + d b = 1
      rw [hc0, hd, zero_add]
    · intro c hc
      rcases Finset.mem_filter.mp hc with ⟨hcS, hc1⟩
      refine Finset.mem_filter.mpr ⟨htrans c hcS, ?_⟩
      change c b + d b = 0
      rw [hc1, hd, CharTwo.add_self_eq_zero]
    · intro c _
      exact hinv c
    · intro c _
      exact hinv c
  have hcompl : (S.filter (fun c => ¬ c b = 0)) =
      S.filter (fun c => c b = 1) := by
    ext c
    simp only [Finset.mem_filter, ne_zero_iff_one]
  have hpartition := Finset.card_filter_add_card_filter_not (s := S) (fun c => c b = 0)
  rw [hcompl] at hpartition
  exact ⟨by omega, by omega⟩

/-- In a binary additive code of length `2 * n` containing the all-one word,
where every word other than zero and one has weight `n`, each class of
coordinates agreeing on the entire code has cardinality `4 * n / |K|`.
The multiplicative formulation gives the exact cardinality without division. -/
theorem card_mul_coordinateClass_card {ι : Type*} [Fintype ι]
    (K : AddSubgroup (ι → ZMod 2)) (n : ℕ) (hlen : Fintype.card ι = 2 * n)
    (hone : (1 : ι → ZMod 2) ∈ K)
    (hweight : ∀ c ∈ K, c ≠ 0 → c ≠ 1 → Nat.card {b : ι // c b = 1} = n)
    (a : ι) :
    Nat.card K * Nat.card {b : ι // ∀ c ∈ K, c b = c a} = 4 * n := by
  classical
  let S : Finset (ι → ZMod 2) := Finset.univ.filter (fun c => c ∈ K)
  let L := S.filter (fun c => c a = 0)
  let C : Finset ι := Finset.univ.filter (fun b => ∀ c ∈ K, c b = c a)
  have memS (c : ι → ZMod 2) : c ∈ S ↔ c ∈ K := by simp [S]
  have memL (c : ι → ZMod 2) : c ∈ L ↔ c ∈ K ∧ c a = 0 := by
    simp [L, memS]
  have memC (b : ι) : b ∈ C ↔ ∀ c ∈ K, c b = c a := by simp [C]
  have cardS : Nat.card K = S.card := Nat.subtype_card S memS
  have cardC : Nat.card {b : ι // ∀ c ∈ K, c b = c a} = C.card :=
    Nat.subtype_card C memC
  have hhalf : 2 * L.card = S.card := by
    exact (twice_card_fibers S a 1 (by simp) (fun c hc =>
      (memS _).mpr (K.add_mem ((memS c).mp hc) hone))).1
  have hzero : (0 : ι → ZMod 2) ∈ L := (memL _).mpr ⟨K.zero_mem, by simp⟩
  have hadd (c d : ι → ZMod 2) (hc : c ∈ L) (hd : d ∈ L) : c + d ∈ L := by
    rcases (memL c).mp hc with ⟨hcK, hc0⟩
    rcases (memL d).mp hd with ⟨hdK, hd0⟩
    exact (memL _).mpr ⟨K.add_mem hcK hdK, by simp [Pi.add_apply, hc0, hd0]⟩

  -- Incidences at a coordinate in the class vanish.
  let F (b : ι) := (L.filter (fun c => c b = 1)).card
  have hvanish (b : ι) (hb : b ∈ C) : F b = 0 := by
    apply Finset.card_filter_eq_zero_iff.mpr
    intro c hc
    rcases (memL c).mp hc with ⟨hcK, hc0⟩
    have hz : c b = 0 := ((memC b).mp hb c hcK).trans hc0
    simp [hz]

  -- Outside the class there is a word in the zero slice taking value one.
  have hvote (b : ι) (hb : b ∉ C) : ∃ d ∈ L, d b = 1 := by
    have hn : ¬ ∀ c ∈ K, c b = c a := fun h => hb ((memC b).mpr h)
    push_neg at hn
    obtain ⟨c, hc, hne⟩ := hn
    rcases zero_or_one (c a) with ha | ha
    · refine ⟨c, (memL c).mpr ⟨hc, ha⟩, (ne_zero_iff_one (c b)).mp ?_⟩
      exact fun hz => hne (hz.trans ha.symm)
    · refine ⟨c + 1, (memL _).mpr ⟨K.add_mem hc hone, ?_⟩, ?_⟩
      · change c a + 1 = 0
        rw [ha, CharTwo.add_self_eq_zero]
      · have hb0 : c b = 0 := by
          rcases zero_or_one (c b) with h | h
          · exact h
          · exact (hne (h.trans ha.symm)).elim
        change c b + 1 = 1
        simp [hb0]
  have hnonclass (b : ι) (hb : b ∉ C) : 2 * F b = L.card := by
    obtain ⟨d, hd, hd1⟩ := hvote b hb
    exact (twice_card_fibers L b d hd1 (fun c hc => hadd c d hc hd)).2

  -- Count incidences by coordinates, using twice each fiber cardinality.
  let D : Finset ι := Finset.univ.filter (fun b => b ∉ C)
  have hpartition : D.card + C.card = 2 * n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun b => b ∈ C)
    have he : (Finset.univ.filter (fun b => b ∈ C)) = C := by
      ext b
      simp
    rw [he, Finset.card_univ, hlen] at h
    change C.card + D.card = 2 * n at h
    omega
  have hcolumns : 2 * (∑ b : ι, F b) = D.card * L.card := by
    rw [Finset.mul_sum]
    calc
      (∑ b : ι, 2 * F b) = ∑ b : ι, if b ∉ C then L.card else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : b ∈ C
        · simp [hb, hvanish b hb]
        · simpa [hb] using hnonclass b hb
      _ = ∑ b ∈ D, L.card := by
        change _ = ∑ b ∈ (Finset.univ.filter (fun b : ι => b ∉ C)), L.card
        rw [Finset.sum_filter]
      _ = D.card * L.card := Finset.sum_const_nat (fun _ _ => rfl)

  -- The same incidences counted by words: all nonzero members have weight n.
  let W (c : ι → ZMod 2) := (Finset.univ.filter (fun b => c b = 1)).card
  have hcounts : (∑ c ∈ L, W c) = ∑ b : ι, F b := by
    simp only [W, F, Finset.card_filter]
    exact Finset.sum_comm
  have hweightL (c : ι → ZMod 2) (hc : c ∈ L.erase 0) : W c = n := by
    rcases Finset.mem_erase.mp hc with ⟨hc0, hcL⟩
    rcases (memL c).mp hcL with ⟨hcK, hca⟩
    have hc1 : c ≠ 1 := by
      intro h
      rw [h] at hca
      change (1 : ZMod 2) = 0 at hca
      exact one_ne_zero hca
    have hW : Nat.card {b : ι // c b = 1} = W c :=
      Nat.subtype_card (Finset.univ.filter (fun b : ι => c b = 1)) (fun b => by simp)
    exact hW.symm.trans (hweight c hcK hc0 hc1)
  have hrows : (∑ c ∈ L, W c) + n = L.card * n := by
    have hW0 : W 0 = 0 := by simp [W]
    have he : (L.erase 0).card + 1 = L.card := by
      rw [Finset.card_erase_of_mem hzero]
      exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨0, hzero⟩)
    calc
      (∑ c ∈ L, W c) + n = (∑ c ∈ L.erase 0, W c) + n := by
        rw [← Finset.sum_erase_add L W hzero, hW0, add_zero]
      _ = (L.erase 0).card * n + n := by
        rw [Finset.sum_const_nat hweightL]
      _ = ((L.erase 0).card + 1) * n := by ring
      _ = L.card * n := by rw [he]

  have hcount : D.card * L.card + 2 * n = (2 * n) * L.card := by
    calc
      D.card * L.card + 2 * n = 2 * (∑ b : ι, F b) + 2 * n := by rw [hcolumns]
      _ = 2 * ((∑ b : ι, F b) + n) := by ring
      _ = 2 * (L.card * n) := by rw [← hcounts, hrows]
      _ = (2 * n) * L.card := by ring
  have hsplit : D.card * L.card + C.card * L.card = (2 * n) * L.card := by
    rw [← Nat.add_mul, hpartition]
  have hclass : L.card * C.card = 2 * n := by
    have h : D.card * L.card + C.card * L.card = D.card * L.card + 2 * n :=
      hsplit.trans hcount.symm
    exact (Nat.mul_comm _ _).trans (Nat.add_left_cancel h)
  rw [cardS, cardC, ← hhalf, Nat.mul_assoc, hclass] <;> omega

end BinaryCode
