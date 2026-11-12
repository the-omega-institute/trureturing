/- GID: D5/S3/Combinatorics/Graph/Roommates/OpenCertificates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/OpenCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Perm]
   utility: none
   digest: Integer-target-injective certificates restrict to intervals and count profiles once. -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace D5.S3.Combinatorics.Graph.Roommates.OpenCertificates

abbrev Ranking := Equiv.Perm (Fin 4)
abbrev Word (m : ℕ) := Fin m → Ranking

/-- Rank of an assigned signed offset; zero is single and has rank four. -/
def offsetRank (r : Ranking) (d : ℤ) : ℕ :=
  if d = 1 then (r 0).val else if d = 2 then (r 1).val
  else if d = -1 then (r 2).val else if d = -2 then (r 3).val else 4

/-- Requests retain their actual ranks when the partner lies outside the interval.
Target injectivity includes those exterior integer targets. -/
structure Certificate {m : ℕ} (w : Word m) (d : Fin m → ℤ) : Prop where
  bounded : ∀ i, -2 ≤ d i ∧ d i ≤ 2
  reciprocal : ∀ i j, d i ≠ 0 → (i.val : ℤ) + d i = j.val → d j = -d i
  target_injective : ∀ i j, d i ≠ 0 → d j ≠ 0 →
    (i.val : ℤ) + d i = (j.val : ℤ) + d j → i = j
  nonblocking : ∀ i j, i.val < j.val → j.val ≤ i.val + 2 →
    d i = (j.val : ℤ) - i.val ∨
    offsetRank (w i) (d i) < offsetRank (w i) ((j.val : ℤ) - i.val) ∨
    offsetRank (w j) (d j) < offsetRank (w j) ((i.val : ℤ) - j.val)

/-- This subtype counts words, with an existential certificate, once per word. -/
def CertifiedWord (m : ℕ) := {w : Word m // ∃ d, Certificate w d}

instance (m : ℕ) : Fintype (CertifiedWord m) := by
  classical
  unfold CertifiedWord
  infer_instance

/-- Number of certified profiles, not the number of certificates. -/
def count (m : ℕ) : ℕ := Fintype.card (CertifiedWord m)

/-- Translate the interval beginning at s to zero-based local coordinates. -/
def intervalIndex {n m : ℕ} (s : ℕ) (h : s + m ≤ n) (i : Fin m) : Fin n :=
  ⟨s + i.val, by omega⟩

/-- Restriction preserves exterior targets as well as internal matching and stability. -/
theorem certificate_restrict {n m : ℕ} {w : Word n} {d : Fin n → ℤ}
    (hc : Certificate w d) (s : ℕ) (h : s + m ≤ n) :
    Certificate (fun i => w (intervalIndex s h i)) (fun i => d (intervalIndex s h i)) := by
  constructor
  · intro i
    exact hc.bounded _
  · intro i j hdi he
    apply hc.reciprocal (intervalIndex s h i) (intervalIndex s h j) hdi
    simp only [intervalIndex, Fin.val_mk, Nat.cast_add]
    omega
  · intro i j hdi hdj he
    have ht : (↑(intervalIndex s h i).val : ℤ) + d (intervalIndex s h i) =
        ↑(intervalIndex s h j).val + d (intervalIndex s h j) := by
      simp only [intervalIndex, Fin.val_mk, Nat.cast_add]
      omega
    have hi := congrArg Fin.val (hc.target_injective _ _ hdi hdj ht)
    apply Fin.ext
    simp only [intervalIndex, Fin.val_mk] at hi
    omega
  · intro i j hij hdist
    have hi : (intervalIndex s h i).val < (intervalIndex s h j).val := by
      simp only [intervalIndex, Fin.val_mk]
      omega
    have hj : (intervalIndex s h j).val ≤ (intervalIndex s h i).val + 2 := by
      simp only [intervalIndex, Fin.val_mk]
      omega
    have hh := hc.nonblocking _ _ hi hj
    have he₁ : ((intervalIndex s h j).val : ℤ) - (intervalIndex s h i).val =
        (j.val : ℤ) - i.val := by simp [intervalIndex]
    have he₂ : ((intervalIndex s h i).val : ℤ) - (intervalIndex s h j).val =
        (i.val : ℤ) - j.val := by simp [intervalIndex]
    simpa only [he₁, he₂] using hh

/-- Word restriction does not choose or count matching witnesses. -/
def restrict {n m : ℕ} (s : ℕ) (h : s + m ≤ n) (w : CertifiedWord n) : CertifiedWord m := by
  refine ⟨fun i => w.val (intervalIndex s h i), ?_⟩
  obtain ⟨d, hd⟩ := w.property
  exact ⟨fun i => d (intervalIndex s h i), certificate_restrict hd s h⟩

def split (m k : ℕ) (w : CertifiedWord (m + k)) : CertifiedWord m × CertifiedWord k :=
  (restrict 0 (by omega) w, restrict m (by omega) w)

private theorem split_injective (m k : ℕ) : Function.Injective (split m k) := by
  intro x y h
  apply Subtype.ext
  funext i
  by_cases hi : i.val < m
  · have he := congrArg (fun p : CertifiedWord m × CertifiedWord k => p.1.val ⟨i.val, hi⟩) h
    simpa only [split, restrict, intervalIndex, Nat.zero_add] using he
  · have he := congrArg (fun p : CertifiedWord m × CertifiedWord k =>
      p.2.val ⟨i.val - m, by omega⟩) h
    simpa only [split, restrict, intervalIndex, Nat.add_sub_of_le (by omega : m ≤ i.val)] using he

/-- Submultiplicativity is an injection on distinct preference profiles. -/
theorem count_submultiplicative (m k : ℕ) : count (m + k) ≤ count m * count k := by
  have h := Fintype.card_le_of_injective (split m k) (split_injective m k)
  simpa only [Fintype.card_prod] using h

#print axioms certificate_restrict
#print axioms count_submultiplicative

end D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
