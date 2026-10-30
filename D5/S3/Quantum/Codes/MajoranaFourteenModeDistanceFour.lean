/- GID: D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Parity Majorana codes with a logical qubit need sixteen modes for distance four. -/

import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
Hastings, arXiv:1703.00612v1, `c.tex` lines 86–117 and 272–273.
The source identifies stabilizers with self-orthogonal binary subspaces, requires
the all-ones parity stabilizer, and defines distance by the least weight in the
commutant outside the stabilizer subspace. Preregistration: issue #23984.
The inequality `2 * finrank C < n` is the source's positive logical-qubit count.
Admission basis: open-problem-resolution. This file is the mathematical source;
publication and freezing belong to the caller.
-/

open scoped BigOperators
open Matrix

noncomputable section

namespace D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour

/-- The weight of the Majorana product is the Hamming weight of its bit string
(Hastings, source line 113). This directly reuses Mathlib's Hamming norm. -/
def weight {ι : Type*} [Fintype ι] (v : ι → ZMod 2) : ℕ := hammingNorm v

/-- Stabilizer subspaces are pairwise orthogonal, including each vector with
itself (Hastings, source lines 94–97). -/
def IsSelfOrthogonal {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) : Prop :=
  ∀ x ∈ c, ∀ y ∈ c, x ⬝ᵥ y = 0

/-- Products commuting with every stabilizer (source lines 107–108).
Mathlib's orthogonal complement uses the other dot-product argument, which is
equal by commutativity over the binary field. -/
def commutant {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  (dotProductBilin (ZMod 2) (ZMod 2)).orthogonal c

/-- Hastings's belief for at most fourteen modes: under the parity convention
(lines 115–117), a positive logical-qubit count (lines 99–104) forces a logical
operator outside the stabilizers of weight below four (lines 107–113).
The fourteen-mode assertion is the belief at source lines 272–273. -/
def claim : Prop :=
  ∀ n : ℕ, n ≤ 14 → ∀ c : Submodule (ZMod 2) (Fin n → ZMod 2),
    IsSelfOrthogonal c → (fun _ => 1) ∈ c →
    2 * Module.finrank (ZMod 2) c < n →
    ∃ v ∈ commutant c, v ∉ c ∧ weight v < 4

private lemma mem_commutant {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (v : ι → ZMod 2) :
    v ∈ commutant c ↔ ∀ x ∈ c, v ⬝ᵥ x = 0 := by
  sorry

private lemma binary_value (x : ZMod 2) : x = 0 ∨ x = 1 := by
  sorry

private lemma parity_card {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) : Even (Fintype.card ι) := by
  sorry

private lemma pair_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) : weight (Pi.single i 1 + Pi.single j (1 : ZMod 2)) = 2 := by
  sorry

private lemma pair_agreement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (i j : ι) (hij : i ≠ j) (hp : Pi.single i 1 + Pi.single j 1 ∈ c) :
    ∀ x ∈ c, x i = x j := by
  sorry

private lemma remove_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (i j : ι) (hij : i ≠ j)
    (hv : Pi.single i 1 + Pi.single j 1 ∈ c) :
    ∃ d : Submodule (ZMod 2) ({a : ι // a ≠ i ∧ a ≠ j} → ZMod 2),
      IsSelfOrthogonal d ∧ (fun _ => 1) ∈ d ∧
      Module.finrank (ZMod 2) d + 1 = Module.finrank (ZMod 2) c ∧
      Fintype.card {a : ι // a ≠ i ∧ a ≠ j} + 2 = Fintype.card ι ∧
      (∀ v ∈ commutant d, v ∉ d → weight v < 4 →
        ∃ w ∈ commutant c, w ∉ c ∧ weight w < 4) := by
  sorry

private lemma column_encoding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hp : (fun _ => 1) ∈ c)
    (hn : 0 < Fintype.card ι)
    (hs : ∀ i j : ι, i ≠ j → Pi.single i 1 + Pi.single j 1 ∉ commutant c) :
    ∃ k : ℕ, k + 1 = Module.finrank (ZMod 2) c ∧
      ∃ r : Fin k → c, Function.Injective (fun i : ι => fun a : Fin k => (r a).val i) := by
  sorry

private lemma column_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (k : ℕ) (r : Fin k → c)
    (hi : Function.Injective (fun i : ι => fun a : Fin k => (r a).val i)) :
    let s := Finset.univ.image (fun i : ι => fun a : Fin k => (r a).val i)
    s.card = Fintype.card ι ∧
      ∀ a : Finset (Fin k), a.card ≤ 2 →
        ∑ x : Fin k → ZMod 2, (if x ∈ s then (1 : ZMod 2) else 0) *
          ∏ b ∈ a, x b = 0 := by
  sorry

private lemma boolean_expansion (k : ℕ) (f : (Fin k → ZMod 2) → ZMod 2)
    (x : Fin k → ZMod 2) :
    f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∑ y : Fin k → ZMod 2, f y * ∏ i ∈ Finset.univ \ a, y i) *
        ∏ i ∈ a, (x i + 1) := by
  sorry

private lemma moment_degree (k : ℕ) (hk : 3 ≤ k)
    (f : (Fin k → ZMod 2) → ZMod 2)
    (hm : ∀ a : Finset (Fin k), a.card ≤ 2 → ∑ x, f x * ∏ i ∈ a, x i = 0) :
    ∃ q : Finset (Fin k) → ZMod 2,
      (∀ a, k - 3 < a.card → q a = 0) ∧
      ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
        q a * ∏ i ∈ a, (x i + 1) := by
  sorry

private lemma affine_weight (k : ℕ) (f : (Fin k → ZMod 2) → ZMod 2)
    (q : Finset (Fin k) → ZMod 2) (hq : ∀ a, 1 < a.card → q a = 0)
    (hf : ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      q a * ∏ i ∈ a, (x i + 1)) :
    weight f = 0 ∨ 2 * weight f = 2 ^ k ∨ weight f = 2 ^ k := by
  sorry

private lemma quadratic_polarization (k : ℕ)
    (f : (Fin k → ZMod 2) → ZMod 2)
    (q : Finset (Fin k) → ZMod 2) (hq : ∀ a, 2 < a.card → q a = 0)
    (hf : ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      q a * ∏ i ∈ a, (x i + 1)) :
    ∀ u x y, f (x + y + u) + f (x + y) + f u + f 0 =
      (f (x + u) + f x + f u + f 0) + (f (y + u) + f y + f u + f 0) := by
  sorry

private lemma walsh_square (k : ℕ) (f : (Fin k → ZMod 2) → ZMod 2)
    (hb : ∀ u x y, f (x + y + u) + f (x + y) + f u + f 0 =
      (f (x + u) + f x + f u + f 0) + (f (y + u) + f y + f u + f 0)) :
    (2 ^ k : ℤ) ∣ (∑ x, if f x = 0 then (1 : ℤ) else -1) ^ 2 := by
  sorry

private lemma quadratic_weight (k : ℕ) (hk : k = 5)
    (f : (Fin k → ZMod 2) → ZMod 2)
    (q : Finset (Fin k) → ZMod 2) (hq : ∀ a, 2 < a.card → q a = 0)
    (hf : ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      q a * ∏ i ∈ a, (x i + 1)) : 4 ∣ weight f := by
  have hb := quadratic_polarization k f q hq hf
  have hw := walsh_square k f hb
  sorry

private lemma moments_obstruction (k : ℕ) (s : Finset (Fin k → ZMod 2))
    (hk : k ≤ 5) (hn : s.card ≤ 14) (hd : 2 * (k + 1) < s.card)
    (he : Even s.card)
    (hm : ∀ a : Finset (Fin k), a.card ≤ 2 →
      ∑ x, (if x ∈ s then (1 : ZMod 2) else 0) * ∏ i ∈ a, x i = 0) : False := by
  classical
  have hcard : weight (fun x => if x ∈ s then (1 : ZMod 2) else 0) = s.card := by
    sorry
  have cases : k = 4 ∨ k = 5 := by
    have hs := Finset.card_le_univ s
    have hu : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [Finset.card_univ, hu] at hs
    sorry
  obtain ⟨q, hq, hf⟩ := moment_degree k (by omega) _ hm
  rcases cases with hfour | hfive
  · have hw := affine_weight k _ q (by simpa only [hfour] using hq) hf
    rw [hcard] at hw
    sorry
  · have hw := quadratic_weight k hfive _ q (by simpa only [hfive] using hq) hf
    rw [hcard] at hw
    sorry

private lemma nondegenerate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (hn : Fintype.card ι ≤ 14)
    (hd : 2 * Module.finrank (ZMod 2) c < Fintype.card ι)
    (hs : ∀ i j : ι, i ≠ j → Pi.single i 1 + Pi.single j 1 ∉ c) :
    ∃ v ∈ commutant c, v ∉ c ∧ weight v < 4 := by
  classical
  by_contra h
  have hscomm : ∀ i j : ι, i ≠ j → Pi.single i 1 + Pi.single j 1 ∉ commutant c := by
    intro i j hij hv
    exact h ⟨_, hv, hs i j hij, by rw [pair_weight i j hij]; decide⟩
  obtain ⟨k, hk, r, hi⟩ := column_encoding c hp (by omega) hscomm
  obtain ⟨hcard, hm⟩ := column_moments c hc hp k r hi
  exact moments_obstruction k _ (by omega) (by omega) (by omega)
    (by rw [hcard]; exact parity_card c hc hp) hm

private lemma general_result {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (hn : Fintype.card ι ≤ 14)
    (hd : 2 * Module.finrank (ZMod 2) c < Fintype.card ι) :
    ∃ v ∈ commutant c, v ∉ c ∧ weight v < 4 := by
  classical
  induction hncard : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h m ih =>
    by_cases hs : ∃ i j : ι, i ≠ j ∧ Pi.single i 1 + Pi.single j 1 ∈ c
    · obtain ⟨i, j, hij, hv⟩ := hs
      obtain ⟨d, hdc, hdp, hdim, hsize, hlift⟩ := remove_pair c hc hp i j hij hv
      have smaller : Fintype.card {a : ι // a ≠ i ∧ a ≠ j} < m := by omega
      have short : ∃ v ∈ commutant d, v ∉ d ∧ weight v < 4 := by
        sorry
      obtain ⟨v, hvc, hvd, hvw⟩ := short
      exact hlift v hvc hvd hvw
    · apply nondegenerate c hc hp hn hd
      intro i j hij hv
      exact hs ⟨i, j, hij, hv⟩

/-- The preregistered bound, with the source's stabilizer, parity and distance
definitions and without any additional nondegeneracy assumption. -/
theorem result : claim := by
  intro n hn c hc hp hd
  exact general_result c hc hp (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [Fintype.card_fin] using hd)

end D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour
