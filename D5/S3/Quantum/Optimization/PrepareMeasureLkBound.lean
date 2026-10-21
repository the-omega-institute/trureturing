/- GID: D5/S3/Quantum/Optimization/PrepareMeasureLkBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Optimization/PrepareMeasureLkBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The prepare-and-measure bound is uniformly strict for every k at least three. -/

import Mathlib

/-! The averaged sign functional gives a strict prepare-and-measure bound. -/

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Optimization.PrepareMeasureLkBound

abbrev Sign := Fin 2

def signValue (s : Sign) : ℝ := if s = 0 then -1 else 1

def manhattan {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

def fiberSum {n m k : ℕ} (f : Fin n → Fin k) (M : Matrix (Fin n) (Fin m) ℝ)
    (j : Fin k) (q : Fin m) : ℝ :=
  ∑ i, if f i = j then M i q else 0

private def fiberMax {n m k : ℕ} (hk : 0 < k) (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  letI : Nonempty (Fin n → Fin k) := ⟨fun _ => ⟨0, hk⟩⟩
  (Finset.univ : Finset (Fin n → Fin k)).sup'
    Finset.univ_nonempty (fun f => ∑ j, ∑ q, |fiberSum f M j q|)

def Lk (k : ℕ) {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  if hk : 0 < k then fiberMax hk M else 0

def L {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  letI : Nonempty (Fin n → Sign) := ⟨fun _ => 0⟩
  (Finset.univ : Finset (Fin n → Sign)).sup'
    Finset.univ_nonempty (fun v => ∑ j, |∑ i, signValue (v i) * M i j|)

def a (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹ * ∑ ε : Fin k → Sign, |∑ i, signValue (ε i)|

def claim : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, c < k ∧
    ∀ n m (M : Matrix (Fin n) (Fin m) ℝ), Lk k M ≤ c * L M

private lemma averaged_abs_lower (k : ℕ) (hk : 0 < k) (x : Fin k → ℝ) :
    (a k / k) * (∑ i, |x i|) ≤
      ((2 : ℝ) ^ k)⁻¹ * ∑ ε : Fin k → Sign, |∑ i, signValue (ε i) * x i| := by
  sorry

private lemma a_lower_three_halves (k : ℕ) (hk : 3 ≤ k) :
    (3 / 2 : ℝ) ≤ a k := by
  sorry

private lemma lk_bound (k : ℕ) (hk : 0 < k) (n m : ℕ)
    (M : Matrix (Fin n) (Fin m) ℝ) :
    Lk k M ≤ ((k : ℝ) / a k) * L M := by
  sorry

theorem result : claim := by
  intro k hk
  have hk0 : 0 < k := by omega
  have ha : (3 / 2 : ℝ) ≤ a k := a_lower_three_halves k hk
  have hak : 1 < a k := by linarith
  let c : ℝ := (k : ℝ) / a k
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    apply (div_lt_iff₀ (lt_trans (by norm_num : (0 : ℝ) < 1) hak)).mpr
    nlinarith
  · intro n m M
    exact lk_bound k hk0 n m M

end D5.S3.Quantum.Optimization.PrepareMeasureLkBound
