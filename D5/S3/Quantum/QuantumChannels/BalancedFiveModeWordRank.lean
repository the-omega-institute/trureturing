/- GID: D5/S3/Quantum/QuantumChannels/BalancedFiveModeWordRank
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/BalancedFiveModeWordRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform homogeneous word rank for the balanced five-mode transported channel. -/

import D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators Matrix Kronecker
open Module Submodule
open D5.S3.Quantum.QuantumChannels.TwoInvolutionWordRank

namespace D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank

abbrev ConfigMatrix := Matrix (Fin 5) (Fin 5) ℂ

/-- The normalized loop/leaf component in the source's transported frames. -/
def reflection0 (a b : ℂ) : ConfigMatrix :=
  !![a, 0, 0, 0, b; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; b, 0, 0, 0, -a]

/-- The balanced signed square component and its unchanged leaf loop. -/
def reflection1 (c : ℂ) : ConfigMatrix :=
  !![0, c, 0, -c, 0; c, 0, c, 0, 0; 0, c, 0, c, 0; -c, 0, c, 0, 0; 0, 0, 0, 0, 1]

private def rotation (a b c : ℂ) : ConfigMatrix := reflection0 a b * reflection1 c

private theorem reflection0_sq (a b : ℂ) (hn : a ^ 2 + b ^ 2 = 1) :
    reflection0 a b * reflection0 a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection0, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf
  all_goals linear_combination hn

private theorem reflection1_sq (c : ℂ) (hn : 2 * c ^ 2 = 1) :
    reflection1 c * reflection1 c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflection1, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf
  all_goals linear_combination hn

private theorem square_relations (a b c : ℂ) (hn : a ^ 2 + b ^ 2 = 1) (hc : 2 * c ^ 2 = 1) :
    b ^ 2 = 1 - a ^ 2 ∧ c ^ 2 = 1/2 ∧ c ^ 3 = c/2 ∧ c ^ 4 = 1/4 := by
  have hcc : c ^ 2 = 1/2 := by linear_combination hc / 2
  refine ⟨?_, hcc, ?_, ?_⟩
  · linear_combination hn
  · rw [pow_succ, hcc]; ring
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hcc]; norm_num

set_option maxHeartbeats 4000000 in
-- Expanding fourth powers contains four nested finite matrix sums.
private theorem quartic (a b c : ℂ) (hn : a ^ 2 + b ^ 2 = 1) (hc : 2 * c ^ 2 = 1) :
    (rotation a b c) ^ 4 = 1 + (a + 1) • rotation a b c - (a + 1) • (rotation a b c) ^ 3 := by
  obtain ⟨hb2, hc2, hc3, hc4⟩ := square_relations a b c hn hc
  have hb3 : b ^ 3 = (1 - a ^ 2) * b := by rw [pow_succ, hb2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, reflection0, reflection1, Matrix.mul_apply, pow_succ,
      Fin.sum_univ_succ] <;> ring_nf <;> simp only [hb2, hb3, hc2, hc3, hc4] <;> ring

private def coordinates : Fin 4 → Fin 5 × Fin 5 := ![(0, 0), (0, 4), (4, 0), (1, 2)]

private def minor (a b c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, a, 1 - a ^ 2; 0, b, -a * b, a * (a + 1) * b; 0, 0, b, -a * b; 0, c, 0, c]

set_option maxHeartbeats 4000000 in
-- The selected power entries expand three nested finite matrix sums.
private theorem power_coordinates (a b c : ℂ) (hn : a ^ 2 + b ^ 2 = 1) (hc : 2 * c ^ 2 = 1) :
    (fun i j : Fin 4 => ((rotation a b c) ^ j.val) (coordinates i).1 (coordinates i).2) =
      minor a b c := by
  obtain ⟨hb2, hc2, hc3, hc4⟩ := square_relations a b c hn hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation, reflection0, reflection1, coordinates, minor, Matrix.mul_apply,
      pow_succ, pow_zero, Matrix.one_apply, Fin.sum_univ_succ] <;>
      try dsimp
  all_goals try ring_nf
  all_goals try simp only [hb2, hc2, hc3]
  all_goals try ring
  all_goals decide

private theorem powers_independent (a b c : ℂ) (hn : a ^ 2 + b ^ 2 = 1) (hc : 2 * c ^ 2 = 1)
    (hb : b ≠ 0) (hca : c ≠ 0) (ha : a ≠ 1) :
    LinearIndependent ℂ (fun i : Fin 4 => (reflection0 a b * reflection1 c) ^ i.val) := by
  have hd : (minor a b c).det = c * b ^ 2 * (1 - a) := by
    simp [minor, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    ring
  have hdn : (minor a b c).det ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (mul_ne_zero hca (pow_ne_zero _ hb)) (sub_ne_zero.mpr ha.symm)
  apply Fintype.linearIndependent_iff.mpr
  intro f hf i
  have heq : (minor a b c) *ᵥ f = 0 := by
    ext j
    have hj := congrArg (fun M : ConfigMatrix => M (coordinates j).1 (coordinates j).2) hf
    change (∑ k : Fin 4, minor a b c j k * f k) = 0
    have hcoord (k : Fin 4) : ((reflection0 a b * reflection1 c) ^ k.val)
        (coordinates j).1 (coordinates j).2 = minor a b c j k :=
      congrFun (congrFun (power_coordinates a b c hn hc) j) k
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hj
    simp_rw [hcoord] at hj
    simpa only [mul_comm] using hj
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdn heq
  exact congrFun hz i

private theorem core_closed (a b c : ℂ) (hn : a ^ 2 + b ^ 2 = 1) (hc : 2 * c ^ 2 = 1) :
    (∀ x ∈ powerSpace (reflection0 a b) (reflection1 c),
      (reflection0 a b * reflection1 c) * x ∈
        powerSpace (reflection0 a b) (reflection1 c)) ∧
    (∀ x ∈ powerSpace (reflection0 a b) (reflection1 c),
      (reflection1 c * reflection0 a b) * x ∈
        powerSpace (reflection0 a b) (reflection1 c)) := by
  let u := reflection0 a b
  let v := reflection1 c
  let R := u * v
  let P := powerSpace u v
  have hu : u * u = 1 := reflection0_sq a b hn
  have hv : v * v = 1 := reflection1_sq c hc
  have hp : ∀ i : Fin 4, R ^ i.val ∈ P := fun i => subset_span ⟨i, rfl⟩
  have hp0 : (1 : ConfigMatrix) ∈ P := by simpa using hp 0
  have hp1 : R ∈ P := by simpa using hp 1
  have hq : R ^ 4 = 1 + (a + 1) • R - (a + 1) • R ^ 3 := quartic a b c hn hc
  have hR : ∀ x ∈ P, R * x ∈ P := by
    intro x hx
    induction hx using span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · simpa using hp 1
      · change R * R ^ 1 ∈ P
        simpa [pow_two] using hp (2 : Fin 4)
      · change R * R ^ 2 ∈ P
        simpa [← pow_succ'] using hp (3 : Fin 4)
      · change R * R ^ 3 ∈ P
        rw [← pow_succ', hq]
        exact P.sub_mem (P.add_mem hp0 (P.smul_mem _ hp1))
          (P.smul_mem _ (hp 3))
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add] using P.add_mem hx hy
    | smul z x _ hx => simpa only [mul_smul_comm] using P.smul_mem z hx
  have hInv : v * u = R ^ 3 + (a + 1) • R ^ 2-(a + 1) • (1 : ConfigMatrix) := by
    have hRR : R * (v * u) = 1 := by
      dsimp [R]
      calc
        (u * v) * (v * u) = u * (v * v) * u := by noncomm_ring
        _ = 1 := by simp [hu, hv]
    have he := congrArg (fun x : ConfigMatrix => x * (v * u)) hq
    have hpow (k : ℕ) : R ^ (k + 1) * (v * u) = R ^ k := by
      rw [pow_succ, mul_assoc, hRR, mul_one]
    simp only [sub_mul, add_mul, one_mul, smul_mul_assoc,
      hpow 3, hpow 2, hRR] at he
    calc
      v * u = R ^ 3-(a + 1) • (1 : ConfigMatrix) + (a + 1) • R ^ 2 := by rw [he]; abel
      _ = R ^ 3 + (a + 1) • R ^ 2-(a + 1) • (1 : ConfigMatrix) := by abel
  refine ⟨hR, ?_⟩
  intro x hx
  rw [hInv, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  have hx2 : R ^ 2 * x ∈ P := by
    simpa only [pow_two, mul_assoc] using hR (R * x) (hR x hx)
  have hx3 : R ^ 3 * x ∈ P := by
    simpa only [pow_succ, pow_two, pow_zero, one_mul, mul_assoc] using
      hR (R * (R * x)) (hR (R * x) (hR x hx))
  exact P.sub_mem (P.add_mem hx3 (P.smul_mem _ hx2)) (P.smul_mem _ hx)

/-- All strict balanced reflection parameters have the same homogeneous rank profile. -/
theorem framed_balanced_word_rank {E : Type*} [Ring E] [Algebra ℂ E]
    [Module.Finite ℂ E] (f : ConfigMatrix →ₐ[ℂ] E) (hf : Function.Injective f)
    (a b c z w : ℂ) (hn : a ^ 2 + b ^ 2 = 1) (hc : 2 * c ^ 2 = 1)
    (hb : b ≠ 0) (hca : c ≠ 0) (ha : a ≠ 1) (hz : z ≠ 0) (hw : w ≠ 0) (n : ℕ) :
    finrank ℂ (wordSpace (z • f (reflection0 a b)) (w • f (reflection1 c)) n) = min (n + 1) 4 := by
  rw [wordSpace_scale _ _ z w hz hw, wordSpace_map]
  rw [← (Submodule.equivMapOfInjective _ hf _).finrank_eq]
  obtain ⟨hR, hD⟩ := core_closed a b c hn hc
  exact homogeneous_word_rank (reflection0 a b) (reflection1 c)
    (reflection0_sq a b hn) (reflection1_sq c hc)
    (powers_independent a b c hn hc hb hca ha) hR hD n

#print axioms framed_balanced_word_rank

end D5.S3.Quantum.QuantumChannels.BalancedFiveModeWordRank
