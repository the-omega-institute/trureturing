/- GID: D5/S3/Quantum/Information/SignallingGameValueEquality
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SignallingGameValueEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The signalling game has classical, quantum and no-signalling value 1/max(m,n). -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import D5.S3.Quantum.Information.SLDSpectralEnergy

/-! The players guess one another's uniformly drawn questions using local correlations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.SignallingGameValueEquality

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
  (IsPOVM diagonal_povm)
open D5.S3.Quantum.FiniteDimensional (bornProbability)
open D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift (labelKernel)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

/-- Nonnegative normalized conditional probabilities with both no-signalling marginals.
The argument order is Alice's answer, Bob's answer, Alice's question, Bob's question. -/
def IsNoSignalling {m n : ℕ} (p : Fin n → Fin m → Fin m → Fin n → ℝ) : Prop :=
  (∀ a b x y, 0 ≤ p a b x y) ∧
  (∀ x y, ∑ a, ∑ b, p a b x y = 1) ∧
  (∀ a x y z, ∑ b, p a b x y = ∑ b, p a b x z) ∧
  (∀ b x z y, ∑ a, p a b x y = ∑ a, p a b z y)

/-- Uniform questions; each player must answer the other player's question. -/
def winProb {m n : ℕ} (p : Fin n → Fin m → Fin m → Fin n → ℝ) : ℝ :=
  (1 / ((m : ℝ) * n)) * ∑ x, ∑ y, p y x x y

/-- The product of the two deterministic local response distributions. -/
def deterministicBox {m n : ℕ} (fa : Fin m → Fin n) (fb : Fin n → Fin m)
    (a : Fin n) (b : Fin m) (x : Fin m) (y : Fin n) : ℝ :=
  labelKernel fa x a * labelKernel fb y b

/-- All winning probabilities of deterministic classical strategies. -/
def classicalValues (m n : ℕ) : Set ℝ :=
  {v | ∃ (fa : Fin m → Fin n) (fb : Fin n → Fin m),
    winProb (deterministicBox fa fb) = v}

/-- A finite bipartite density matrix and a local POVM for each local question. -/
def IsQuantumStrategy {m n da db : ℕ}
    (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ) : Prop :=
  IsDensity rho ∧ (∀ x, IsPOVM (a x)) ∧ (∀ y, IsPOVM (b y))

/-- Born's rule for local measurements of a shared bipartite state. -/
def quantumBox {m n da db : ℕ}
    (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ)
    (u : Fin n) (v : Fin m) (x : Fin m) (y : Fin n) : ℝ :=
  (bornProbability rho (a x u ⊗ₖ b y v)).re

/-- All winning probabilities over all finite local dimensions, states and local POVMs. -/
def quantumValues (m n : ℕ) : Set ℝ :=
  {v | ∃ (da db : ℕ) (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ),
    IsQuantumStrategy rho a b ∧ winProb (quantumBox rho a b) = v}

/-- All winning probabilities of normalized no-signalling boxes. -/
def noSignallingValues (m n : ℕ) : Set ℝ :=
  {v | ∃ p : Fin n → Fin m → Fin m → Fin n → ℝ,
    IsNoSignalling p ∧ winProb p = v}

/-- For every pair of nonempty question sets all three greatest values equal `1/max(m,n)`. -/
def claim : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    IsGreatest (noSignallingValues m n) (1 / (max m n : ℝ)) ∧
    IsGreatest (quantumValues m n) (1 / (max m n : ℝ)) ∧
    IsGreatest (classicalValues m n) (1 / (max m n : ℝ))

private lemma noSignalling_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {p : Fin n → Fin m → Fin m → Fin n → ℝ} (hp : IsNoSignalling p) :
    winProb p ≤ 1 / (max m n : ℝ) := by
  obtain ⟨hpos, hnorm, ha, hb⟩ := hp
  let xzero : Fin m := ⟨0, by omega⟩
  let yzero : Fin n := ⟨0, by omega⟩
  have hmarg : (∑ x, ∑ y, p y x x y) ≤ (m : ℝ) := by
    calc
      (∑ x, ∑ y, p y x x y) ≤ ∑ x, ∑ y, ∑ b, p y b x yzero := by
        apply sum_le_sum
        intro x hx
        apply sum_le_sum
        intro y hy
        rw [← ha y x y yzero]
        exact single_le_sum (fun b _ => hpos y b x y) (mem_univ x)
      _ = m := by simp only [hnorm, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
  have hnarg : (∑ x, ∑ y, p y x x y) ≤ (n : ℝ) := by
    calc
      (∑ x, ∑ y, p y x x y) = ∑ y, ∑ x, p y x x y := sum_comm
      _ ≤ ∑ y, ∑ x, ∑ a, p a x xzero y := by
        apply sum_le_sum
        intro y hy
        apply sum_le_sum
        intro x hx
        rw [← hb x x xzero y]
        exact single_le_sum (fun a _ => hpos a x x y) (mem_univ y)
      _ = n := by
        have hs (y : Fin n) : (∑ x, ∑ a, p a x xzero y) = 1 := by
          rw [sum_comm]
          exact hnorm xzero y
        simp only [hs, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold winProb
  rcases le_total m n with hmn | hnm
  · rw [max_eq_right (show (m : ℝ) ≤ n by exact_mod_cast hmn)]
    calc
      _ ≤ 1 / ((m : ℝ) * n) * m := mul_le_mul_of_nonneg_left hmarg (by positivity)
      _ = 1 / (n : ℝ) := by field_simp
  · rw [max_eq_left (show (n : ℝ) ≤ m by exact_mod_cast hnm)]
    calc
      _ ≤ 1 / ((m : ℝ) * n) * n := mul_le_mul_of_nonneg_left hnarg (by positivity)
      _ = 1 / (m : ℝ) := by field_simp

private lemma quantum_noSignalling {m n da db : ℕ}
    (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ)
    (hs : IsQuantumStrategy rho a b) : IsNoSignalling (quantumBox rho a b) := by
  obtain ⟨⟨hrho, htrace⟩, ha, hb⟩ := hs
  have right (u : Fin n) (x : Fin m) (y : Fin n) :
      (∑ v, quantumBox rho a b u v x y) =
        (trace (rho * (a x u ⊗ₖ (1 : Matrix (Fin db) (Fin db) ℂ)))).re := by
    simp only [quantumBox.eq_1, bornProbability, ← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum]
    have he : (∑ v, a x u ⊗ₖ b y v) = a x u ⊗ₖ (1 : Matrix (Fin db) (Fin db) ℂ) := by
      calc
        _ = a x u ⊗ₖ (∑ v, b y v) := by
          exact (map_sum (Matrix.kroneckerBilinear (R := ℂ) (a x u))
            (b y) univ).symm
        _ = _ := by rw [(hb y).2]
    rw [he]
  have left (v : Fin m) (x : Fin m) (y : Fin n) :
      (∑ u, quantumBox rho a b u v x y) =
        (trace (rho * ((1 : Matrix (Fin da) (Fin da) ℂ) ⊗ₖ b y v))).re := by
    simp only [quantumBox.eq_1, bornProbability, ← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum]
    have he : (∑ u, a x u ⊗ₖ b y v) = (1 : Matrix (Fin da) (Fin da) ℂ) ⊗ₖ b y v := by
      calc
        _ = (∑ u, a x u) ⊗ₖ b y v := by
          exact (LinearMap.map_sum₂ (Matrix.kroneckerBilinear (R := ℂ))
            univ (a x) (b y v)).symm
        _ = _ := by rw [(ha x).2]
    rw [he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v x y
    exact (Complex.nonneg_iff.mp
      (hrho.trace_mul_nonneg (((ha x).1 u).kronecker ((hb y).1 v)))).1
  · intro x y
    simp only [right, ← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum]
    have he : (∑ u, a x u ⊗ₖ (1 : Matrix (Fin db) (Fin db) ℂ)) = 1 := by
      calc
        _ = (∑ u, a x u) ⊗ₖ (1 : Matrix (Fin db) (Fin db) ℂ) := by
          exact (LinearMap.map_sum₂ (Matrix.kroneckerBilinear (R := ℂ))
            univ (a x) (1 : Matrix (Fin db) (Fin db) ℂ)).symm
        _ = 1 := by rw [(ha x).2, one_kronecker_one]
    rw [he, Matrix.mul_one, htrace, Complex.one_re]
  · intro u x y z
    rw [right, right]
  · intro v x z y
    rw [left, left]

private lemma deterministic_quantum {m n : ℕ} (fa : Fin m → Fin n) (fb : Fin n → Fin m) :
    ∃ (rho : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
      (a : Fin m → Fin n → Matrix (Fin 1) (Fin 1) ℂ)
      (b : Fin n → Fin m → Matrix (Fin 1) (Fin 1) ℂ),
      IsQuantumStrategy rho a b ∧ quantumBox rho a b = deterministicBox fa fb := by
  let a : Fin m → Fin n → Matrix (Fin 1) (Fin 1) ℂ :=
    fun x u => diagonal (fun _ => (labelKernel fa x u : ℂ))
  let b : Fin n → Fin m → Matrix (Fin 1) (Fin 1) ℂ :=
    fun y v => diagonal (fun _ => (labelKernel fb y v : ℂ))
  refine ⟨1, a, b, ⟨⟨Matrix.PosSemidef.one, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp only [trace_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_one, one_mul]
  · intro x
    exact diagonal_povm (fun u _ => labelKernel fa x u)
      (fun u _ => by unfold labelKernel; split_ifs <;> norm_num)
      (fun _ => by simp [labelKernel])
  · intro y
    exact diagonal_povm (fun v _ => labelKernel fb y v)
      (fun v _ => by unfold labelKernel; split_ifs <;> norm_num)
      (fun _ => by simp [labelKernel])
  · funext u v x y
    by_cases hu : u = fa x <;> by_cases hv : v = fb y <;>
      simp only [quantumBox.eq_1, bornProbability, deterministicBox.eq_1, labelKernel, eq_comm, a, b, hu, hv, ite_true, ite_false,
        Complex.ofReal_one, Complex.ofReal_zero, diagonal_one, diagonal_zero,
        one_kronecker_one, zero_kronecker, kronecker_zero,
        trace_one, trace_zero, Fintype.card_prod, Fintype.card_fin, Nat.cast_one,
        mul_one, mul_zero, Complex.one_re, Complex.zero_re]

private lemma optimal_deterministic {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ (fa : Fin m → Fin n) (fb : Fin n → Fin m),
      winProb (deterministicBox fa fb) = 1 / (max m n : ℝ) := by
  let fa : Fin m → Fin n := fun x => @Fin.ofNat n ⟨by omega⟩ x.val
  let fb : Fin n → Fin m := fun y => @Fin.ofNat m ⟨by omega⟩ y.val
  refine ⟨fa, fb, ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold winProb
  rcases le_total m n with hmn | hnm
  · have hi (x : Fin m) : fb (fa x) = x := by
      apply Fin.ext
      dsimp only [fa, fb]
      simp only [Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt hmn), Nat.mod_eq_of_lt x.isLt]
    have hs : (∑ x, ∑ y, deterministicBox fa fb y x x y) = (m : ℝ) := by
      simp only [deterministicBox.eq_1, labelKernel, eq_comm, ite_mul, one_mul, zero_mul]
      simp [hi]
    rw [hs, max_eq_right (show (m : ℝ) ≤ n by exact_mod_cast hmn)]
    field_simp
  · have hi (y : Fin n) : fa (fb y) = y := by
      apply Fin.ext
      dsimp only [fa, fb]
      simp only [Fin.val_ofNat]
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le y.isLt hnm), Nat.mod_eq_of_lt y.isLt]
    have hs : (∑ x, ∑ y, deterministicBox fa fb y x x y) = (n : ℝ) := by
      rw [sum_comm]
      simp only [deterministicBox.eq_1, labelKernel, eq_comm, mul_ite, mul_one, mul_zero]
      simp [hi]
    rw [hs, max_eq_left (show (n : ℝ) ≤ m by exact_mod_cast hnm)]
    field_simp

/-- The uniform signalling game has the same sharp value in all three strategy classes. -/
theorem result : claim := by
  intro m n hm hn
  obtain ⟨fa, fb, hv⟩ := optimal_deterministic hm hn
  obtain ⟨rho, a, b, hs, he⟩ := deterministic_quantum fa fb
  have hp := quantum_noSignalling rho a b hs
  have hq : winProb (quantumBox rho a b) = 1 / (max m n : ℝ) := by rw [he, hv]
  refine ⟨⟨⟨_, hp, hq⟩, ?_⟩, ⟨⟨1, 1, rho, a, b, hs, hq⟩, ?_⟩,
    ⟨⟨fa, fb, hv⟩, ?_⟩⟩
  · rintro v ⟨p, hp, rfl⟩
    exact noSignalling_bound hm hn hp
  · rintro v ⟨da, db, rho, a, b, hs, rfl⟩
    exact noSignalling_bound hm hn (quantum_noSignalling rho a b hs)
  · rintro v ⟨fa, fb, rfl⟩
    obtain ⟨rho, a, b, hs, he⟩ := deterministic_quantum fa fb
    rw [← he]
    exact noSignalling_bound hm hn (quantum_noSignalling rho a b hs)

end D5.S3.Quantum.Information.SignallingGameValueEquality
