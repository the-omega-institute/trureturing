/- GID: D5/S3/Combinatorics/Graph/Walks/AndersonDefectFamily
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/AndersonDefectFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: The actual defect family has scalar joint commutant and persistent nodal polynomial factors. -/

/-
proof_shape: defect_family: content.
admission_basis: escape-witness.
escape_witness: the actual defect geometry supplies the adjacent-unit seed,
  and actual periodic transport supplies the normalized fixed-node eigenvector;
  both are consumed by defect_family.
Direct frozen dependencies: CycleDiagonalUnitPropagation.cycle_diagonal_units_full;
  AndersonSymmetryConverseRefutation.bad; MatrixTracePowerSum.pow_add_two.
-/

import D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic
import D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import D5.S3.Combinatorics.Graph.AndersonSymmetryConverseRefutation
import D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation

set_option autoImplicit false

open Matrix
open scoped Fin.NatCast

open D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed

namespace D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily

/-- The actual graph Hamiltonian, with the ordinary cycle graph Laplacian. -/
def hamiltonian {K : Type*} [CommRing K] (r m : ℕ) (t : K) :
    Matrix (Fin (r * m)) (Fin (r * m)) K :=
  (SimpleGraph.cycleGraph (r * m)).lapMatrix K + t • Matrix.diagonal (signWord r m)

/-- One step of the scalar Schrodinger recurrence. -/
def transfer {K : Type*} [Ring K] (d : K) : Matrix (Fin 2) (Fin 2) K :=
  !![d, -1; 1, 0]

/-- The periodic block is minus followed by r-1 plus signs. -/
def block {K : Type*} [Ring K] (r : ℕ) (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  transfer a ^ (r - 1) * transfer b

/-- The trace of the actual periodic block as a polynomial in the spectral variable. -/
noncomputable def discriminant {K : Type*} [CommRing K] (r : ℕ) (t : K) : Polynomial K :=
  (block r (2 + Polynomial.C t - Polynomial.X)
    (2 - Polynomial.C t - Polynomial.X)).trace

/-- The exact product indexed by the strict inequality from the periodic spectrum. -/
noncomputable def traceFactors {K : Type*} [CommRing K] [Algebra ℝ K]
    (r m : ℕ) (t : K) : Polynomial K :=
  ∏ k ∈ (Finset.range m).filter (fun k => 0 < k ∧ 2 * k < m),
    (discriminant r t - Polynomial.C (algebraMap ℝ K
      (2 * Real.cos (2 * Real.pi * k / m))))

private lemma map_transfer {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (d : R) :
    (transfer d).map f = transfer (f d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transfer]

private lemma map_block {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (r : ℕ) (a b : R) : (block r a b).map f = block r (f a) (f b) := by
  simp only [block, ← RingHom.mapMatrix_apply, map_mul, map_pow]
  simp only [RingHom.mapMatrix_apply, map_transfer]

private lemma discriminant_eval {K : Type*} [CommRing K] (r : ℕ) (t μ : K) :
    (discriminant r t).eval μ = (block r (2 + t - μ) (2 - t - μ)).trace := by
  change (Polynomial.evalRingHom μ) (block r (2 + Polynomial.C t - Polynomial.X)
    (2 - Polynomial.C t - Polynomial.X)).trace = _
  rw [AddMonoidHom.map_trace (Polynomial.evalRingHom μ), map_block]
  simp

private lemma discriminant_eval₂ {K E : Type*} [CommRing K] [CommRing E]
    (f : K →+* E) (r : ℕ) (t : K) (μ : E) :
    (discriminant r t).eval₂ f μ = (block r (2 + f t - μ) (2 - f t - μ)).trace := by
  change (Polynomial.eval₂RingHom f μ) (block r (2 + Polynomial.C t - Polynomial.X)
    (2 - Polynomial.C t - Polynomial.X)).trace = _
  rw [AddMonoidHom.map_trace (Polynomial.eval₂RingHom f μ), map_block]
  simp

private lemma map_hamiltonian {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r m : ℕ) (t : R) :
    (hamiltonian r m t).map f = hamiltonian r m (f t) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hv : i.val % r = 0 ∨ i.val = defectSite r m <;>
      simp [hamiltonian, Matrix.map_apply, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply, Matrix.diagonal, signWord, hv]
  · by_cases ha : (SimpleGraph.cycleGraph (r * m)).Adj i j <;>
      simp [hamiltonian, Matrix.map_apply, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply, Matrix.diagonal, hij, ha]

private lemma transfer_det {K : Type*} [CommRing K] (d : K) :
    (transfer d).det = 1 := by
  simp [transfer, Matrix.det_fin_two]

private lemma sl2_power {K : Type*} [CommRing K]
    (B : Matrix (Fin 2) (Fin 2) K) (hdet : B.det = 1) (n : ℕ) :
    B ^ n = (Polynomial.Chebyshev.S K ((n : ℤ) - 1)).eval B.trace • B -
      (Polynomial.Chebyshev.S K ((n : ℤ) - 2)).eval B.trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
  let s : ℤ → K := fun j => (Polynomial.Chebyshev.S K j).eval B.trace
  have chebStep (j : ℤ) : s (j + 1) = B.trace * s j - s (j - 1) := by
    simp [s, Polynomial.Chebyshev.S_add_one]
  change B ^ n = s ((n : ℤ) - 1) • B - s ((n : ℤ) - 2) • 1
  induction n using Nat.twoStepInduction with
  | zero => simp [s, Polynomial.Chebyshev.S_neg_one, Polynomial.Chebyshev.S_neg_two]
  | one => simp [s, Polynomial.Chebyshev.S_neg_one]
  | more n ih0 ih1 =>
    rw [D5.S0.Observation.MatrixTracePowerSum.pow_add_two, hdet, one_smul, ih1, ih0]
    have h0 : ((n + 2 : ℕ) : ℤ) - 2 = n := by omega
    have h1 : ((n + 2 : ℕ) : ℤ) - 1 = (n : ℤ) + 1 := by omega
    have h2 : ((n + 1 : ℕ) : ℤ) - 1 = n := by omega
    have h3 : ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 := by omega
    rw [h0, h1, h2, h3, chebStep, show s (n : ℤ) = B.trace * s ((n : ℤ) - 1) - s ((n : ℤ) - 2) from by
      simpa [sub_sub] using chebStep ((n : ℤ) - 1)]
    module

private lemma block_trace {K : Type*} [CommRing K] (r : ℕ) (hr : 3 ≤ r) (a b : K) :
    (block r a b).trace =
      b * (Polynomial.Chebyshev.S K ((r : ℤ) - 1)).eval a -
      2 * (Polynomial.Chebyshev.S K ((r : ℤ) - 2)).eval a := by
  have htr : (transfer a).trace = a := by simp [transfer, Matrix.trace_fin_two]
  have hmul : (transfer a * transfer b).trace = a * b - 2 := by
    simp [transfer, Matrix.trace_fin_two]
    ring
  rw [block, sl2_power (transfer a) (transfer_det a), Matrix.sub_mul,
    Matrix.smul_mul, Matrix.smul_mul, one_mul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, hmul, htr]
  have ht : (transfer b).trace = b := by simp [transfer, Matrix.trace_fin_two]
  rw [ht]
  have h1 : ((r - 1 : ℕ) : ℤ) - 1 = (r : ℤ) - 2 := by omega
  have h2 : ((r - 1 : ℕ) : ℤ) - 2 = (r : ℤ) - 3 := by omega
  rw [h1, h2]
  have hs := Polynomial.Chebyshev.S_add_one K ((r : ℤ) - 2)
  have he : (Polynomial.Chebyshev.S K ((r : ℤ) - 1)).eval a =
      a * (Polynomial.Chebyshev.S K ((r : ℤ) - 2)).eval a -
      (Polynomial.Chebyshev.S K ((r : ℤ) - 3)).eval a := by
    have hh := congrArg (Polynomial.eval a) hs
    simpa [sub_sub, show (r : ℤ) - 2 + 1 = (r : ℤ) - 1 by omega] using hh
  rw [he]
  simp only [smul_eq_mul]
  ring

private lemma sl2_torsion_of_cos {K : Type*} [Field K] [Algebra ℝ K]
    (B : Matrix (Fin 2) (Fin 2) K) (hdet : B.det = 1)
    (m k : ℕ) (hk : 0 < k) (hkm : 2 * k < m)
    (htrace : B.trace = algebraMap ℝ K (2 * Real.cos (2 * Real.pi * k / m))) :
    B ^ m = 1 := by
  let θ : ℝ := 2 * Real.pi * k / m
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkmR : (2 : ℝ) * k < m := by exact_mod_cast hkm
  have hθpos : 0 < θ := div_pos (by positivity) hmR
  have hθpi : θ < Real.pi := by
    apply (div_lt_iff₀ hmR).mpr
    nlinarith [Real.pi_pos]
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθpos hθpi).ne'
  have hperiod : (m : ℝ) * θ = k * (2 * Real.pi) := by
    dsimp [θ]
    field_simp
  have hfirst : (Polynomial.Chebyshev.S ℝ ((m : ℤ) - 1)).eval (2 * Real.cos θ) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hsin
    have hh := Polynomial.Chebyshev.S_two_mul_real_cos θ ((m : ℤ) - 1)
    have ha : (((m : ℤ) - 1 : ℤ) + 1 : ℝ) * θ = (2 * k : ℕ) * Real.pi := by
      push_cast
      nlinarith [hperiod]
    rw [ha, Real.sin_nat_mul_pi] at hh
    exact hh
  have hsecond : (Polynomial.Chebyshev.S ℝ ((m : ℤ) - 2)).eval (2 * Real.cos θ) = -1 := by
    apply (mul_right_cancel₀ hsin)
    have hh := Polynomial.Chebyshev.S_two_mul_real_cos θ ((m : ℤ) - 2)
    rw [hh]
    have ha : (((m : ℤ) - 2 : ℤ) + 1 : ℝ) * θ = k * (2 * Real.pi) - θ := by
      push_cast
      nlinarith [hperiod]
    rw [ha, Real.sin_nat_mul_two_pi_sub]
    ring
  rw [sl2_power B hdet, htrace]
  rw [← Polynomial.Chebyshev.algebraMap_eval_S,
    ← Polynomial.Chebyshev.algebraMap_eval_S]
  change algebraMap ℝ K ((Polynomial.Chebyshev.S ℝ ((m : ℤ) - 1)).eval
      (2 * Real.cos θ)) • B -
    algebraMap ℝ K ((Polynomial.Chebyshev.S ℝ ((m : ℤ) - 2)).eval
      (2 * Real.cos θ)) • 1 = 1
  rw [hfirst, hsecond]
  simp

private def evolution {K : Type*} [Ring K] (d : ℕ → K) :
    ℕ → Matrix (Fin 2) (Fin 2) K
  | 0 => 1
  | n + 1 => transfer (d n) * evolution d n

private lemma evolution_add {K : Type*} [Ring K] (d : ℕ → K) (n k : ℕ) :
    evolution d (n + k) = evolution (fun i => d (n + i)) k * evolution d n := by
  induction k with
  | zero => simp [evolution]
  | succ k ih =>
    change transfer (d (n + k)) * evolution d (n + k) =
      (transfer (d (n + k)) * evolution (fun i => d (n + i)) k) * evolution d n
    rw [ih, mul_assoc]

private lemma evolution_det {K : Type*} [CommRing K] (d : ℕ → K) (n : ℕ) :
    (evolution d n).det = 1 := by
  induction n with
  | zero => simp [evolution]
  | succ n ih => simp [evolution, Matrix.det_mul, transfer_det, ih]

private lemma periodic_evolution {K : Type*} [Ring K] (r m : ℕ) (hr : 0 < r)
    (a b : K) :
    evolution (fun i => if i % r = 0 then b else a) (r * m) = block r a b ^ m := by
  let d : ℕ → K := fun i => if i % r = 0 then b else a
  have prefixStep : ∀ s, s < r → evolution d (s + 1) = transfer a ^ s * transfer b := by
    intro s
    induction s with
    | zero => intro _; simp [evolution, d]
    | succ s ih =>
      intro hs
      have hsr : s < r := by omega
      have hmod : (s + 1) % r = s + 1 := Nat.mod_eq_of_lt hs
      rw [evolution, ih hsr]
      simp only [d, hmod, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      rw [← mul_assoc, ← pow_succ']
  have whole : evolution d r = block r a b := by
    have hh := prefixStep (r - 1) (by omega)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ r), block] using hh
  change evolution d (r * m) = block r a b ^ m
  induction m with
  | zero => simp [evolution]
  | succ m ih =>
    rw [Nat.mul_succ, evolution_add]
    have shifted : (fun i => d (r * m + i)) = d := by
      funext i
      simp [d, Nat.add_mod, Nat.mul_mod]
    rw [shifted, whole, ih, pow_succ']

private lemma cycle_equation {K : Type*} [CommRing K] (L : ℕ) (hL : 3 ≤ L)
    (v : Fin L → K) (t μ : K) (z : Fin L → K)
    (recurrence : ∀ i : Fin L,
      (2 + t * v i - μ) * z i =
        z (i - ⟨1, by omega⟩) + z (i + ⟨1, by omega⟩)) :
    ((SimpleGraph.cycleGraph L).lapMatrix K + t • Matrix.diagonal v) *ᵥ z = μ • z := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
  have hone : (⟨1, by omega⟩ : Fin (n + 3)) = 1 := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < n + 3 by omega)]
  simp only [hone] at recurrence
  have hne (i : Fin (n + 3)) : i - 1 ≠ i + 1 := by
    intro he
    have he' : (0 : Fin (n + 3)) = 2 := by
      calc
        0 = (i - 1) - (i - 1) := by simp
        _ = (i + 1) - (i - 1) := by rw [he]
        _ = 2 := by
          simpa only [one_add_one_eq_two] using
            (show (i + 1) - (i - 1) = (1 : Fin (n + 3)) + 1 by abel)
    have hv := congrArg Fin.val he'
    simp [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at hv
  ext i
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_diagonal,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [SimpleGraph.lapMatrix_mulVec_apply,
    SimpleGraph.cycleGraph_degree_three_le,
    SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair (hne i)]
  have hh := recurrence i
  linear_combination hh

set_option maxHeartbeats 1000000 in
-- Finite matrix and cycle-coordinate normalization uses this local proof budget.
/-- Identity monodromy of the actual periodic block gives a nonzero eigenvector
of the actual defect Hamiltonian, normalized at the neighbour of the fixed node. -/
private theorem defect_nodal_of_block_power_one {K : Type*} [Field K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) (t μ : K)
    (monodromy : block r (2 + t - μ) (2 - t - μ) ^ m = 1) :
    ∃ z : Fin (r * m) → K,
      z ≠ 0 ∧ hamiltonian r m t *ᵥ z = μ • z ∧
      z ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩ = 0 ∧
      z ⟨defectSite r m + 1, by have := defect_bounds r m hr hm; omega⟩ = 1 := by
  classical
  have hL : 3 ≤ r * m := by
    calc
      3 ≤ r := hr
      _ = r * 1 := by simp
      _ ≤ r * m := Nat.mul_le_mul_left r (by omega)
  have hpos : 0 < r := by omega
  have hLpos : 0 < r * m := by omega
  letI : NeZero (r * m) := ⟨by omega⟩
  let L := r * m
  let q := defectSite r m
  have hq : q + 1 < L := defect_bounds r m hr hm
  let d : ℕ → K := fun i => if i % r = 0 then 2 - t - μ else 2 + t - μ
  let F := evolution d
  have hF : F L = 1 := by
    dsimp [F, L, d]
    rw [periodic_evolution r m hpos, monodromy]
  let e : Fin 2 → K := ![0, -1]
  let w : Fin 2 → K := (F q)⁻¹ *ᵥ e
  let y : ℕ → Fin 2 → K := fun i => F i *ᵥ w
  have yq : y q = e := by
    dsimp [y, w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv]
    · simp
    · rw [show (F q).det = 1 from evolution_det d q]
      exact isUnit_one
  have yf (i : ℕ) : y (i + 1) 0 = d i * y i 0 - y i 1 := by
    dsimp [y, F]
    rw [evolution, ← Matrix.mulVec_mulVec]
    simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  have ys (i : ℕ) : y (i + 1) 1 = y i 0 := by
    dsimp [y, F]
    rw [evolution, ← Matrix.mulVec_mulVec]
    simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  have yp (i : ℕ) : y (L + i) = y i := by
    have hd : (fun j => d (L + j)) = d := by
      funext j
      simp [d, L, Nat.add_mod, Nat.mul_mod]
    dsimp [y, F]
    rw [evolution_add, hd, show evolution d L = 1 from hF, mul_one]
  let z : Fin L → K := fun i => y i.val 0
  have hzq : z ⟨q, by omega⟩ = 0 := by
    change y q 0 = 0
    rw [yq]
    rfl
  have hznext : z ⟨q + 1, hq⟩ = 1 := by
    change y (q + 1) 0 = 1
    rw [yf, yq]
    simp [e]
  have hz : z ≠ 0 := by
    intro he
    have hh := congrFun he ⟨q + 1, hq⟩
    rw [hznext] at hh
    exact one_ne_zero hh
  have hrec : ∀ i : Fin L,
      (2 + t * signWord r m i - μ) * z i =
        z (i - ⟨1, by omega⟩) + z (i + ⟨1, by omega⟩) := by
    intro i
    have hone : (⟨1, by omega⟩ : Fin L) = 1 := by
      ext
      simp [Nat.mod_eq_of_lt (by omega : 1 < L)]
    rw [hone]
    have forward : z (i + 1) = y (i.val + 1) 0 := by
      by_cases hlast : i.val + 1 < L
      · simp only [z, Fin.val_add_one_of_lt' hlast]
      · have hi : i.val + 1 = L := by have := i.isLt; omega
        have he : i + 1 = 0 := by
          apply Fin.ext
          simp [Fin.val_add, hi, Nat.mod_eq_of_lt (by omega : 1 < L)]
        rw [he]
        change y 0 0 = y (i.val + 1) 0
        rw [hi]
        simpa using congrFun (yp 0).symm 0
    have backward : z (i - 1) = y i.val 1 := by
      by_cases hi : i = 0
      · subst i
        have hval : ((0 : Fin L) - 1).val = L - 1 := by
          simp [Fin.val_neg, Nat.mod_eq_of_lt (by omega : 1 < L), show L ≠ 1 by omega]
        change y (((0 : Fin L) - 1).val) 0 = y 0 1
        rw [hval]
        have hs := ys (L - 1)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ L)] at hs
        have hper : y L = y 0 := by simpa using yp 0
        rw [hper] at hs
        exact hs.symm
      · rw [show z (i - 1) = y (i.val - 1) 0 by
          simp only [z, Fin.val_sub_one_of_ne_zero hi]]
        have hival : 0 < i.val := by
          have hh : i.val ≠ 0 := fun he => hi (Fin.ext he)
          omega
        have hs := ys (i.val - 1)
        rw [Nat.sub_add_cancel hival] at hs
        exact hs.symm
    rw [forward, backward]
    have base : d i.val * y i.val 0 = y i.val 1 + y (i.val + 1) 0 := by
      rw [yf]
      ring
    by_cases hiq : i.val = q
    · have hzero : y i.val 0 = 0 := by
        rw [hiq, yq]
        rfl
      simpa [z, hzero] using base
    · have coeff : 2 + t * signWord r m i - μ = d i.val := by
        have hiq' : i.val ≠ defectSite r m := hiq
        simp only [signWord, hiq', or_false, d]
        split_ifs <;> ring
      simpa only [coeff, z] using base
  exact ⟨z, hz, cycle_equation L hL (signWord r m) t μ z hrec, hzq, hznext⟩


/-- The actual deleted-site principal minor, indexed by the remaining vertices. -/
def deleted {K : Type*} [CommRing K] (r m : ℕ) (t : K) (j : Fin (r * m)) :
    Matrix {i : Fin (r * m) // i ≠ j} {i : Fin (r * m) // i ≠ j} K :=
  (hamiltonian r m t).submatrix
    (Subtype.val : {i : Fin (r * m) // i ≠ j} → Fin (r * m)) Subtype.val

/-- The monic greatest common divisor of the two actual characteristic polynomials. -/
noncomputable def nodeFactor {K : Type*} [Field K] (r m : ℕ)
    (hr : 3 ≤ r) (hm : 2 ≤ m) (t : K) : Polynomial K := by
  classical
  exact normalize (gcd (hamiltonian r m t).charpoly
    (deleted r m t ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly)

private lemma nodeFactor_monic {K : Type*} [Field K] (r m : ℕ)
    (hr : 3 ≤ r) (hm : 2 ≤ m) (t : K) : (nodeFactor r m hr hm t).Monic := by
  classical
  apply Polynomial.monic_normalize
  exact gcd_ne_zero_of_left (Matrix.charpoly_monic _).ne_zero

private lemma nodeFactor_divides {K : Type*} [Field K] (r m : ℕ)
    (hr : 3 ≤ r) (hm : 2 ≤ m) (t : K) :
    nodeFactor r m hr hm t ∣ (hamiltonian r m t).charpoly ∧
    nodeFactor r m hr hm t ∣ (deleted r m t
      ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly := by
  classical
  exact ⟨normalize_dvd_iff.mpr (gcd_dvd_left _ _),
    normalize_dvd_iff.mpr (gcd_dvd_right _ _)⟩

private lemma root_of_eigenvector {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] (H : Matrix n n K) (μ : K) (z : n → K)
    (hz : z ≠ 0) (he : H *ᵥ z = μ • z) : H.charpoly.IsRoot μ := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    exact hz (funext (by simpa using h))
  rw [Polynomial.IsRoot, Matrix.eval_charpoly]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v := z)
  · simp [Matrix.sub_mulVec, Matrix.smul_mulVec, he]
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr hi

private lemma deleted_eigenvector {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] (H : Matrix n n K) (μ : K) (z : n → K) (j : n)
    (hz : z ≠ 0) (he : H *ᵥ z = μ • z) (hj : z j = 0) :
    (H.submatrix (Subtype.val : {i : n // i ≠ j} → n) Subtype.val).charpoly.IsRoot μ := by
  classical
  let y : {i : n // i ≠ j} → K := fun i => z i
  have hy : y ≠ 0 := by
    intro h
    apply hz
    funext i
    by_cases hi : i = j
    · simpa [hi] using hj
    · exact congrFun h ⟨i, hi⟩
  apply root_of_eigenvector _ μ y hy
  ext i
  have hs := Fintype.sum_subtype_add_sum_subtype (fun k : n => k ≠ j)
    (fun k => H i.val k * z k)
  have hzsum : (∑ k : {k : n // ¬ k ≠ j}, H i.val k * z k) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : k.val = j := by simpa using k.property
    simp [hk, hj]
  rw [hzsum, add_zero] at hs
  change (∑ k : {k : n // k ≠ j}, H i.val k.val * z k.val) = μ * z i.val
  rw [hs]
  exact congrFun he i.val

/-- Identity block monodromy forces a common root of the actual characteristic
polynomial and the actual principal minor at the fixed defect site. -/
private theorem defect_common_roots_of_block_power_one {K : Type*} [Field K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) (t μ : K)
    (monodromy : block r (2 + t - μ) (2 - t - μ) ^ m = 1) :
    (hamiltonian r m t).charpoly.IsRoot μ ∧
    (deleted r m t ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly.IsRoot μ := by
  obtain ⟨z, hz, he, hj, _⟩ := defect_nodal_of_block_power_one r m hr hm t μ monodromy
  exact ⟨root_of_eigenvector _ μ z hz he, deleted_eigenvector _ μ z _ hz he hj⟩


/-- Every interior periodic trace value produces a normalized eigenvector of the
actual defect model, at the same prescribed node. -/
private theorem defect_nodal_of_trace_cos {K : Type*} [Field K] [Algebra ℝ K]
    (r m k : ℕ) (hr : 3 ≤ r) (hk : 0 < k) (hkm : 2 * k < m) (t μ : K)
    (htrace : (discriminant r t).eval μ =
      algebraMap ℝ K (2 * Real.cos (2 * Real.pi * k / m))) :
    ∃ z : Fin (r * m) → K,
      z ≠ 0 ∧ hamiltonian r m t *ᵥ z = μ • z ∧
      z ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩ = 0 ∧
      z ⟨defectSite r m + 1, by have := defect_bounds r m hr (by omega); omega⟩ = 1 := by
  apply defect_nodal_of_block_power_one r m hr (by omega) t μ
  exact sl2_torsion_of_cos _
    (by simp [block, Matrix.det_mul, Matrix.det_pow, transfer_det]) m k hk hkm
    (by simpa only [discriminant_eval] using htrace)


set_option maxHeartbeats 1000000 in
-- Finite matrix and cycle-coordinate normalization uses this local proof budget.
/-- Each irreducible factor of the exact periodic trace product divides the
characteristic polynomial and the deleted-node principal minor of the same model. -/
private theorem trace_factor_divides_characteristic_and_minor {K : Type*} [Field K] [Algebra ℝ K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t : K) (π : Polynomial K)
    (hπ : Irreducible π) (hdiv : π ∣ traceFactors r m t) :
    π ∣ (hamiltonian r m t).charpoly ∧
    π ∣ (deleted r m t
      ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩).charpoly := by
  classical
  letI : Fact (Irreducible π) := ⟨hπ⟩
  let E := AdjoinRoot π
  let f : K →+* E := algebraMap K E
  let μ : E := AdjoinRoot.root π
  have hz : Polynomial.aeval μ (traceFactors r m t) = 0 := by
    rwa [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
  simp only [traceFactors, map_prod, map_sub, Polynomial.aeval_C] at hz
  obtain ⟨k, hkmem, hkzero⟩ := Finset.prod_eq_zero_iff.mp hz
  have hk := (Finset.mem_filter.mp hkmem).2
  have htrace : (discriminant r (f t)).eval μ =
      algebraMap ℝ E (2 * Real.cos (2 * Real.pi * k / m)) := by
    rw [sub_eq_zero] at hkzero
    rw [discriminant_eval]
    rw [Polynomial.aeval_def, discriminant_eval₂] at hkzero
    simpa only [f, ← IsScalarTower.algebraMap_apply ℝ K E] using hkzero
  have hb : block r (2 + f t - μ) (2 - f t - μ) ^ m = 1 :=
    sl2_torsion_of_cos _
      (by simp [block, Matrix.det_mul, Matrix.det_pow, transfer_det]) m k hk.1 hk.2
      (by simpa only [discriminant_eval] using htrace)
  have hroots := defect_common_roots_of_block_power_one r m hr (by omega) (f t) μ hb
  have hchar : Polynomial.aeval μ (hamiltonian r m t).charpoly = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      ← Matrix.charpoly_map, map_hamiltonian]
    exact hroots.1
  have hminor : Polynomial.aeval μ (deleted r m t
      ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩).charpoly = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map]
    have heq : (deleted r m t
        ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩).map f =
        deleted r m (f t)
        ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩ := by
      unfold deleted
      rw [← Matrix.submatrix_map, map_hamiltonian]
    rw [heq]
    exact hroots.2
  exact ⟨(AdjoinRoot.mk_eq_zero.mp ((AdjoinRoot.aeval_eq _).symm.trans hchar)),
    (AdjoinRoot.mk_eq_zero.mp ((AdjoinRoot.aeval_eq _).symm.trans hminor))⟩


/-- The monic gcd over the rational-function field descends faithfully to the
polynomial coefficient ring and divides both original bivariate polynomials there. -/
private theorem nodeFactor_descent (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ G : Polynomial (Polynomial ℝ), G.Monic ∧
      G.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) =
        nodeFactor r m hr hm (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) ∧
      G ∣ (hamiltonian r m (Polynomial.X : Polynomial ℝ)).charpoly ∧
      G ∣ (deleted r m (Polynomial.X : Polynomial ℝ)
        ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly := by
  classical
  let f := algebraMap (Polynomial ℝ) (RatFunc ℝ)
  let g := nodeFactor r m hr hm (f Polynomial.X)
  have hg := nodeFactor_monic r m hr hm (f Polynomial.X)
  have hd := nodeFactor_divides r m hr hm (f Polynomial.X)
  have hpmap : ((hamiltonian r m (Polynomial.X : Polynomial ℝ)).charpoly).map f =
      (hamiltonian r m (f Polynomial.X)).charpoly := by
    rw [← Matrix.charpoly_map, map_hamiltonian]
  obtain ⟨G, hG⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (RatFunc ℝ)
    (Matrix.charpoly_monic (hamiltonian r m (Polynomial.X : Polynomial ℝ)))
    (g := g) (by rw [hpmap]; exact hd.1)
  rw [hg.leadingCoeff, Polynomial.C_1, mul_one] at hG
  have hGmonic : G.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective (Polynomial ℝ) (RatFunc ℝ))
    rw [hG]
    exact hg
  refine ⟨G, hGmonic, hG, ?_, ?_⟩
  · apply (Matrix.charpoly_monic _).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc ℝ) hGmonic
    rw [hG, hpmap]
    exact hd.1
  · apply (Matrix.charpoly_monic _).dvd_of_fraction_map_dvd_fraction_map (K := RatFunc ℝ) hGmonic
    rw [hG, ← Matrix.charpoly_map]
    have hmap : (deleted r m (Polynomial.X : Polynomial ℝ)
        ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).map f =
        deleted r m (f Polynomial.X)
        ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩ := by
      unfold deleted
      rw [← Matrix.submatrix_map, map_hamiltonian]
    rw [hmap]
    exact hd.2

/-- Every monic irreducible factor of the specified periodic trace product
is a factor of the original monic nodal gcd. -/
private theorem trace_factor_divides_nodeFactor {K : Type*} [Field K] [Algebra ℝ K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t : K)
    (π : Polynomial K) (hπ : Irreducible π) (hdiv : π ∣ traceFactors r m t) :
    π ∣ nodeFactor r m hr (by omega) t := by
  classical
  obtain ⟨hp, hq⟩ := trace_factor_divides_characteristic_and_minor r m hr hm t π hπ hdiv
  exact dvd_normalize_iff.mpr (dvd_gcd hp hq)

/-- The descended monic gcd remains monic and divides the actual characteristic
polynomial and actual deleted-site minor at every real specialization. -/
private theorem nodeFactor_descent_specialization (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ G : Polynomial (Polynomial ℝ), G.Monic ∧
      G.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) =
        nodeFactor r m hr hm (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) ∧
      G ∣ (hamiltonian r m (Polynomial.X : Polynomial ℝ)).charpoly ∧
      G ∣ (deleted r m (Polynomial.X : Polynomial ℝ)
        ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly ∧
      ∀ t : ℝ, (G.map (Polynomial.evalRingHom t)).Monic ∧
        G.map (Polynomial.evalRingHom t) ∣ (hamiltonian r m t).charpoly ∧
        G.map (Polynomial.evalRingHom t) ∣ (deleted r m t
          ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly := by
  classical
  obtain ⟨G, hG, hmap, hp, hq⟩ := nodeFactor_descent r m hr hm
  refine ⟨G, hG, hmap, hp, hq, fun t => ⟨hG.map _, ?_, ?_⟩⟩
  · have h := Polynomial.map_dvd (Polynomial.evalRingHom t) hp
    rw [← Matrix.charpoly_map, map_hamiltonian] at h
    simpa using h
  · have h := Polynomial.map_dvd (Polynomial.evalRingHom t) hq
    rw [← Matrix.charpoly_map] at h
    have heq : (deleted r m (Polynomial.X : Polynomial ℝ)
        ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).map
          (Polynomial.evalRingHom t) = deleted r m t
        ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩ := by
      unfold deleted
      rw [← Matrix.submatrix_map, map_hamiltonian]
      simp
    rw [heq] at h
    exact h

/-- At every complex coupling, every specified interior trace value is attained. -/
private lemma discriminant_attains (r : ℕ) (hr : 3 ≤ r) (t c : ℂ) :
    ∃ μ : ℂ, (discriminant r t).eval μ = c := by
  let s₁ := Polynomial.Chebyshev.S ℂ ((r - 1 : ℕ) : ℤ)
  let s₂ := Polynomial.Chebyshev.S ℂ ((r - 2 : ℕ) : ℤ)
  let P := s₁ * (Polynomial.X - Polynomial.C (2 * t)) - Polynomial.C 2 * s₂ - Polynomial.C c
  have h1 : s₁.natDegree = r - 1 := D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chebS_degree _
  have h2 : s₂.natDegree = r - 2 := D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chebS_degree _
  have h₁ : s₁ ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (show 0 < s₁.natDegree by omega)
  have hbig : (s₁ * (Polynomial.X - Polynomial.C (2 * t))).natDegree = r := by
    rw [Polynomial.natDegree_mul h₁ (Polynomial.X_sub_C_ne_zero _),
      Polynomial.natDegree_X_sub_C, h1]
    omega
  have hsmall : (Polynomial.C (2 : ℂ) * s₂).natDegree = r - 2 := by
    rw [Polynomial.natDegree_C_mul (by norm_num), h2]
  have hP : P.natDegree = r := by
    dsimp [P]
    rw [Polynomial.natDegree_sub_C,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt
        (show (Polynomial.C (2 : ℂ) * s₂).natDegree <
          (s₁ * (Polynomial.X - Polynomial.C (2 * t))).natDegree by omega), hbig]
  obtain ⟨x, hx⟩ := Complex.exists_root (f := P)
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega))
  refine ⟨2 + t - x, ?_⟩
  rw [discriminant_eval, block_trace r hr]
  have ha : 2 + t - (2 + t - x) = x := by ring
  have hb : 2 - t - (2 + t - x) = x - 2 * t := by ring
  rw [ha, hb]
  have hi1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  have hi2 : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
  have hh : (s₁.eval x * (x - 2 * t) - 2 * s₂.eval x) - c = 0 := by
    simpa only [Polynomial.IsRoot, P, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C] using hx
  dsimp [s₁, s₂] at hh
  rw [hi1, hi2] at hh
  linear_combination hh

/-- The same fixed site carries a nonzero eigenvector at every real coupling. -/
private theorem defect_nodal_every_real (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) :
    ∀ t : ℝ, ∃ (μ : ℂ) (z : Fin (r * m) → ℂ),
      z ≠ 0 ∧ hamiltonian r m (t : ℂ) *ᵥ z = μ • z ∧
      z ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩ = 0 ∧
      z ⟨defectSite r m + 1, by have := defect_bounds r m hr (by omega); omega⟩ = 1 := by
  intro t
  obtain ⟨μ, hμ⟩ := discriminant_attains r hr (t : ℂ)
    (algebraMap ℝ ℂ (2 * Real.cos (2 * Real.pi * (1 : ℕ) / m)))
  obtain ⟨z, hz⟩ := defect_nodal_of_trace_cos r m 1 hr (by omega) (by omega) (t : ℂ) μ hμ
  exact ⟨μ, z, hz⟩

/-- The persistent nodal spectrum at the prescribed site has real eigenvalues
and real normalized eigenvectors at every real coupling. -/
private theorem defect_real_nodal (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) :
    ∀ t : ℝ, ∃ (μ : ℝ) (z : Fin (r * m) → ℝ),
      z ≠ 0 ∧ hamiltonian r m t *ᵥ z = μ • z ∧
      z ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩ = 0 ∧
      z ⟨defectSite r m + 1, by have := defect_bounds r m hr (by omega); omega⟩ = 1 := by
  classical
  intro t
  obtain ⟨μ, z, hz, he, hq, hn⟩ := defect_nodal_every_real r m hr hm t
  have hD : (Matrix.diagonal (signWord (K := ℂ) r m)).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    simp only [signWord]
    split_ifs <;> simp [isSelfAdjoint_iff]
  have hH : (hamiltonian r m (t : ℂ)).IsHermitian :=
    (SimpleGraph.isHermitian_lapMatrix ℂ _).add (hD.smul (by simp [isSelfAdjoint_iff]))
  have hroot := root_of_eigenvector _ μ z hz he
  rw [hH.charpoly_eq] at hroot
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at hroot
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  have hμ : μ = (hH.eigenvalues i : ℂ) := sub_eq_zero.mp hi
  rw [hμ] at he
  let y : Fin (r * m) → ℝ := fun j => (z j).re
  have hey : hamiltonian r m t *ᵥ y = hH.eigenvalues i • y := by
    have hmap := map_hamiltonian Complex.ofRealHom r m t
    change (hamiltonian r m t).map Complex.ofReal = hamiltonian r m (t : ℂ) at hmap
    have he' : (hamiltonian r m t).map Complex.ofReal *ᵥ z =
        (hH.eigenvalues i : ℂ) • z := by
      simpa only [hmap] using he
    ext j
    have hh := congrArg Complex.re (congrFun he' j)
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum,
      Pi.smul_apply, smul_eq_mul, y] using hh
  have hyn : y ⟨defectSite r m + 1,
      by have := defect_bounds r m hr (by omega); omega⟩ = 1 := by
    simpa [y] using congrArg Complex.re hn
  have hyq : y ⟨defectSite r m,
      by have := defect_bounds r m hr (by omega); omega⟩ = 0 := by
    simpa [y] using congrArg Complex.re hq
  have hy : y ≠ 0 := by
    intro h
    have hh := congrFun h ⟨defectSite r m + 1,
      by have := defect_bounds r m hr (by omega); omega⟩
    rw [hyn] at hh
    exact one_ne_zero hh
  exact ⟨hH.eigenvalues i, y, hy, hey, hyq, hyn⟩

/-- Badness is the original Anderson predicate, for every real coupling. -/
private theorem defect_bad (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) :
    D5.S3.Combinatorics.Graph.AndersonSymmetryConverseRefutation.bad
      (signWord (K := ℝ) r m) := by
  intro t h
  obtain ⟨μ, z, hz, he, hq, _⟩ := defect_nodal_every_real r m hr hm t
  have hw : (fun j => ((signWord r m j : ℝ) : ℂ)) = signWord r m := by
    funext j
    simp only [signWord]
    split_ifs <;> simp
  rw [hw] at h
  exact h.2 μ z hz he _ hq

private lemma rational_discriminant_degree (r : ℕ) (hr : 3 ≤ r) (t : RatFunc ℝ) :
    (discriminant r t).natDegree = r := by
  let K := RatFunc ℝ
  let a : Polynomial K := Polynomial.C (2 + t) - Polynomial.X
  let b : Polynomial K := Polynomial.C (2 - t) - Polynomial.X
  let s₁ := Polynomial.Chebyshev.S K ((r : ℤ) - 1)
  let s₂ := Polynomial.Chebyshev.S K ((r : ℤ) - 2)
  have ha : a.natDegree = 1 := by
    have he : a = -(Polynomial.X - Polynomial.C (2 + t)) := by dsimp [a]; ring
    rw [he,Polynomial.natDegree_neg,Polynomial.natDegree_X_sub_C]
  have hb : b.natDegree = 1 := by
    have he : b = -(Polynomial.X - Polynomial.C (2 - t)) := by dsimp [b]; ring
    rw [he,Polynomial.natDegree_neg,Polynomial.natDegree_X_sub_C]
  have hs1 : (s₁.comp a).natDegree = r - 1 := by
    rw [Polynomial.natDegree_comp,ha,mul_one]
    have he : (r : ℤ) - 1 = ((r - 1 : ℕ) : ℤ) := by omega
    dsimp [s₁]
    rw [he]
    exact D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chebS_degree _
  have hs2 : (s₂.comp a).natDegree = r - 2 := by
    rw [Polynomial.natDegree_comp,ha,mul_one]
    have he : (r : ℤ) - 2 = ((r - 2 : ℕ) : ℤ) := by omega
    dsimp [s₂]
    rw [he]
    exact D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chebS_degree _
  have heq : discriminant r t = s₁.comp a * b - Polynomial.C 2 * s₂.comp a := by
    apply Polynomial.funext
    intro x
    rw [discriminant_eval, block_trace r hr]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_comp,
      Polynomial.eval_C,a,b,s₁,s₂,Polynomial.eval_X]
    ring
  rw [heq]
  have hbig : (s₁.comp a * b).natDegree = r := by
    rw [Polynomial.natDegree_mul
      (Polynomial.ne_zero_of_natDegree_gt (show 0 < (s₁.comp a).natDegree by omega))
      (Polynomial.ne_zero_of_natDegree_gt (show 0 < b.natDegree by omega)),hs1,hb]
    omega
  have hsmall : (Polynomial.C (2 : K) * s₂.comp a).natDegree = r - 2 := by
    rw [Polynomial.natDegree_C_mul (by norm_num),hs2]
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by omega),hbig]

private lemma trace_has_monic_irreducible (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m)
    (t : RatFunc ℝ) : ∃ π : Polynomial (RatFunc ℝ),
      π.Monic ∧ Irreducible π ∧ π ∣ traceFactors r m t := by
  classical
  let f := discriminant r t - Polynomial.C (algebraMap ℝ (RatFunc ℝ)
    (2 * Real.cos (2 * Real.pi * (1 : ℕ) / m)))
  have hf : f.natDegree = r := by rw [Polynomial.natDegree_sub_C,rational_discriminant_degree r hr]
  obtain ⟨π,hmon,hirr,hdiv⟩ := Polynomial.exists_monic_irreducible_factor f
    (Polynomial.not_isUnit_of_natDegree_pos f (by omega))
  refine ⟨π,hmon,hirr,hdiv.trans ?_⟩
  unfold traceFactors
  apply Finset.dvd_prod_of_mem
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

private lemma monic_factor_descent (G : Polynomial (Polynomial ℝ)) (hG : G.Monic)
    (π : Polynomial (RatFunc ℝ)) (hπ : π.Monic)
    (hd : π ∣ G.map (algebraMap (Polynomial ℝ) (RatFunc ℝ))) :
    ∃ Fπ : Polynomial (Polynomial ℝ), Fπ.Monic ∧
      Fπ.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) = π ∧ Fπ ∣ G := by
  obtain ⟨Fπ,hFπ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (RatFunc ℝ) hG hd
  rw [hπ.leadingCoeff, Polynomial.C_1, mul_one] at hFπ
  have hm : Fπ.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective (Polynomial ℝ) (RatFunc ℝ))
    rw [hFπ]
    exact hπ
  refine ⟨Fπ,hm,hFπ,?_⟩
  apply hG.dvd_of_fraction_map_dvd_fraction_map (K := RatFunc ℝ) hm
  rwa [hFπ]

/-- The full actual defect family: scalar complex common commutant, real
orthogonal symmetries only plus/minus identity, and, for m at least three,
badness, fixed-site real nodal spectrum, and faithful monic polynomial factors. -/
theorem defect_family (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    (∀ X : Matrix (Fin (r * m)) (Fin (r * m)) ℂ,
      Commute X (((SimpleGraph.cycleGraph (r * m)).lapMatrix ℝ).map Complex.ofReal) →
      Commute X ((Matrix.diagonal (signWord (K := ℝ) r m)).map Complex.ofReal) →
      ∃ c : ℂ, X = c • (1 : Matrix (Fin (r * m)) (Fin (r * m)) ℂ)) ∧
    (∀ O : Matrix (Fin (r * m)) (Fin (r * m)) ℝ,
      O ∈ Matrix.orthogonalGroup (Fin (r * m)) ℝ →
      Commute O ((SimpleGraph.cycleGraph (r * m)).lapMatrix ℝ) →
      Commute O (Matrix.diagonal (signWord r m)) → O = 1 ∨ O = -1) ∧
    (3 ≤ m →
      D5.S3.Combinatorics.Graph.AndersonSymmetryConverseRefutation.bad
        (signWord (K := ℝ) r m) ∧
      (∀ t : ℝ, ∃ (μ : ℝ) (z : Fin (r * m) → ℝ),
        z ≠ 0 ∧ hamiltonian r m t *ᵥ z = μ • z ∧
        z ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩ = 0 ∧
        z ⟨defectSite r m + 1, by have := defect_bounds r m hr hm; omega⟩ = 1) ∧
      (nodeFactor r m hr hm
        (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X)).Monic ∧
      ∃ G : Polynomial (Polynomial ℝ), G.Monic ∧
        G.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) =
          nodeFactor r m hr hm (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) ∧
        G ∣ (hamiltonian r m (Polynomial.X : Polynomial ℝ)).charpoly ∧
        G ∣ (deleted r m (Polynomial.X : Polynomial ℝ)
          ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly ∧
        (∀ t : ℝ, (G.map (Polynomial.evalRingHom t)).Monic ∧
          G.map (Polynomial.evalRingHom t) ∣ (hamiltonian r m t).charpoly ∧
          G.map (Polynomial.evalRingHom t) ∣ (deleted r m t
            ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly) ∧
        (∃ F : Polynomial (Polynomial ℝ), F.Monic ∧ 0 < F.natDegree ∧ F ∣ G) ∧
        ∀ π : Polynomial (RatFunc ℝ), π.Monic → Irreducible π →
          π ∣ traceFactors r m (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) →
          π ∣ nodeFactor r m hr hm (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) ∧
          ∃ Fπ : Polynomial (Polynomial ℝ), Fπ.Monic ∧
            Fπ.map (algebraMap (Polynomial ℝ) (RatFunc ℝ)) = π ∧ Fπ ∣ G ∧
            ∀ t : ℝ, (Fπ.map (Polynomial.evalRingHom t)).Monic ∧
              Fπ.map (Polynomial.evalRingHom t) ∣ (hamiltonian r m t).charpoly ∧
              Fπ.map (Polynomial.evalRingHom t) ∣ (deleted r m t
                ⟨defectSite r m, by have := defect_bounds r m hr hm; omega⟩).charpoly) := by
  classical
  have hL : 3 ≤ r * m := by nlinarith
  have hs := CycleDiagonalUnitPropagation.cycle_diagonal_units_full (r * m) hL
    (signWord r m) (defect_diagonal_seed r m hr hm)
  refine ⟨hs.2.1,hs.2.2,fun hm3 => ?_⟩
  obtain ⟨G,hG,hmap,hp,hq,hspec⟩ := nodeFactor_descent_specialization r m hr hm
  refine ⟨defect_bad r m hr hm3,defect_real_nodal r m hr hm3,
    nodeFactor_monic r m hr hm _,G,hG,hmap,hp,hq,hspec,?_,?_⟩
  · obtain ⟨π,hπ,hirr,hdiv⟩ := trace_has_monic_irreducible r m hr hm3
      (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X)
    have hd := trace_factor_divides_nodeFactor r m hr hm3
      (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) π hirr hdiv
    obtain ⟨F,hF,hFmap,hFdiv⟩ := monic_factor_descent G hG π hπ (by rwa [hmap])
    refine ⟨F,hF,?_,hFdiv⟩
    have he := hF.natDegree_map (algebraMap (Polynomial ℝ) (RatFunc ℝ))
    rw [hFmap] at he
    rw [← he]
    exact hπ.natDegree_pos_of_not_isUnit hirr.not_isUnit
  · intro π hπ hirr hdiv
    have hd := trace_factor_divides_nodeFactor r m hr hm3
      (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X) π hirr hdiv
    refine ⟨hd,?_⟩
    obtain ⟨Fπ,hFπ,hFπmap,hFπdiv⟩ := monic_factor_descent G hG π hπ (by rwa [hmap])
    refine ⟨Fπ,hFπ,hFπmap,hFπdiv,fun t => ⟨hFπ.map _,?_,?_⟩⟩
    · exact (Polynomial.map_dvd (Polynomial.evalRingHom t) hFπdiv).trans (hspec t).2.1
    · exact (Polynomial.map_dvd (Polynomial.evalRingHom t) hFπdiv).trans (hspec t).2.2

end D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
