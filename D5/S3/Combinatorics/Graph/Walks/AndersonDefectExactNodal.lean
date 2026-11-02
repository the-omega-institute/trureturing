/- GID: D5/S3/Combinatorics/Graph/Walks/AndersonDefectExactNodal
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/AndersonDefectExactNodal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual common roots satisfy the two periodic Chebyshev equations. -/

/-
proof_shape: symmetric_nodal_kernel, common_root_nodal, rotated_block_cyclic,
  nodal_fixed_state, common_root_trace_constraints: content.
proof_shape: rotated_entries, cycle_recurrence, rotated_evolution,
  chebyshev_common_root_cos: bind-only.
admission_basis: escape-witness (candidate, independent assessment pending).
escape_witness: zero extension and symmetry produce a nonzero nodal kernel
  vector; native cycle transport makes its rotated block state periodic;
  transcendence excludes a scalar block state. These facts are used in
  common_root_trace_constraints.
The bind-only helpers are used by rotated_block_cyclic, nodal_fixed_state
  and common_root_trace_constraints, respectively.
All declarations have utility kind none: they are general algebraic statements,
not bounded enumerations, checkers, numerical reductions or certified instances.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24624.
-/

import D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-! Common roots at the designated defect site satisfy periodic trace constraints. -/

set_option autoImplicit false
open Matrix
open scoped Fin.NatCast
open D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
open private sl2_power discriminant_eval periodic_evolution from D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily

namespace D5.S3.Combinatorics.Graph.Walks.AndersonDefectExactNodal

private theorem symmetric_nodal_kernel {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] (S : Matrix n n K) (hS : S.IsSymm) (j : n)
    (hd : S.det = 0)
    (hm : (S.submatrix (Subtype.val : {i : n // i ≠ j} → n) Subtype.val).det = 0) :
    ∃ z : n → K, z ≠ 0 ∧ S *ᵥ z = 0 ∧ z j = 0 := by
  classical
  obtain ⟨z, hz, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  by_cases hj : z j = 0
  · exact ⟨z, hz, he, hj⟩
  obtain ⟨w, hw, hminor⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hm
  let y : n → K := fun i => if hi : i ≠ j then w ⟨i, hi⟩ else 0
  have hyj : y j = 0 := by simp [y]
  have hy : y ≠ 0 := by
    intro h
    apply hw
    funext i
    have hh := congrFun h i.val
    simpa [y, i.property] using hh
  have haway (i : n) (hi : i ≠ j) : (S *ᵥ y) i = 0 := by
    have hh := congrFun hminor ⟨i, hi⟩
    have hsum := Fintype.sum_subtype_add_sum_subtype (fun k : n => k ≠ j)
      (fun k => S i k * y k)
    have hzero : (∑ k : {k : n // ¬ k ≠ j}, S i k * y k) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk : k.val = j := by simpa using k.property
      simp [hk, hyj]
    rw [hzero, add_zero] at hsum
    change (∑ k : n, S i k * y k) = 0
    rw [← hsum]
    have hyn (k : {k : n // k ≠ j}) : y k = w k := by simp [y, k.property]
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hyn, Pi.zero_apply] using hh
  have hsupport : S *ᵥ y = Pi.single j ((S *ᵥ y) j) := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [hi, haway i hi]
  have hdot : z j * (S *ᵥ y) j = 0 := by
    have hcomm := hS.dotProduct_mulVec_comm (x := z) (y := y)
    rw [he, dotProduct_zero, hsupport] at hcomm
    simpa [dotProduct, Pi.single_apply] using hcomm
  have hjzero : (S *ᵥ y) j = 0 := (mul_eq_zero.mp hdot).resolve_left hj
  refine ⟨y, hy, ?_, hyj⟩
  rw [hsupport, hjzero]
  simp

open D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
open D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily

private theorem common_root_nodal {K : Type*} [Field K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t μ : K)
    (hp : (hamiltonian r m t).charpoly.IsRoot μ)
    (hq : (deleted r m t ⟨defectSite r m,
      by have := defect_bounds r m hr (by omega); omega⟩).charpoly.IsRoot μ) :
    ∃ z : Fin (r * m) → K, z ≠ 0 ∧ hamiltonian r m t *ᵥ z = μ • z ∧
      z ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩ = 0 := by
  classical
  let j : Fin (r * m) := ⟨defectSite r m,
    by have := defect_bounds r m hr (by omega); omega⟩
  let H := hamiltonian r m t
  let S := μ • (1 : Matrix (Fin (r * m)) (Fin (r * m)) K) - H
  have hsym : S.IsSymm := (Matrix.isSymm_one.smul μ).sub
    ((SimpleGraph.isSymm_lapMatrix K _).add ((Matrix.isSymm_diagonal _).smul t))
  have hd : S.det = 0 := by
    simpa only [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal, S, H] using hp
  have hsub : S.submatrix (Subtype.val : {i : Fin (r * m) // i ≠ j} → Fin (r * m))
      Subtype.val = μ • 1 - deleted r m t j := by
    ext i k
    simp [S, H, deleted, Matrix.submatrix_apply, Matrix.one_apply,
      Subtype.ext_iff]
  have hmnr : (S.submatrix (Subtype.val : {i : Fin (r * m) // i ≠ j} → Fin (r * m))
      Subtype.val).det = 0 := by
    rw [hsub]
    simpa only [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] using hq
  obtain ⟨z, hz, he, hj⟩ := symmetric_nodal_kernel S hsym j hd hmnr
  refine ⟨z, hz, ?_, hj⟩
  change (μ • (1 : Matrix (Fin (r * m)) (Fin (r * m)) K) - H) *ᵥ z = 0 at he
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at he
  exact he.symm

private lemma rotated_entries {K : Type*} [Field K] (r : ℕ) (hr : 3 ≤ r) (a b : K) :
    let C := transfer a * transfer b * transfer a ^ (r - 2)
    let s := (Polynomial.Chebyshev.S K ((r : ℤ) - 2)).eval a
    let v := (Polynomial.Chebyshev.S K ((r : ℤ) - 3)).eval a
    C 1 0 = b * s - v ∧ C 0 0 = a * (b * s - v) - s := by
  dsimp only
  have hp := sl2_power (transfer a) (transfer_det a) (r - 2)
  have hi1 : ((r - 2 : ℕ) : ℤ) - 1 = (r : ℤ) - 3 := by omega
  have hi2 : ((r - 2 : ℕ) : ℤ) - 2 = (r : ℤ) - 4 := by omega
  rw [hi1, hi2] at hp
  have hs := congrArg (Polynomial.eval a) (Polynomial.Chebyshev.S_add_one K ((r : ℤ) - 3))
  have hi : (r : ℤ) - 3 + 1 = (r : ℤ) - 2 := by omega
  rw [hi] at hs
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at hs
  rw [hp]
  have hi3 : (r : ℤ) - 3 - 1 = (r : ℤ) - 4 := by omega
  rw [hi3] at hs
  simp [transfer, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]
  constructor
  · linear_combination -b * hs
  · linear_combination (1 - a * b) * hs

/-- At a transcendental coupling, a periodic state fixed after a whole number of
blocks cannot be a scalar state for the block through the prescribed defect. -/
private theorem rotated_block_cyclic {K : Type*} [Field K] [Algebra ℝ K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t μ : K)
    (ht : Transcendental ℝ t)
    (hfix : (transfer (2 + t - μ) * transfer (2 - t - μ) *
      transfer (2 + t - μ) ^ (r - 2)) ^ m *ᵥ ![1, 0] = ![1, 0]) :
    (transfer (2 + t - μ) * transfer (2 - t - μ) *
      transfer (2 + t - μ) ^ (r - 2)) 1 0 ≠ 0 := by
  classical
  let a := 2 + t - μ
  let b := 2 - t - μ
  let C := transfer a * transfer b * transfer a ^ (r - 2)
  let s := (Polynomial.Chebyshev.S K ((r : ℤ) - 2)).eval a
  let v := (Polynomial.Chebyshev.S K ((r : ℤ) - 3)).eval a
  change C 1 0 ≠ 0
  intro hzero
  have hc := rotated_entries r hr a b
  change C 1 0 = b * s - v ∧ C 0 0 = a * (b * s - v) - s at hc
  have hbs : b * s - v = 0 := hc.1.symm.trans hzero
  have he : C *ᵥ ![1, 0] = (-s) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc.1, hc.2, hbs]
  have hvec : Module.End.HasEigenvector C.toLin' (-s) ![1, 0] := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr he, ?_⟩
    intro h
    have := congrFun h 0
    simp at this
  have hp := hvec.pow_apply m
  rw [← Matrix.toLin'_pow] at hp
  change C ^ m *ᵥ ![1, 0] = (-s) ^ m • ![1, 0] at hp
  have hpower : (-s) ^ m = 1 := by
    have hh := congrFun (hp.symm.trans hfix) 0
    simpa using hh
  have hsalg : IsAlgebraic ℝ s := by
    have hpa : IsAlgebraic ℝ ((-s) ^ m) := by rw [hpower]; exact isAlgebraic_one
    simpa using (IsAlgebraic.of_pow (by omega : 0 < m) hpa).neg
  let P := Polynomial.Chebyshev.S ℝ ((r : ℤ) - 2)
  have hP : P.natDegree = r - 2 := by
    have hi : (r : ℤ) - 2 = ((r - 2 : ℕ) : ℤ) := by omega
    dsimp [P]
    rw [hi]
    exact D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chebS_degree _
  have haalg : IsAlgebraic ℝ a := by
    apply IsAlgebraic.of_aeval P (by omega : P.natDegree ≠ 0)
      (mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt (by omega : 0 < P.natDegree))))
    simpa only [P, Polynomial.Chebyshev.aeval_S] using hsalg
  have alg_eval (Q : Polynomial ℝ) : IsAlgebraic ℝ (Polynomial.aeval a Q) :=
    (Algebra.isAlgebraic_adjoin_singleton_iff.mpr haalg) _
      (Q.aeval_mem_adjoin_singleton ℝ a)
  have hvalg : IsAlgebraic ℝ v := by
    simpa only [Polynomial.Chebyshev.aeval_S] using
      alg_eval (Polynomial.Chebyshev.S ℝ ((r : ℤ) - 3))
  have hsne : s ≠ 0 := by
    intro h
    simp [h, show m ≠ 0 by omega] at hpower
  have hb : b = v * s⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hsne).mpr
    exact sub_eq_zero.mp hbs
  have hbalg : IsAlgebraic ℝ b := by
    rw [hb]
    exact hvalg.mul (IsAlgebraic.inv_iff.mpr hsalg)
  apply ht
  have htwo : (2 : K) ≠ 0 := by
    have hh := (algebraMap ℝ K).injective.ne (by norm_num : (2 : ℝ) ≠ 0)
    simpa only [map_ofNat, map_zero] using hh
  have hrel : t = (a - b) * (2 : K)⁻¹ := by
    dsimp [a, b]
    field_simp [htwo]
    ring
  rw [hrel]
  exact (haalg.sub hbalg).mul (IsAlgebraic.inv_iff.mpr (isAlgebraic_natCast 2))



private lemma cycle_recurrence {K : Type*} [Field K] (L : ℕ) (hL : 3 ≤ L)
    (v : Fin L → K) (t μ : K) (z : Fin L → K)
    (he : ((SimpleGraph.cycleGraph L).lapMatrix K + t • Matrix.diagonal v) *ᵥ z = μ • z) :
    ∀ i : Fin L, (2 + t * v i - μ) * z i =
      z (i - ⟨1, by omega⟩) + z (i + ⟨1, by omega⟩) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
  intro i
  have hone : (⟨1, by omega⟩ : Fin (n + 3)) = 1 := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < n + 3 by omega)]
  rw [hone]
  have hne : i - 1 ≠ i + 1 := by
    intro hh
    have htwo : (0 : Fin (n + 3)) = 2 := by
      calc
        0 = (i - 1) - (i - 1) := by simp
        _ = (i + 1) - (i - 1) := by rw [hh]
        _ = 2 := by
          simpa only [one_add_one_eq_two] using
            (show (i + 1) - (i - 1) = (1 : Fin (n + 3)) + 1 by abel)
    have hv := congrArg Fin.val htwo
    simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hv
  have hrow := congrFun he i
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_diagonal,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hrow
  rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.cycleGraph_degree_three_le,
    SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne] at hrow
  linear_combination hrow

private lemma rotated_evolution {K : Type*} [Field K] (r m : ℕ) (hr : 3 ≤ r)
    (a b : K) :
    evolution (fun i => if (i + 2) % r = 0 then b else a) (r * m) =
      (transfer a * transfer b * transfer a ^ (r - 2)) ^ m := by
  let d₀ : ℕ → K := fun i => if i % r = 0 then b else a
  let d : ℕ → K := fun i => if (i + 2) % r = 0 then b else a
  let E := transfer a * transfer b
  let C := transfer a * transfer b * transfer a ^ (r - 2)
  have base : evolution d₀ (r * m) = block r a b ^ m :=
    periodic_evolution r m (by omega) a b
  have start : evolution d₀ 2 = E := by
    simp [evolution, d₀, E, Nat.mod_eq_of_lt (by omega : 1 < r)]
  have shift₂ : (fun i => d₀ (2 + i)) = d := by
    funext i; simp only [d₀, d, Nat.add_comm]
  have shiftL : (fun i => d₀ (r * m + i)) = d₀ := by
    funext i; simp [d₀, Nat.add_mod]
  have first := evolution_add d₀ 2 (r * m)
  have last := evolution_add d₀ (r * m) 2
  rw [shift₂, start] at first
  rw [shiftL, start, base] at last
  have whole : evolution d (r * m) * E = E * block r a b ^ m := by
    calc
      _ = evolution d₀ (2 + r * m) := first.symm
      _ = evolution d₀ (r * m + 2) := by congr 1; omega
      _ = _ := last
  have intertwines : SemiconjBy E (block r a b) C := by
    change (transfer a * transfer b) * (transfer a ^ (r - 1) * transfer b) =
      (transfer a * transfer b * transfer a ^ (r - 2)) * (transfer a * transfer b)
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
    simp only [mul_assoc]
  have heq : evolution d (r * m) * E = C ^ m * E :=
    whole.trans (intertwines.pow_right m)
  have hinv : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by
    simp [E, Matrix.det_mul, transfer_det])
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M * E⁻¹) heq
  change evolution d (r * m) = C ^ m
  simpa only [mul_assoc, hinv, mul_one] using hh

/-- A nodal eigenvector of the actual cycle gives a fixed state for the rotated
periodic block, without replacing the principal minor by a path Laplacian. -/
private theorem nodal_fixed_state {K : Type*} [Field K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t μ : K)
    (z : Fin (r * m) → K) (hz : z ≠ 0)
    (he : hamiltonian r m t *ᵥ z = μ • z)
    (hnode : z ⟨defectSite r m,
      by have := defect_bounds r m hr (by omega); omega⟩ = 0) :
    (transfer (2 + t - μ) * transfer (2 - t - μ) *
      transfer (2 + t - μ) ^ (r - 2)) ^ m *ᵥ ![1, 0] = ![1, 0] := by
  classical
  let L := r * m
  have hL : 3 ≤ L := by dsimp [L]; nlinarith
  letI : NeZero L := ⟨by omega⟩
  let q := defectSite r m
  have hq : q + 1 < L := defect_bounds r m hr (by omega)
  let k : ℕ → Fin L := fun n => ((q + n : ℕ) : Fin L)
  let a := 2 + t - μ
  let b := 2 - t - μ
  let d : ℕ → K := fun n => if (n + 2) % r = 0 then b else a
  let y : ℕ → Fin 2 → K := fun n => ![z (k (n + 1)), z (k n)]
  have hnode' : z (k 0) = 0 := by
    convert hnode using 1
    apply congrArg z
    apply Fin.ext
    simp [k, q, Nat.mod_eq_of_lt (by omega : q < L)]
  have hrec (i : Fin L) :
      (2 + t * signWord r m i - μ) * z i = z (i - 1) + z (i + 1) := by
    have hh := cycle_recurrence L hL (signWord r m) t μ z he i
    have hone : (⟨1, by omega⟩ : Fin L) = 1 := by
      ext; simp [Nat.mod_eq_of_lt (by omega : 1 < L)]
    simpa only [hone] using hh
  have hstep (n : ℕ) : y (n + 1) = transfer (d n) *ᵥ y n := by
    have hrow := hrec (k (n + 1))
    have hprev : k (n + 1) - 1 = k n := by
      simp only [k, Nat.cast_add, Nat.cast_one]
      abel
    have hnext : k (n + 1) + 1 = k (n + 1 + 1) := by
      simp only [k, Nat.cast_add, Nat.cast_one]
      abel
    rw [hprev, hnext] at hrow
    have coeff : (2 + t * signWord r m (k (n + 1)) - μ) * z (k (n + 1)) =
        d n * z (k (n + 1)) := by
      by_cases hiq : (k (n + 1)).val = q
      · have hki : k (n + 1) = k 0 := by
          apply Fin.ext
          simpa [k, Nat.mod_eq_of_lt (by omega : q < L)] using hiq
        simp [hki, hnode']
      · have hmod : (k (n + 1)).val % r = (n + 2) % r := by
          change ((q + (n + 1)) % (r * m)) % r = _
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_right r m)]
          have hsum : q + (n + 1) = (m - 1) * r + (n + 2) := by
            dsimp [q, defectSite]; omega
          rw [hsum]
          simp [Nat.add_mod]
        have hiq' : (k (n + 1)).val ≠ defectSite r m := hiq
        simp only [signWord, hiq', or_false, hmod, d, a, b]
        split_ifs <;> ring
    rw [coeff] at hrow
    ext i
    fin_cases i <;> simp [y, transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -hrow
  have hy (n : ℕ) : y n = evolution d n *ᵥ y 0 := by
    induction n with
    | zero => simp [evolution]
    | succ n ih => rw [hstep, ih, evolution, Matrix.mulVec_mulVec]
  have hkL (n : ℕ) : k (L + n) = k n := by simp [k, Nat.cast_add]
  have hperiod : y L = y 0 := by
    ext i
    fin_cases i <;> simp [y, hkL, show k L = k 0 by simpa using hkL 0]
  have hnonzero : z (k 1) ≠ 0 := by
    intro hn
    have hy0 : y 0 = 0 := by ext i; fin_cases i <;> simp [y, hn, hnode']
    have hall (n : ℕ) : y n = 0 := by rw [hy, hy0, Matrix.mulVec_zero]
    apply hz
    funext i
    have hidx : k ((i - (q : Fin L)).val) = i := by
      simp only [k]
      simp
    have hh := congrFun (hall (i - (q : Fin L)).val) 1
    simpa [y, hidx] using hh
  have hy0 : y 0 = z (k 1) • ![1, 0] := by
    ext i; fin_cases i <;> simp [y, hnode']
  have hfix := (hy L).symm.trans hperiod
  rw [hy0, Matrix.mulVec_smul] at hfix
  have hcancel : evolution d L *ᵥ ![1, 0] = ![1, 0] := by
    exact (smul_right_injective _ hnonzero) hfix
  simpa only [L, d, rotated_evolution r m hr, a, b] using hcancel



private lemma chebyshev_common_root_cos {K : Type*} [Field K] [Algebra ℝ K]
    (m : ℕ) (hm : 3 ≤ m) (x : K)
    (h1 : (Polynomial.Chebyshev.S K ((m : ℤ) - 1)).eval x = 0)
    (h2 : (Polynomial.Chebyshev.S K ((m : ℤ) - 2)).eval x + 1 = 0) :
    ∃ k : ℕ, 0 < k ∧ 2 * k < m ∧
      x = algebraMap ℝ K (2 * Real.cos (2 * Real.pi * k / m)) := by
  classical
  let φ := algebraMap ℝ K
  letI : CharZero K := CharZero.of_addMonoidHom φ.toAddMonoidHom φ.map_one φ.injective
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let n := m - 1
  have hn : n + 1 = m := Nat.sub_add_cancel (by omega)
  have hi1 : (m : ℤ) - 1 = (n : ℤ) := by dsimp [n]; omega
  have hSU (j : ℤ) : (Polynomial.Chebyshev.S K j).eval x =
      (Polynomial.Chebyshev.U K j).eval (x / 2) := by
    rw [Polynomial.Chebyshev.S_eq_U_comp_half_mul_X]
    rw [Polynomial.eval_comp]
    congr 1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      invOf_eq_inv, div_eq_mul_inv]
    ring
  let P := Polynomial.Chebyshev.U ℝ (n : ℤ)
  have hcard : P.roots.card = P.natDegree := by
    dsimp [P]
    rw [Polynomial.Chebyshev.roots_U_real, ← Finset.card_def,
      Finset.card_image_of_injOn ((Finset.range n).nodup_map_iff_injOn.mp
        (Polynomial.Chebyshev.roots_U_real_nodup n)), Finset.card_range,
      Polynomial.Chebyshev.natDegree_U_natCast]
  have hmap : P.roots.map φ = (P.map φ).roots :=
    Polynomial.roots_map_of_injective_of_card_eq_natDegree φ.injective hcard
  have hP : P ≠ 0 := Polynomial.Chebyshev.U_ne_zero ℝ (n : ℤ) (by omega)
  have hzero : (P.map φ).eval (x / 2) = 0 := by
    simpa only [P, Polynomial.Chebyshev.map_U, ← hi1, ← hSU] using h1
  have hmem : x / 2 ∈ (P.map φ).roots :=
    (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff φ.injective).mpr hP)).mpr hzero
  rw [← hmap] at hmem
  obtain ⟨y, hy, hxy⟩ := Multiset.mem_map.mp hmem
  have hx : x = φ (2 * y) := by
    rw [map_mul, map_ofNat, hxy]
    field_simp
  have h2r : (Polynomial.Chebyshev.S ℝ ((m : ℤ) - 2)).eval (2 * y) + 1 = 0 := by
    apply φ.injective
    simp only [map_add, map_one, map_zero]
    change (algebraMap ℝ K)
      ((Polynomial.Chebyshev.S ℝ ((m : ℤ) - 2)).eval (2 * y)) + 1 = 0
    rw [Polynomial.Chebyshev.algebraMap_eval_S, ← hx]
    exact h2
  have hU1 : (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1)).eval y = 0 := by
    rw [hi1]
    exact (Polynomial.mem_roots hP).mp hy
  have hU2 : (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 2)).eval y + 1 = 0 := by
    simpa [Polynomial.Chebyshev.S_eq_U_comp_half_mul_X,
      Polynomial.eval_comp, invOf_eq_inv] using h2r
  have hT : (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y = 1 := by
    have hh := congrArg (Polynomial.eval y)
      (Polynomial.Chebyshev.T_eq_X_mul_U_sub_U ℝ ((m : ℤ) - 2))
    have hidx : (m : ℤ) - 2 + 2 = (m : ℤ) := by omega
    have hidx' : (m : ℤ) - 2 + 1 = (m : ℤ) - 1 := by omega
    rw [hidx, hidx'] at hh
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, hU1,
      mul_zero, zero_sub] at hh
    linarith
  obtain ⟨j, hj, hjeven, hyj⟩ :=
    (Polynomial.Chebyshev.eval_T_real_eq_one_iff (by omega : m ≠ 0) y).mp hT
  change y ∈ (Polynomial.Chebyshev.U ℝ (n : ℤ)).roots at hy
  rw [Polynomial.Chebyshev.roots_U_real] at hy
  obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp (show y ∈
    (Finset.range n).image (fun k : ℕ => Real.cos ((k + 1) * Real.pi / (n + 1))) from hy)
  have hi' : i + 1 < m := by have := Finset.mem_range.mp hi; omega
  have hnR : (n : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hn
  rw [hnR] at hiy
  have hθ : ((i : ℝ) + 1) * Real.pi / m = (j : ℝ) * Real.pi / m := by
    apply Real.injOn_cos
    · constructor
      · positivity
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < m)).mpr
        have hle : (i : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : i + 1 ≤ m)
        nlinarith [Real.pi_pos]
    · constructor
      · positivity
      · apply (div_le_iff₀ (by positivity : (0 : ℝ) < m)).mpr
        have hle : (j : ℝ) ≤ m := by exact_mod_cast hj
        nlinarith [Real.pi_pos]
    · exact hiy.trans hyj
  have hij : j = i + 1 := by
    have hmpos : (0 : ℝ) < m := by positivity
    have heq := (div_left_inj' (ne_of_gt hmpos)).mp hθ
    have heq' : (i : ℝ) + 1 = (j : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast heq'.symm
  obtain ⟨k, hk⟩ := hjeven
  refine ⟨k, by omega, by omega, ?_⟩
  rw [hx, hyj, hk]
  congr 2
  push_cast
  congr 1
  ring

/-- Every common root of the actual cycle characteristic polynomial and the
actual principal minor obeys both periodic Chebyshev equations. -/
theorem common_root_trace_constraints {K : Type*} [Field K] [Algebra ℝ K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t μ : K)
    (ht : Transcendental ℝ t)
    (hp : (hamiltonian r m t).charpoly.IsRoot μ)
    (hq : (deleted r m t ⟨defectSite r m,
      by have := defect_bounds r m hr (by omega); omega⟩).charpoly.IsRoot μ) :
    (Polynomial.Chebyshev.S K ((m : ℤ) - 1)).eval ((discriminant r t).eval μ) = 0 ∧
    (Polynomial.Chebyshev.S K ((m : ℤ) - 2)).eval ((discriminant r t).eval μ) + 1 = 0 ∧
    (traceFactors r m t).IsRoot μ := by
  classical
  obtain ⟨z, hz, he, hnode⟩ := common_root_nodal r m hr hm t μ hp hq
  have hfix := nodal_fixed_state r m hr hm t μ z hz he hnode
  have hc := rotated_block_cyclic r m hr hm t μ ht hfix
  let a := 2 + t - μ
  let b := 2 - t - μ
  let C := transfer a * transfer b * transfer a ^ (r - 2)
  have hdet : C.det = 1 := by simp [C, Matrix.det_mul, Matrix.det_pow, transfer_det]
  have htrace : C.trace = (discriminant r t).eval μ := by
    rw [discriminant_eval]
    dsimp only [C, block]
    rw [Matrix.trace_mul_cycle, ← pow_succ]
    congr 2
    congr 1
    omega
  have hpower := sl2_power C hdet m
  change C ^ m *ᵥ ![1, 0] = ![1, 0] at hfix
  change C 1 0 ≠ 0 at hc
  rw [hpower] at hfix
  have hsecond := congrFun hfix 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.smul_apply] at hsecond
  have hs : (Polynomial.Chebyshev.S K ((m : ℤ) - 1)).eval C.trace = 0 :=
    hsecond.resolve_right hc
  have hfirst := congrFun hfix 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.smul_apply, hs] at hfirst
  rw [← htrace]
  have hs2 : (Polynomial.Chebyshev.S K ((m : ℤ) - 2)).eval C.trace + 1 = 0 := by
    linear_combination -hfirst
  refine ⟨hs, hs2, ?_⟩
  obtain ⟨k, hkpos, hkm, hk⟩ := chebyshev_common_root_cos m hm C.trace hs hs2
  change (traceFactors r m t).eval μ = 0
  change (Polynomial.evalRingHom μ)
    (∏ k ∈ (Finset.range m).filter (fun k => 0 < k ∧ 2 * k < m),
      (discriminant r t - Polynomial.C (algebraMap ℝ K
        (2 * Real.cos (2 * Real.pi * k / m))))) = 0
  rw [map_prod]
  apply Finset.prod_eq_zero (i := k)
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hkpos, hkm⟩
  · change (discriminant r t - Polynomial.C (algebraMap ℝ K
      (2 * Real.cos (2 * Real.pi * k / m)))).eval μ = 0
    simp only [Polynomial.eval_sub, Polynomial.eval_C]
    rw [← htrace, hk, sub_self]

end D5.S3.Combinatorics.Graph.Walks.AndersonDefectExactNodal
