/- GID: D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniConverseWIP
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Complex path contractions and the all-order cluster readouts. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The four-party complex contraction and finite rank arguments for arXiv:2611.27660v1. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniConverseWIP

open Matrix
open scoped BigOperators Matrix

abbrev Bits := Fin 4 → Fin 2
abbrev BitPair := Fin 2 × Fin 2

def cluster (s : Bits) : ℚ :=
  if s 0 = s 1 ∧ s 2 = s 3 then
    if s 0 = 1 ∧ s 2 = 1 then -(1 / 2) else 1 / 2
  else 0

private def setPair (a b : Fin 4) (x y : Fin 2) (s : Bits) : Bits :=
  fun i => if i = a then x else if i = b then y else s i

/-- The normalized complex cluster amplitude. -/
noncomputable def clusterState (s : Bits) : ℂ := cluster s

abbrev Coordinate {D : ℕ} (d : Fin D → ℕ) := (i : Fin D) → Fin (d i)

abbrev Tensor {D : ℕ} (d : Fin D → ℕ) := Coordinate d → ℂ

abbrev Wire {D : ℕ} (d : Fin D → ℕ) (i : Fin D) := Fin (d i) × Fin (d i)

abbrev qubits : Fin 4 → ℕ := fun _ => 2

theorem positiveQubits : ∀ i, 0 < qubits i := fun _ => Nat.zero_lt_succ _

private def fill {D : ℕ} {d : Fin D → ℕ} (a b : Fin D)
    (x : Fin (d a)) (y : Fin (d b)) (z : Coordinate d) : Coordinate d :=
  fun i => if h : i = a then h.symm ▸ x else if h : i = b then h.symm ▸ y else z i

/-- One column pair contributes the reduced density of its two incident strand colors. -/
noncomputable def marginalEntry {D : ℕ} {d : Fin D → ℕ} (hd : ∀ i, 0 < d i)
    (ψ : Tensor d) (a b : Fin D) (p : Wire d a) (q : Wire d b) : ℂ :=
  ∑ z : Coordinate d, if z a = ⟨0, hd a⟩ ∧ z b = ⟨0, hd b⟩ then
    ψ (fill a b p.1 q.1 z) * star (ψ (fill a b p.2 q.2 z))
  else 0

private noncomputable def pairedVertices (ψ : Bits → ℂ) (a b : Fin 4)
    (p q : BitPair) (z : Bits) : ℂ :=
  if z a = 0 ∧ z b = 0 then
    ψ (setPair a b p.1 q.1 z) * star (ψ (setPair a b p.2 q.2 z))
  else 0

/-- The two-color marginal for four qubits. -/
noncomputable def pairEntryCRaw (ψ : Bits → ℂ) (a b : Fin 4) (p q : BitPair) : ℂ :=
  ∑ z : Bits, pairedVertices ψ a b p q z

private theorem fill_four (a b : Fin 4) (x y : Fin 2) (z : Bits) :
    fill (d := qubits) a b x y z = setPair a b x y z := by
  funext i
  by_cases ha : i = a
  · subst i
    simp [fill, setPair]
  · by_cases hb : i = b
    · subst i
      simp [fill, setPair, ha]
    · simp [fill, setPair, ha, hb]

theorem marginalEntry_four (ψ : Bits → ℂ) (a b : Fin 4) (p q : BitPair) :
    marginalEntry positiveQubits ψ a b p q = pairEntryCRaw ψ a b p q := by
  unfold marginalEntry pairEntryCRaw pairedVertices
  simp only [fill_four]
  rfl

/-- Eq. (24) for four qubits. The three spectator assignments label the parallel internal
edges within the three vertex pairs. The two bit pairs label the edges across adjacent
pairs. The middle white vertex is on the other strand. The input is ket–dual and
the output is dual–ket. Each summand contains all six vertex amplitudes. -/
noncomputable def graphEntry (ψ : Bits → ℂ) (a b c d : Fin 4) (out input : BitPair) : ℂ :=
  ∑ x : BitPair, ∑ y : BitPair, ∑ w : Bits, ∑ u : Bits, ∑ v : Bits,
    pairedVertices ψ a b input x u *
      pairedVertices ψ b c x.swap y.swap v * pairedVertices ψ c d y out.swap w

theorem graphEntry_eq_marginal_chain (ψ : Bits → ℂ) (a b c d : Fin 4) (out input : BitPair) :
    graphEntry ψ a b c d out input =
      ∑ x : BitPair, ∑ y : BitPair,
        pairEntryCRaw ψ a b input x * pairEntryCRaw ψ b c x.swap y.swap *
          pairEntryCRaw ψ c d y out.swap := by
  simp only [graphEntry, pairEntryCRaw]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]


def pairEntry (a b : Fin 4) (p q : BitPair) : ℚ :=
  ∑ z : Bits, if z a = 0 ∧ z b = 0 then
    cluster (setPair a b p.1 q.1 z) * cluster (setPair a b p.2 q.2 z)
  else 0

def pairEntryC (a b : Fin 4) (p q : BitPair) : ℂ := (pairEntry a b p q : ℂ)

def pairTable (a b : Fin 4) (p q : BitPair) : ℚ :=
  if a.val / 2 = b.val / 2 then
    if p = q ∧ p.1 = p.2 then 1 / 2 else 0
  else if p.1 = p.2 ∧ q.1 = q.2 then 1 / 4 else 0

def rationalContraction (a b c d : Fin 4) (out input : BitPair) : ℚ :=
  ∑ x : BitPair, ∑ y : BitPair,
    pairEntry a b input x * pairEntry b c x.swap y.swap * pairEntry c d y out.swap

def complexContraction (a b c d : Fin 4) (out input : BitPair) : ℂ :=
  ∑ x : BitPair, ∑ y : BitPair,
    pairEntryC a b input x * pairEntryC b c x.swap y.swap * pairEntryC c d y out.swap

def corners (scale : ℚ) (out input : BitPair) : ℚ :=
  if out.1 = out.2 ∧ input.1 = input.2 then scale else 0

def Distinct (a b c d : Fin 4) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

instance (a b c d : Fin 4) : Decidable (Distinct a b c d) := by
  unfold Distinct
  infer_instance

private theorem pairEntryC_cast (a b : Fin 4) (p q : BitPair) :
    pairEntryCRaw clusterState a b p q = (pairEntry a b p q : ℂ) := by
  simp only [pairEntryCRaw, pairedVertices, pairEntry, clusterState, star_ratCast]
  change _ = (Rat.castHom ℂ) _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs
  · exact (map_mul (Rat.castHom ℂ) _ _).symm
  · simp

private theorem pair_check :
    ∀ (a b : Fin 4) (p q : BitPair), a ≠ b →
      pairEntry a b p q = pairTable a b p q := by
  decide +kernel

private theorem path_check :
    ∀ (a b c d : Fin 4) (out input : BitPair), Distinct a b c d →
      (∑ x : BitPair, ∑ y : BitPair,
        pairTable a b input x * pairTable b c x.swap y.swap *
          pairTable c d y out.swap) =
        corners (1 / 16) out input := by
  decide +kernel

theorem rationalContraction_eq (a b c d : Fin 4) (out input : BitPair)
    (h : Distinct a b c d) :
    rationalContraction a b c d out input = corners (1 / 16) out input := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  simpa only [rationalContraction, pair_check _ _ _ _ hab, pair_check _ _ _ _ hbc,
    pair_check _ _ _ _ hcd] using
      path_check a b c d out input ⟨hab, hac, had, hbc, hbd, hcd⟩

theorem complexContraction_eq (a b c d : Fin 4) (out input : BitPair)
    (h : Distinct a b c d) :
    complexContraction a b c d out input =
      (corners (1 / 16) out input : ℂ) := by
  calc
    complexContraction a b c d out input =
        (Rat.castHom ℂ) (rationalContraction a b c d out input) := by
      simp only [complexContraction, rationalContraction, pairEntryC,
        map_sum, map_mul, Rat.coe_castHom]
    _ = _ := congrArg (Rat.castHom ℂ) (rationalContraction_eq a b c d out input h)

theorem cluster_graph_eq (a b c d : Fin 4) (out input : BitPair)
    (h : Distinct a b c d) :
    graphEntry clusterState a b c d out input = (corners (1 / 16) out input : ℂ) := by
  rw [graphEntry_eq_marginal_chain]
  simp_rw [pairEntryC_cast]
  exact complexContraction_eq a b c d out input h


theorem cluster_normalization : (∑ s : Bits, cluster s * cluster s) = 1 := by
  decide +kernel

theorem complex_gram : ∀ out input : BitPair,
    (∑ k : BitPair, (corners (1 / 16) out k : ℂ) *
      star (corners (1 / 16) input k : ℂ)) =
      (corners (1 / 128) out input : ℂ) := by
  intro out input
  fin_cases out <;> fin_cases input <;>
    norm_num [corners, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_product]

theorem complex_square : ∀ out input : BitPair,
    (∑ k : BitPair, (corners (1 / 128) out k : ℂ) *
      (corners (1 / 128) k input : ℂ)) =
      (1 / 64 : ℂ) * (corners (1 / 128) out input : ℂ) := by
  intro out input
  fin_cases out <;> fin_cases input <;>
    norm_num [corners, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_product]

private theorem power_succ_of_square {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (t : ℂ) (hsq : X * X = t • X) (k : ℕ) :
    X ^ (k + 1) = t ^ k • X := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ X (k + 1), ih, Matrix.smul_mul, hsq, smul_smul, pow_succ t k]

theorem logRatio_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (t : ℝ) (ht : t ≠ 0)
    (htrace : X.trace = (t : ℂ)) (hsq : X * X = (t : ℂ) • X) (k : ℕ) :
    -Real.log ((X ^ (k + 1)).trace.re / X.trace.re ^ (k + 1)) = 0 := by
  rw [power_succ_of_square X _ hsq, Matrix.trace_smul, smul_eq_mul, htrace,
    ← pow_succ, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re,
    div_self (pow_ne_zero _ ht), Real.log_one, neg_zero]

/-- The ordered contraction matrix has the two endpoint pairs as its column and row indices. -/
noncomputable def contraction (ψ : Bits → ℂ) (σ : Equiv.Perm (Fin 4)) :
    Matrix BitPair BitPair ℂ :=
  fun out input => graphEntry ψ (σ 0) (σ 1) (σ 2) (σ 3) out input

/-- Eq. (30) evaluated on the four-qubit contraction. -/
noncomputable def ordered (ψ : Bits → ℂ) (σ : Equiv.Perm (Fin 4)) (n : ℕ) : ℝ :=
  let A := contraction ψ σ
  let X := A * Aᴴ
  (-Real.log ((X ^ n).trace.re / X.trace.re ^ n))

/-- Eq. (31), with one term per permutation of the four colors. -/
noncomputable def averaged (ψ : Bits → ℂ) (n : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin 4), ordered ψ σ n) / (Nat.factorial 4 : ℝ)

theorem cluster_state_normalized : (∑ s : Bits, Complex.normSq (clusterState s)) = 1 := by
  have h := congrArg (Rat.castHom ℝ) cluster_normalization
  simpa only [clusterState, Complex.normSq_ratCast, map_sum, map_mul, map_one,
    Rat.coe_castHom] using h

theorem cluster_ordered_zero (σ : Equiv.Perm (Fin 4)) (n : ℕ) (hn : 2 ≤ n) :
    ordered clusterState σ n = 0 := by
  have hd : Distinct (σ 0) (σ 1) (σ 2) (σ 3) := by
    unfold Distinct
    simpa only [Ne, σ.injective.eq_iff] using
      (show (0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧
        (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3 from by decide)
  let X : Matrix BitPair BitPair ℂ := fun i j => (corners (1 / 128) i j : ℂ)
  have hgram : contraction clusterState σ * (contraction clusterState σ)ᴴ = X := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, contraction, cluster_graph_eq _ _ _ _ _ _ hd]
    exact complex_gram i j
  have ht : X.trace = ((1 / 64 : ℝ) : ℂ) := by
    norm_num [X, Matrix.trace, Matrix.diag, corners, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hs : X * X = ((1 / 64 : ℝ) : ℂ) • X := by
    ext i j
    change (∑ k, (corners (1 / 128) i k : ℂ) * (corners (1 / 128) k j : ℂ)) = _
    rw [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    exact complex_square i j
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa only [ordered, hgram] using logRatio_eq_zero X _ (by norm_num) ht hs k

theorem cluster_averaged_zero (n : ℕ) (hn : 2 ≤ n) : averaged clusterState n = 0 := by
  simp [averaged, cluster_ordered_zero _ n hn]

theorem prime_singleton_stripping {r : ℕ} (hprime : Nat.Prime r)
    {ι : Type*} [Fintype ι] (f : ι → ℕ) (hprod : ∏ i, f i = r) :
    ∃ i, f i = r ∧ ∀ j, j ≠ i → f j = 1 := by
  classical
  have hdiv (i : ι) : f i ∣ r := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hcases (i : ι) : f i = 1 ∨ f i = r :=
    hprime.eq_one_or_self_of_dvd _ (hdiv i)
  obtain ⟨i, hi⟩ : ∃ i, f i = r := by
    by_contra hnone
    have hall : ∀ i, f i = 1 := by
      intro i
      rcases hcases i with h | h
      · exact h
      · exact False.elim (hnone ⟨i, h⟩)
    have : (1 : ℕ) = r := by simpa [hall] using hprod
    exact hprime.ne_one this.symm
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hrest : (Finset.univ.erase i).prod f = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hprime.pos
    calc
      r * (Finset.univ.erase i).prod f =
          f i * (Finset.univ.erase i).prod f := by rw [hi]
      _ = ∏ k, f k := Finset.mul_prod_erase _ f (Finset.mem_univ i)
      _ = r * 1 := by simp [hprod]
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
  have hone := (Finset.prod_eq_one_iff.mp hrest)
  exact hone j hjmem

end D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniConverseWIP
