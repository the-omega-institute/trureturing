/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ThreeBlockGram
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace comparison from three positive spectral Gram blocks. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import D5.S3.Quantum.Analysis.RefinedBMVThreeSpectralValues
import Batteries.Tactic.OpenPrivate

/-!
# Three positive Gram blocks for the four-copy comparison

The reduction uses PSD compressions of the second factor indexed by three
spectral labels. It allows empty fibers and arbitrary spectral multiplicities.
The coefficients are the unnormalized four-slot deficits of
`FourCopyGap`. The three block orders are (0,1,2), (0,2,1), (1,2,0).
-/

noncomputable section

set_option maxHeartbeats 1000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.ThreeBlockGram

open FourCopyGap
open private monomial balanced gapDefect_diagonal gaps_card_pos trace_mul_nonneg_of_posSemidef
  trace_mask_product contract diagonal_gap_scaled eigenDiagonal rootDiagonal wordMean_conjugation
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Kernel := Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ

/-- The three adjacent transpositions generate permutation symmetry of the
scalar four-slot deficit. -/
theorem gapDefect_swap01 (p : ℕ) (a b c d : ℝ) :
    gapDefect p a b c d = gapDefect p b a c d := by
  have hs : (∑ q ∈ gaps p, monomial a b c d q) =
      ∑ q ∈ gaps p, monomial b a c d q := by
    let e (q : Gap) : Gap := (q.2.1, q.1, q.2.2.1, q.2.2.2)
    apply Finset.sum_nbij' e e
    · intro q hq
      simp only [mem_gaps, e] at hq ⊢
      omega
    · intro q hq
      simp only [mem_gaps, e] at hq ⊢
      omega
    · intro q _
      rcases q with ⟨i,j,k,l⟩
      rfl
    · intro q _
      rcases q with ⟨i,j,k,l⟩
      rfl
    · intro q _
      simp only [monomial, e]
      ring
  unfold gapDefect
  rw [hs]
  congr 1
  unfold balanced
  ring

theorem gapDefect_swap12 (p : ℕ) (a b c d : ℝ) :
    gapDefect p a b c d = gapDefect p a c b d := by
  have hs : (∑ q ∈ gaps p, monomial a b c d q) =
      ∑ q ∈ gaps p, monomial a c b d q := by
    let e (q : Gap) : Gap := (q.1, q.2.2.1, q.2.1, q.2.2.2)
    apply Finset.sum_nbij' e e
    · intro q hq
      simp only [mem_gaps, e] at hq ⊢
      omega
    · intro q hq
      simp only [mem_gaps, e] at hq ⊢
      omega
    · intro q _
      rcases q with ⟨i,j,k,l⟩
      rfl
    · intro q _
      rcases q with ⟨i,j,k,l⟩
      rfl
    · intro q _
      simp only [monomial, e]
      ring
  unfold gapDefect
  rw [hs]
  congr 1
  unfold balanced
  ring

theorem gapDefect_swap23 (p : ℕ) (a b c d : ℝ) :
    gapDefect p a b c d = gapDefect p a b d c := by
  have hs : (∑ q ∈ gaps p, monomial a b c d q) =
      ∑ q ∈ gaps p, monomial a b d c q := by
    let e (q : Gap) : Gap := (q.1, q.2.1, q.2.2.2, q.2.2.1)
    apply Finset.sum_nbij' e e
    · intro q hq
      simp only [mem_gaps, e] at hq ⊢
      omega
    · intro q hq
      simp only [mem_gaps, e] at hq ⊢
      omega
    · intro q _
      rcases q with ⟨i,j,k,l⟩
      rfl
    · intro q _
      rcases q with ⟨i,j,k,l⟩
      rfl
    · intro q _
      simp only [monomial, e]
      ring
  unfold gapDefect
  rw [hs]
  congr 1
  unfold balanced
  ring

/-- Pure triples, double pairs and repeated-label triangle deficits. -/
def f (d : Kernel) (i j : Fin 3) : ℝ := d i i i j

def g (d : Kernel) (i j : Fin 3) : ℝ := d i i j j

def h (d : Kernel) (i j k : Fin 3) : ℝ := d i i j k

/-- The real symmetric coefficient block on order (i,j,k), regarded as complex
for pairing against Hilbert–Schmidt Gram matrices. -/
def gramBlock (d : Kernel) (alloc : Fin 3 → Fin 3 → ℝ) (i j k : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![(f d i j : ℂ), (g d i j : ℂ) / 2, (alloc i j : ℂ);
    (g d i j : ℂ) / 2, (f d j i : ℂ), (alloc j i : ℂ);
    (alloc i j : ℂ), (alloc j i : ℂ), (h d k i j : ℂ)]

/-- The exact cyclic trace, with its complex value. -/
def trace4 (X : Fin 3 → Matrix n n ℂ) (i j k l : Fin 3) : ℂ :=
  trace (X i * X j * X k * X l)

theorem trace4_rotate (X : Fin 3 → Matrix n n ℂ) (i j k l : Fin 3) :
    trace4 X i j k l = trace4 X j k l i := by
  simpa only [trace4, mul_assoc] using trace_mul_comm (X i) (X j * X k * X l)

/-- The complete rotation orbit enumeration. There are three orbits of size
one, three of size two, and eighteen of size four. The six oriented triangle
orbits are retained individually. -/
theorem enumerate_cycles (w : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ)
    (hr : ∀ i j k l, w i j k l = w j k l i) :
    (∑ i, ∑ j, ∑ k, ∑ l, w i j k l) =
      w 0 0 0 0 + w 1 1 1 1 + w 2 2 2 2 +
      4 * (w 0 0 0 1 + w 0 0 0 2 + w 0 1 1 1 +
        w 1 1 1 2 + w 0 2 2 2 + w 1 2 2 2) +
      4 * (w 0 0 1 1 + w 0 0 2 2 + w 1 1 2 2) +
      2 * (w 0 1 0 1 + w 0 2 0 2 + w 1 2 1 2) +
      4 * (w 0 1 0 2 + w 0 1 2 1 + w 0 2 1 2) +
      4 * (w 0 0 1 2 + w 0 0 2 1 + w 0 1 1 2 +
        w 0 2 1 1 + w 0 1 2 2 + w 0 2 2 1) := by
  simp only [Fin.sum_univ_three]
  -- Every rule rotates a nonrepresentative word toward its least rotation.
  simp only [hr 0 0 1 0, hr 0 0 2 0, hr 0 1 0 0, hr 0 1 1 0,
      hr 0 1 2 0, hr 0 2 0 0, hr 0 2 0 1, hr 0 2 1 0,
      hr 0 2 2 0, hr 1 0 0 0, hr 1 0 0 1, hr 1 0 0 2,
      hr 1 0 1 0, hr 1 0 1 1, hr 1 0 1 2, hr 1 0 2 0,
      hr 1 0 2 1, hr 1 0 2 2, hr 1 1 0 0, hr 1 1 0 1,
      hr 1 1 0 2, hr 1 1 1 0, hr 1 1 2 0, hr 1 1 2 1,
      hr 1 2 0 0, hr 1 2 0 1, hr 1 2 0 2, hr 1 2 1 0,
      hr 1 2 1 1, hr 1 2 2 0, hr 1 2 2 1, hr 2 0 0 0,
      hr 2 0 0 1, hr 2 0 0 2, hr 2 0 1 0, hr 2 0 1 1,
      hr 2 0 1 2, hr 2 0 2 0, hr 2 0 2 1, hr 2 0 2 2,
      hr 2 1 0 0, hr 2 1 0 1, hr 2 1 0 2, hr 2 1 1 0,
      hr 2 1 1 1, hr 2 1 1 2, hr 2 1 2 0, hr 2 1 2 1,
      hr 2 1 2 2, hr 2 2 0 0, hr 2 2 0 1, hr 2 2 0 2,
      hr 2 2 1 0, hr 2 2 1 1, hr 2 2 1 2, hr 2 2 2 0,
      hr 2 2 2 1]
  ring

/-- The Gram contraction over the ordered labels (i,j,k). -/
def gramContraction (X : Fin 3 → Matrix n n ℂ) (i j k : Fin 3)
    (G : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  ∑ u, ∑ v, G u v * trace4 X i (![i,j,k] u) j (![i,j,k] v)

/-- The Gram contraction is nonnegative for any positive compressions and
any PSD coefficient block. Its Gram vectors are the entries of
`sqrt (X i) * X (![i,j,k] u) * sqrt (X j)`. -/
theorem gramContraction_nonneg (X : Fin 3 → Matrix n n ℂ)
    (hX : ∀ i, (X i).PosSemidef) (i j k : Fin 3)
    (G : Matrix (Fin 3) (Fin 3) ℂ) (hG : G.PosSemidef) :
    0 ≤ gramContraction X i j k G := by
  let S := CFC.sqrt (X i)
  let T := CFC.sqrt (X j)
  have hS : S * S = X i := CFC.sqrt_mul_sqrt_self _ (hX i).nonneg
  have hT : T * T = X j := CFC.sqrt_mul_sqrt_self _ (hX j).nonneg
  have hs : Sᴴ = S := (CFC.sqrt_nonneg (X i)).posSemidef.isHermitian.eq
  have ht : Tᴴ = T := (CFC.sqrt_nonneg (X j)).posSemidef.isHermitian.eq
  let q : Fin 3 → Fin 3 := ![i,j,k]
  let V (u : Fin 3) := S * X (q u) * T
  let W : Matrix (n × n) (Fin 3) ℂ := fun ab u ↦ V u ab.1 ab.2
  have hv (u v : Fin 3) :
      trace (V u * (V v)ᴴ) = trace4 X i (q u) j (q v) := by
    calc
      _ = trace (S * (X (q u) * (X j * (X (q v) * S)))) := by
        simp only [V, conjTranspose_mul, hs, ht, (hX (q v)).isHermitian.eq]
        rw [← hT]
        simp only [mul_assoc]
      _ = _ := by
        rw [trace_mul_comm S]
        simp only [trace4, mul_assoc, hS]
        simpa only [mul_assoc] using
          trace_mul_comm (X (q u) * (X j * X (q v))) (X i)
  have hk (u v : Fin 3) : (Wᴴ * W) v u = trace4 X i (q u) j (q v) := by
    rw [← hv]
    change (∑ ab : n × n, star (V v ab.1 ab.2) * V u ab.1 ab.2) =
      ∑ a : n, ∑ b : n, V u a b * star (V v a b)
    rw [Fintype.sum_prod_type]
    simp only [mul_comm]
  have heq : gramContraction X i j k G = trace (G * (Wᴴ * W)) := by
    simp only [gramContraction, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply (M := G) (N := Wᴴ * W), hk, q]
  rw [heq]
  exact trace_mul_nonneg_of_posSemidef hG (posSemidef_conjTranspose_mul_self W)

/-- The alternating two-label trace is the squared Hilbert–Schmidt norm
of the positive compression by the square root of X_i. -/
theorem alternating_nonneg (X : Fin 3 → Matrix n n ℂ)
    (hX : ∀ i, (X i).PosSemidef) (i j : Fin 3) :
    0 ≤ trace4 X i j i j := by
  let S := CFC.sqrt (X i)
  have hs : Sᴴ = S := (CFC.sqrt_nonneg (X i)).posSemidef.isHermitian.eq
  have hS : S * S = X i := CFC.sqrt_mul_sqrt_self _ (hX i).nonneg
  let D := S * X j * S
  have hD : D.PosSemidef := by
    simpa only [D, hs] using (hX j).mul_mul_conjTranspose_same S
  have htr : trace (Dᴴ * D) = trace4 X i j i j := by
    rw [hD.isHermitian.eq]
    calc
      _ = trace (S * (X j * (X i * (X j * S)))) := by
        rw [← hS]
        simp only [D, mul_assoc]
      _ = _ := by
        rw [trace_mul_comm S]
        simp only [trace4, mul_assoc, hS]
        simpa only [mul_assoc] using trace_mul_comm (X j * (X i * X j)) (X i)
  rw [← htr]
  exact (posSemidef_conjTranspose_mul_self D).trace_nonneg

/-- The full weighted cyclic trace sum. -/
def gapSum (d : Kernel) (X : Fin 3 → Matrix n n ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (d i j k l : ℂ) * trace4 X i j k l

/-- Exact algebraic contraction, with no sign assumption on individual
triangle traces. The row sums account for both orientations of each triangle. -/
theorem gapSum_eq_grams (d : Kernel) (X : Fin 3 → Matrix n n ℂ)
    (alloc : Fin 3 → Fin 3 → ℝ)
    (h01 : ∀ i j k l, d i j k l = d j i k l)
    (h12 : ∀ i j k l, d i j k l = d i k j l)
    (h23 : ∀ i j k l, d i j k l = d i j l k)
    (hd : ∀ i, d i i i i = 0)
    (hr0 : alloc 0 1 + alloc 0 2 = h d 0 1 2)
    (hr1 : alloc 1 0 + alloc 1 2 = h d 1 0 2)
    (hr2 : alloc 2 0 + alloc 2 1 = h d 2 0 1) :
    gapSum d X =
      4 * (gramContraction X 0 1 2 (gramBlock d alloc 0 1 2) +
        gramContraction X 0 2 1 (gramBlock d alloc 0 2 1) +
        gramContraction X 1 2 0 (gramBlock d alloc 1 2 0)) +
      2 * ((g d 0 1 : ℂ) * trace4 X 0 1 0 1 +
        (g d 0 2 : ℂ) * trace4 X 0 2 0 2 +
        (g d 1 2 : ℂ) * trace4 X 1 2 1 2) := by
  have hw (i j k l : Fin 3) :
      (d i j k l : ℂ) * trace4 X i j k l =
        (d j k l i : ℂ) * trace4 X j k l i := by
    rw [trace4_rotate X i j k l, h01 i j k l, h12 j i k l, h23 j k i l]
  unfold gapSum
  rw [enumerate_cycles (fun i j k l ↦ (d i j k l : ℂ) * trace4 X i j k l) hw]
  simp only [gramContraction, gramBlock, f, g, h, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.of_apply,
    hd, Complex.ofReal_zero, zero_mul, zero_add]
  simp only [h] at hr0 hr1 hr2
  -- Sort the scalar indices using adjacent transpositions.
  simp only [h01 1 0 0 0, h01 1 0 0 1, h01 1 0 0 2, h01 1 0 1 0,
      h01 1 0 1 1, h01 1 0 1 2, h01 1 0 2 0, h01 1 0 2 1,
      h01 1 0 2 2, h01 2 0 0 0, h01 2 0 0 1, h01 2 0 0 2,
      h01 2 0 1 0, h01 2 0 1 1, h01 2 0 1 2, h01 2 0 2 0,
      h01 2 0 2 1, h01 2 0 2 2, h01 2 1 0 0, h01 2 1 0 1,
      h01 2 1 0 2, h01 2 1 1 0, h01 2 1 1 1, h01 2 1 1 2,
      h01 2 1 2 0, h01 2 1 2 1, h01 2 1 2 2, h12 0 1 0 0,
      h12 0 1 0 1, h12 0 1 0 2, h12 0 2 0 0, h12 0 2 0 1,
      h12 0 2 0 2, h12 0 2 1 0, h12 0 2 1 1, h12 0 2 1 2,
      h12 1 1 0 0, h12 1 1 0 1, h12 1 1 0 2, h12 1 2 0 0,
      h12 1 2 0 1, h12 1 2 0 2, h12 1 2 1 0, h12 1 2 1 1,
      h12 1 2 1 2, h12 2 1 0 0, h12 2 1 0 1, h12 2 1 0 2,
      h12 2 2 0 0, h12 2 2 0 1, h12 2 2 0 2, h12 2 2 1 0,
      h12 2 2 1 1, h12 2 2 1 2, h23 0 0 1 0, h23 0 0 2 0,
      h23 0 0 2 1, h23 0 1 1 0, h23 0 1 2 0, h23 0 1 2 1,
      h23 0 2 1 0, h23 0 2 2 0, h23 0 2 2 1, h23 1 0 1 0,
      h23 1 0 2 0, h23 1 0 2 1, h23 1 1 1 0, h23 1 1 2 0,
      h23 1 1 2 1, h23 1 2 1 0, h23 1 2 2 0, h23 1 2 2 1,
      h23 2 0 1 0, h23 2 0 2 0, h23 2 0 2 1, h23 2 1 1 0,
      h23 2 1 2 0, h23 2 1 2 1, h23 2 2 1 0, h23 2 2 2 0,
      h23 2 2 2 1] at hr0 hr1 hr2 ⊢
  -- Put each trace at the least cyclic rotation as in enumerate_cycles.
  simp only [trace4_rotate X 0 0 1 0, trace4_rotate X 0 0 2 0, trace4_rotate X 0 1 0 0, trace4_rotate X 0 1 1 0,
      trace4_rotate X 0 1 2 0, trace4_rotate X 0 2 0 0, trace4_rotate X 0 2 0 1, trace4_rotate X 0 2 1 0,
      trace4_rotate X 0 2 2 0, trace4_rotate X 1 0 0 0, trace4_rotate X 1 0 0 1, trace4_rotate X 1 0 0 2,
      trace4_rotate X 1 0 1 0, trace4_rotate X 1 0 1 1, trace4_rotate X 1 0 1 2, trace4_rotate X 1 0 2 0,
      trace4_rotate X 1 0 2 1, trace4_rotate X 1 0 2 2, trace4_rotate X 1 1 0 0, trace4_rotate X 1 1 0 1,
      trace4_rotate X 1 1 0 2, trace4_rotate X 1 1 1 0, trace4_rotate X 1 1 2 0, trace4_rotate X 1 1 2 1,
      trace4_rotate X 1 2 0 0, trace4_rotate X 1 2 0 1, trace4_rotate X 1 2 0 2, trace4_rotate X 1 2 1 0,
      trace4_rotate X 1 2 1 1, trace4_rotate X 1 2 2 0, trace4_rotate X 1 2 2 1, trace4_rotate X 2 0 0 0,
      trace4_rotate X 2 0 0 1, trace4_rotate X 2 0 0 2, trace4_rotate X 2 0 1 0, trace4_rotate X 2 0 1 1,
      trace4_rotate X 2 0 1 2, trace4_rotate X 2 0 2 0, trace4_rotate X 2 0 2 1, trace4_rotate X 2 0 2 2,
      trace4_rotate X 2 1 0 0, trace4_rotate X 2 1 0 1, trace4_rotate X 2 1 0 2, trace4_rotate X 2 1 1 0,
      trace4_rotate X 2 1 1 1, trace4_rotate X 2 1 1 2, trace4_rotate X 2 1 2 0, trace4_rotate X 2 1 2 1,
      trace4_rotate X 2 1 2 2, trace4_rotate X 2 2 0 0, trace4_rotate X 2 2 0 1, trace4_rotate X 2 2 0 2,
      trace4_rotate X 2 2 1 0, trace4_rotate X 2 2 1 1, trace4_rotate X 2 2 1 2, trace4_rotate X 2 2 2 0,
      trace4_rotate X 2 2 2 1]
  rw [← hr0, ← hr1, ← hr2]
  push_cast
  ring

/-- Transfer from the three scalar PSD blocks to the full matrix contraction. -/
theorem gapSum_nonneg (d : Kernel) (X : Fin 3 → Matrix n n ℂ)
    (hX : ∀ i, (X i).PosSemidef) (alloc : Fin 3 → Fin 3 → ℝ)
    (h01 : ∀ i j k l, d i j k l = d j i k l)
    (h12 : ∀ i j k l, d i j k l = d i k j l)
    (h23 : ∀ i j k l, d i j k l = d i j l k)
    (hd : ∀ i, d i i i i = 0)
    (hn : ∀ i j, 0 ≤ g d i j)
    (hr0 : alloc 0 1 + alloc 0 2 = h d 0 1 2)
    (hr1 : alloc 1 0 + alloc 1 2 = h d 1 0 2)
    (hr2 : alloc 2 0 + alloc 2 1 = h d 2 0 1)
    (hG01 : (gramBlock d alloc 0 1 2).PosSemidef)
    (hG02 : (gramBlock d alloc 0 2 1).PosSemidef)
    (hG12 : (gramBlock d alloc 1 2 0).PosSemidef) :
    0 ≤ gapSum d X := by
  rw [gapSum_eq_grams d X alloc h01 h12 h23 hd hr0 hr1 hr2]
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg (add_nonneg
      (gramContraction_nonneg X hX 0 1 2 _ hG01)
      (gramContraction_nonneg X hX 0 2 1 _ hG02))
      (gramContraction_nonneg X hX 1 2 0 _ hG12)))
    (mul_nonneg (by norm_num) (add_nonneg (add_nonneg
      (mul_nonneg (Complex.zero_le_real.mpr (hn 0 1)) (alternating_nonneg X hX 0 1))
      (mul_nonneg (Complex.zero_le_real.mpr (hn 0 2)) (alternating_nonneg X hX 0 2)))
      (mul_nonneg (Complex.zero_le_real.mpr (hn 1 2)) (alternating_nonneg X hX 1 2))))

/-- The actual four-slot scalar kernel of the word mean. -/
def spectralDefect (p : ℕ) (x : Fin 3 → ℝ) : Kernel :=
  fun i j k l ↦ gapDefect p (x i) (x j) (x k) (x l)

/-- The six allocated coefficients, row sums and three PSD conditions. -/
def Allocation (d : Kernel) (alloc : Fin 3 → Fin 3 → ℝ) : Prop :=
  (alloc 0 1 + alloc 0 2 = h d 0 1 2) ∧
  (alloc 1 0 + alloc 1 2 = h d 1 0 2) ∧
  (alloc 2 0 + alloc 2 1 = h d 2 0 1) ∧
  (gramBlock d alloc 0 1 2).PosSemidef ∧
  (gramBlock d alloc 0 2 1).PosSemidef ∧
  (gramBlock d alloc 1 2 0).PosSemidef

theorem spectral_gapSum_nonneg (p : ℕ) (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (X : Fin 3 → Matrix n n ℂ) (hX : ∀ i, (X i).PosSemidef)
    (alloc : Fin 3 → Fin 3 → ℝ) (hAlloc : Allocation (spectralDefect p x) alloc) :
    0 ≤ gapSum (spectralDefect p x) X := by
  obtain ⟨hr0, hr1, hr2, hG01, hG02, hG12⟩ := hAlloc
  exact gapSum_nonneg _ X hX alloc
    (fun i j k l ↦ gapDefect_swap01 p (x i) (x j) (x k) (x l))
    (fun i j k l ↦ gapDefect_swap12 p (x i) (x j) (x k) (x l))
    (fun i j k l ↦ gapDefect_swap23 p (x i) (x j) (x k) (x l))
    (fun i ↦ gapDefect_diagonal p (x i) (hx i))
    (fun i j ↦ gapDefect_nonneg p (hx i) (hx i) (hx j) (hx j))
    hr0 hr1 hr2 hG01 hG02 hG12

/-- Compress the spectral mask through the positive square root of B. -/
def compression (label : n → Fin 3) (B : Matrix n n ℂ) (i : Fin 3) :
    Matrix n n ℂ :=
  CFC.sqrt B * spectralMask label i * CFC.sqrt B

theorem compression_posSemidef (label : n → Fin 3) (B : Matrix n n ℂ)
    (i : Fin 3) : (compression label B i).PosSemidef := by
  have hP : (spectralMask label i).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro a
    change 0 ≤ (if label a = i then 1 else 0 : ℂ)
    split <;> simp
  have hS := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  simpa only [compression, hS.eq] using hP.mul_mul_conjTranspose_same (CFC.sqrt B)

theorem compression_trace4 (label : n → Fin 3) (B : Matrix n n ℂ)
    (hB : B.PosSemidef) (i j k l : Fin 3) :
    trace4 (compression label B) i j k l = cycleTrace (spectralBlock label B) i j k l := by
  rw [← trace_mask_product label B]
  let S := CFC.sqrt B
  let P := spectralMask label
  have hS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  change trace ((S * P i * S) * (S * P j * S) * (S * P k * S) * (S * P l * S)) =
    trace ((P i * B) * (P j * B) * (P k * B) * (P l * B))
  calc
    _ = trace (S * (P i * (B * (P j * (B * (P k * (B * (P l * S)))))))) := by
      rw [← hS]
      simp only [mul_assoc]
    _ = _ := by
      rw [trace_mul_comm S]
      simp only [mul_assoc, hS]

/-- Transfer to the actual ordered-word mean in an eigenbasis. -/
theorem diagonal_bound (p : ℕ) (label : n → Fin 3) (x : Fin 3 → ℝ)
    (hx : ∀ i, 0 ≤ x i) (B : Matrix n n ℂ) (hB : B.PosSemidef)
    (alloc : Fin 3 → Fin 3 → ℝ) (hAlloc : Allocation (spectralDefect p x) alloc) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤ FourCopyGap.wordMean p (eigenDiagonal label x) B := by
  have hn := spectral_gapSum_nonneg p x hx (compression label B)
    (compression_posSemidef label B) alloc hAlloc
  have heq : gapSum (spectralDefect p x) (compression label B) =
      ((gaps p).card : ℂ) *
        (FourCopyGap.wordMean p (eigenDiagonal label x) B - trace ((rootDiagonal label x p * B) ^ 4)) := by
    rw [diagonal_gap_scaled]
    simp only [gapSum, spectralDefect, compression_trace4 label B hB,
      contract, LinearMap.coe_mk, AddHom.coe_mk]
  rw [heq] at hn
  have hc : (0 : ℝ) < (gaps p).card := by exact_mod_cast gaps_card_pos p
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hre),
    (sub_eq_zero.mp ((mul_eq_zero.mp him.symm).resolve_left hc.ne')).symm⟩

/-- The full three-spectrum refined BMV four-copy product comparison under the
three PSD block certificate. A label map for the eigenvalues permits arbitrary
multiplicity, and the three labels need not all occur. -/
theorem product_bound (p : ℕ) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i) (label : n → Fin 3)
    (hlabel : ∀ a, hA.isHermitian.eigenvalues a = x (label a))
    (alloc : Fin 3 → Fin 3 → ℝ) (hAlloc : Allocation (spectralDefect p x) alloc) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  let H := hA.isHermitian
  let U := H.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ _ (star U)
  have hd : φ A = eigenDiagonal label x := by
    rw [H.conjStarAlgAut_star_eigenvectorUnitary]
    congr 1
    funext a
    exact congrArg Complex.ofReal (hlabel a)
  have hB' : (φ B).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have hr : φ (A ^ ((p : ℝ) / 4)) = rootDiagonal label x p := by
    rw [CFC.rpow_eq_cfc_real hA.nonneg, H.cfc_eq, Matrix.IsHermitian.cfc]
    have hf : φ.symm = Unitary.conjStarAlgAut ℂ _ U := by simp [φ]
    change φ (Unitary.conjStarAlgAut ℂ _ U _) = _
    rw [← hf, StarAlgEquiv.apply_symm_apply]
    congr 1
    funext a
    change ((H.eigenvalues a ^ ((p : ℝ) / 4) : ℝ) : ℂ) =
      ((x (label a) ^ ((p : ℝ) / 4) : ℝ) : ℂ)
    rw [hlabel a]
  have hm : FourCopyGap.wordMean p (eigenDiagonal label x) (φ B) = FourCopyGap.wordMean p A B := by
    rw [← hd]
    exact wordMean_conjugation p (star U) A B
  have ht : trace ((rootDiagonal label x p * φ B) ^ 4) =
      trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) := by
    rw [← hr, ← map_mul φ, ← map_pow φ]
    exact trace_conjugation (star U) _
  simpa only [ht, hm] using diagonal_bound p label x hx (φ B) hB' alloc hAlloc

/-- A spectrum contained in the chosen three values, with unrestricted
multiplicities, inherits the same Gram certificate. -/
theorem product_bound_of_spectrum_subset (p : ℕ) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (x : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hspectrum : ∀ a, ∃ i, hA.isHermitian.eigenvalues a = x i)
    (alloc : Fin 3 → Fin 3 → ℝ) (hAlloc : Allocation (spectralDefect p x) alloc) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  classical
  exact product_bound p A B hA hB x hx
    (fun a ↦ Classical.choose (hspectrum a))
    (fun a ↦ Classical.choose_spec (hspectrum a)) alloc hAlloc

#print axioms enumerate_cycles
#print axioms gapSum_eq_grams
#print axioms gramContraction_nonneg
#print axioms product_bound

end RefinedBMV.ThreeBlockGram
