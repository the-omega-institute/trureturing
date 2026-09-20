/- GID: D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/WeightedTensorConvolution
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: Quadratic weighted tensor convolution on the integer lattice has norm bound sixteen. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution

open scoped BigOperators

/-- The quadratic Fourier weight on the two-dimensional integer lattice. -/
def weight (k : ℤ × ℤ) : ℝ := 1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2

/-- The complex outer product, equipped with the Frobenius norm. -/
def outer (x y : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun ij => x ij.1 * y ij.2)

/-- The full-frequency coefficient convolution. -/
def convolution (a b : ℤ × ℤ → EuclideanSpace ℂ (Fin 2))
    (k : ℤ × ℤ) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  ∑' p, outer (a p) (b (k - p))

/-- Absolute coefficient convergence, weighted square summability, and the
quantitative tensor-product estimate for arbitrary quadratic-energy inputs. -/
theorem weighted_tensor_convolution
    (a b : ℤ × ℤ → EuclideanSpace ℂ (Fin 2))
    (ha : Summable (fun k => weight k ^ 2 * ‖a k‖ ^ 2))
    (hb : Summable (fun k => weight k ^ 2 * ‖b k‖ ^ 2)) :
    (∀ k, Summable (fun p => ‖outer (a p) (b (k - p))‖)) ∧
    Summable (fun k => weight k ^ 2 * ‖convolution a b k‖ ^ 2) ∧
    Real.sqrt (∑' k, weight k ^ 2 * ‖convolution a b k‖ ^ 2) ≤
      16 * Real.sqrt (∑' k, weight k ^ 2 * ‖a k‖ ^ 2) *
        Real.sqrt (∑' k, weight k ^ 2 * ‖b k‖ ^ 2) := by
  classical
  have hw (k : ℤ × ℤ) : 0 < weight k := by unfold weight; positivity
  have houter (x y : EuclideanSpace ℂ (Fin 2)) : ‖outer x y‖ = ‖x‖ * ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    simp only [EuclideanSpace.norm_sq_eq, outer, mul_pow, norm_mul,
      Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  let f : ℤ → ℝ := fun n => 1 / (1 + 2 * (n : ℝ) ^ 2)
  have hfpos (n : ℤ) : 0 ≤ f n := by dsimp [f]; positivity
  have hstep (n : ℕ) : f (n + 1) ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
    dsimp [f]
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    field_simp
    nlinarith
  have hpartial (N : ℕ) :
      ∑ n ∈ Finset.range N, f (n + 1) ≤ 1 - 1 / ((N : ℝ) + 1) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep N
      push_cast
      have hn : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
      rw [hn]
      linarith only [ih, hs]
  have hnat : Summable (fun n : ℕ => f (n + 1)) :=
    summable_of_sum_range_le (fun n => hfpos _) (fun N =>
      (hpartial N).trans (sub_le_self _ (by positivity)))
  have hnatle : (∑' n : ℕ, f (n + 1)) ≤ 1 :=
    hnat.tsum_le_of_sum_range_le (fun N =>
      (hpartial N).trans (sub_le_self _ (by positivity)))
  have hnatzero : Summable (fun n : ℕ => f n) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hnat
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    simpa only [f, Int.cast_neg, even_two, Even.neg_pow] using hnat
  have hf : Summable f := hnatzero.of_nat_of_neg_add_one hneg
  have hfle : (∑' n : ℤ, f n) ≤ 3 := by
    rw [tsum_of_nat_of_neg_add_one hnatzero hneg]
    have hz : 1 + (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, f n := by
      simpa only [Finset.sum_range_one, show f 0 = 1 by norm_num [f],
        Nat.cast_add, Nat.cast_one, Nat.cast_zero] using hnatzero.sum_add_tsum_nat_add 1
    have heven (n : ℤ) : f (-n) = f n := by simp [f]
    simp only [heven]
    linarith
  have hff := hf.mul_of_nonneg hf hfpos hfpos
  have hffle : (∑' k : ℤ × ℤ, f k.1 * f k.2) ≤ 9 := by
    rw [← hf.tsum_mul_tsum hf hff]
    have h0 : 0 ≤ ∑' n : ℤ, f n := tsum_nonneg hfpos
    nlinarith
  have hweight (k : ℤ × ℤ) : (weight k ^ 2)⁻¹ ≤ f k.1 * f k.2 := by
    have hden : (1 + 2 * (k.1 : ℝ) ^ 2) * (1 + 2 * (k.2 : ℝ) ^ 2) ≤
        weight k ^ 2 := by
      dsimp [weight]
      nlinarith [sq_nonneg ((k.1 : ℝ) ^ 2 - (k.2 : ℝ) ^ 2)]
    dsimp [f]
    rw [one_div_mul_one_div, one_div]
    exact inv_anti₀ (by positivity) hden
  have hws : Summable (fun k : ℤ × ℤ => (weight k ^ 2)⁻¹) :=
    hff.of_nonneg_of_le (fun _ => by positivity) hweight
  have hwle : (∑' k : ℤ × ℤ, (weight k ^ 2)⁻¹) ≤ 9 :=
    (hws.tsum_le_tsum hweight hff).trans hffle
  have hcs (u v : ℤ × ℤ → ℝ) (hu : ∀ p, 0 ≤ u p) (hv : ∀ p, 0 ≤ v p)
      (hus : Summable (fun p => u p ^ 2)) (hvs : Summable (fun p => v p ^ 2)) :
      Summable (fun p => u p * v p) ∧
      (∑' p, u p * v p) ^ 2 ≤ (∑' p, u p ^ 2) * (∑' p, v p ^ 2) := by
    have hfin (s : Finset (ℤ × ℤ)) : ∑ p ∈ s, u p * v p ≤
        Real.sqrt (∑' p, u p ^ 2) * Real.sqrt (∑' p, v p ^ 2) := by
      apply (Real.sum_mul_le_sqrt_mul_sqrt s u v).trans
      gcongr
      · exact hus.sum_le_tsum s (fun _ _ => sq_nonneg _)
      · exact hvs.sum_le_tsum s (fun _ _ => sq_nonneg _)
    have huv := summable_of_sum_le (fun p => mul_nonneg (hu p) (hv p)) hfin
    refine ⟨huv, ?_⟩
    calc
      (∑' p, u p * v p) ^ 2 ≤
          (Real.sqrt (∑' p, u p ^ 2) * Real.sqrt (∑' p, v p ^ 2)) ^ 2 := by
        exact pow_le_pow_left₀ (tsum_nonneg (fun p => mul_nonneg (hu p) (hv p)))
          (huv.tsum_le_of_sum_le hfin) 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _)),
        Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))]
  let A := fun k => weight k ^ 2 * ‖a k‖ ^ 2
  let B := fun k => weight k ^ 2 * ‖b k‖ ^ 2
  have hA (k : ℤ × ℤ) : 0 ≤ A k := by dsimp [A]; positivity
  have hB (k : ℤ × ℤ) : 0 ≤ B k := by dsimp [B]; positivity
  have hAB : Summable (fun pq : (ℤ × ℤ) × (ℤ × ℤ) => A pq.1 * B pq.2) :=
    ha.mul_of_nonneg hb hA hB
  let e : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) :=
    (Equiv.prodComm _ _).trans (Equiv.prodCongrRight (fun p => Equiv.subRight p))
  have hjoint : Summable (fun kp : (ℤ × ℤ) × (ℤ × ℤ) => A kp.2 * B (kp.1 - kp.2)) :=
    (e.summable_iff (f := fun pq : (ℤ × ℤ) × (ℤ × ℤ) => A pq.1 * B pq.2)).mpr hAB
  have hrow (k : ℤ × ℤ) := hjoint.prod_factor k
  have htotal : (∑' k, ∑' p, A p * B (k - p)) = (∑' p, A p) * ∑' p, B p := by
    rw [← hjoint.tsum_prod]
    exact (e.tsum_eq (fun pq => A pq.1 * B pq.2)).trans
      (ha.tsum_mul_tsum hb hAB).symm
  have hkernel (k p : ℤ × ℤ) :
      (weight k / (weight p * weight (k - p))) ^ 2 ≤
        8 * ((weight p ^ 2)⁻¹ + (weight (k - p) ^ 2)⁻¹) := by
    have htri : weight k ≤ 2 * (weight p + weight (k - p)) := by
      simp only [weight, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
      nlinarith [sq_nonneg ((k.1 : ℝ) - 2 * (p.1 : ℝ)),
        sq_nonneg ((k.2 : ℝ) - 2 * (p.2 : ℝ))]
    have hs : weight k ^ 2 ≤ 8 * (weight p ^ 2 + weight (k - p) ^ 2) := by
      have hh := pow_le_pow_left₀ (hw k).le htri 2
      nlinarith [sq_nonneg (weight p - weight (k - p))]
    rw [div_pow, mul_pow]
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos (hw p))
      (sq_pos_of_pos (hw (k - p))))).mpr
    field_simp [(hw p).ne', (hw (k - p)).ne']
    nlinarith
  have hks (k : ℤ × ℤ) :
      Summable (fun p => (weight k / (weight p * weight (k - p))) ^ 2) ∧
      (∑' p, (weight k / (weight p * weight (k - p))) ^ 2) ≤ 144 := by
    have ht : Summable (fun p => (weight (k - p) ^ 2)⁻¹) :=
      ((Equiv.subLeft k).summable_iff (f := fun p : ℤ × ℤ => (weight p ^ 2)⁻¹)).mpr hws
    have htval : (∑' p, (weight (k - p) ^ 2)⁻¹) =
        ∑' p, (weight p ^ 2)⁻¹ := (Equiv.subLeft k).tsum_eq (fun p => (weight p ^ 2)⁻¹)
    have hmaj := (hws.add ht).mul_left 8
    have hk := hmaj.of_nonneg_of_le (fun _ => sq_nonneg _) (hkernel k)
    refine ⟨hk, (hk.tsum_le_tsum (hkernel k) hmaj).trans ?_⟩
    rw [tsum_mul_left, hws.tsum_add ht, htval]
    linarith
  have hconv (k : ℤ × ℤ) :
      Summable (fun p => ‖outer (a p) (b (k - p))‖) ∧
      weight k ^ 2 * ‖convolution a b k‖ ^ 2 ≤ 144 * ∑' p, A p * B (k - p) := by
    let u := fun p => weight k / (weight p * weight (k - p))
    let v := fun p => weight p * ‖a p‖ * (weight (k - p) * ‖b (k - p)‖)
    have hv0 (p : ℤ × ℤ) : 0 ≤ v p :=
      mul_nonneg (mul_nonneg (hw p).le (norm_nonneg _))
        (mul_nonneg (hw (k - p)).le (norm_nonneg _))
    have hvsq (p : ℤ × ℤ) : v p ^ 2 = A p * B (k - p) := by dsimp [v, A, B]; ring
    have hvs : Summable (fun p => v p ^ 2) := (hrow k).congr (fun p => (hvsq p).symm)
    have hc := hcs u v (fun p => div_nonneg (hw k).le
      (mul_nonneg (hw p).le (hw (k - p)).le)) hv0 (hks k).1 hvs
    have hid (p : ℤ × ℤ) : u p * v p = weight k * ‖outer (a p) (b (k - p))‖ := by
      dsimp [u, v]
      rw [houter]
      field_simp [(hw p).ne', (hw (k - p)).ne']
    have hsum : Summable (fun p => ‖outer (a p) (b (k - p))‖) := by
      have hh := (hc.1.congr hid).mul_left (weight k)⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ (hw k).ne', one_mul] using hh
    refine ⟨hsum, ?_⟩
    calc
      weight k ^ 2 * ‖convolution a b k‖ ^ 2 ≤
          weight k ^ 2 * (∑' p, ‖outer (a p) (b (k - p))‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_tsum_le_tsum_norm hsum) 2
      _ = (∑' p, u p * v p) ^ 2 := by simp_rw [hid]; rw [tsum_mul_left, mul_pow]
      _ ≤ (∑' p, u p ^ 2) * (∑' p, v p ^ 2) := hc.2
      _ ≤ 144 * ∑' p, A p * B (k - p) := by
        simp_rw [hvsq]
        exact mul_le_mul_of_nonneg_right (hks k).2
          (tsum_nonneg (fun p => mul_nonneg (hA p) (hB (k - p))))
  have hout : Summable (fun k => weight k ^ 2 * ‖convolution a b k‖ ^ 2) :=
    (hjoint.prod.mul_left 144).of_nonneg_of_le (fun _ => by positivity) (fun k => (hconv k).2)
  refine ⟨fun k => (hconv k).1, hout, ?_⟩
  have henergy : (∑' k, weight k ^ 2 * ‖convolution a b k‖ ^ 2) ≤
      144 * (∑' p, A p) * ∑' p, B p := by
    have hh := hout.tsum_le_tsum (fun k => (hconv k).2) (hjoint.prod.mul_left 144)
    simpa only [tsum_mul_left, htotal, mul_assoc] using hh
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hEa : 0 ≤ ∑' p, A p := tsum_nonneg hA
    have hEb : 0 ≤ ∑' p, B p := tsum_nonneg hB
    change (∑' k, weight k ^ 2 * ‖convolution a b k‖ ^ 2) ≤
      (16 * Real.sqrt (∑' p, A p) * Real.sqrt (∑' p, B p)) ^ 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hEa, Real.sq_sqrt hEb]
    nlinarith [mul_nonneg hEa hEb]

#print axioms weighted_tensor_convolution

end D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
