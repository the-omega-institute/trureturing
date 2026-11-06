/- GID: D5/S3/VertexAlgebra/Analysis/OriginalModeCommutator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalModeCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original lattice mode commutators in one Sobolev operator space. -/

import D5.S3.VertexAlgebra.Analysis.OriginalSmoothFields
import D5.S3.VertexAlgebra.LatticeActualChargedLocality
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-
   All spaces, modes, constants, and tests below are the original ones.
   Composition is transported only along equality of natural Sobolev orders.
   The delta convention is delta C m n = C (m+1) n - C m (n+1).
   This module supplies recurrence, growth, and the actual infinite-composition
   expansion; it contains no Newton, derivative, Fourier-product, or contact
   theorem. Mathlib's normed-operator and infinite-sum APIs are reused under
   their Apache 2.0 license. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology VertexOperator

namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing

open LatticeGeneratingFieldLocality
open LatticePositiveEnergy
open SmoothCircleFourier
open SmoothCircleFourier.Test
open Model

variable (M : Model)

/-- Equality transport of the source order; no inclusion or extra regularity. -/
def Model.castSource {i j k : ℕ} (h : i = j)
    (A : M.Sobolev i →L[ℂ] M.Sobolev k) :
    M.Sobolev j →L[ℂ] M.Sobolev k := h ▸ A

private theorem castSource_norm {i j k : ℕ} (h : i = j)
    (A : M.Sobolev i →L[ℂ] M.Sobolev k) :
    ‖M.castSource h A‖ = ‖A‖ := by
  cases h
  rfl

private theorem castSource_embed {i j k : ℕ} (h : i = j)
    (A : M.Sobolev i →L[ℂ] M.Sobolev k) (v : Carrier M.D) :
    M.castSource h A (M.embed j v) = A (M.embed i v) := by
  cases h
  rfl

private theorem castSource_smul {i j k : ℕ} (h : i = j)
    (c : ℂ) (A : M.Sobolev i →L[ℂ] M.Sobolev k) :
    M.castSource h (c • A) = c • M.castSource h A := by
  cases h
  rfl

private theorem castSource_tsum {ι : Type*} {i j k : ℕ} (h : i = j)
    (A : ι → M.Sobolev i →L[ℂ] M.Sobolev k) :
    M.castSource h (∑' p, A p) = ∑' p, M.castSource h (A p) := by
  cases h
  rfl

/-- A_a^k(m) A_b^(r+k)(n), with source s+(r+k) transported to r+s+k. -/
def Model.modeProduct (a b : Charge M.D) (k : ℕ) (m n : ℤ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  M.castSource (by omega : M.order b + (M.order a + k) =
    M.order a + M.order b + k)
    ((M.modeExtension a k m).comp (M.modeExtension b (M.order a + k) n))

/-- A_b^k(n) A_a^(s+k)(m), on exactly the same source as modeProduct. -/
def Model.reverseModeProduct (a b : Charge M.D) (k : ℕ) (m n : ℤ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  M.castSource (by omega : M.order a + (M.order b + k) =
    M.order a + M.order b + k)
    ((M.modeExtension b k n).comp (M.modeExtension a (M.order b + k) m))

/-- The original mode commutator C_k in B(H_(r+s+k),H_k). -/
def Model.modeCommutator (a b : Charge M.D) (k : ℕ) (m n : ℤ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  M.modeProduct a b k m n - M.reverseModeProduct a b k m n

theorem modeProduct_embed (a b : Charge M.D) (k : ℕ) (m n : ℤ)
    (v : Carrier M.D) :
    M.modeProduct a b k m n (M.embed (M.order a + M.order b + k) v) =
      M.embed k (M.mode a m (M.mode b n v)) := by
  rw [Model.modeProduct, castSource_embed]
  simp only [ContinuousLinearMap.comp_apply, modeExtension_embed]

theorem reverseModeProduct_embed (a b : Charge M.D) (k : ℕ) (m n : ℤ)
    (v : Carrier M.D) :
    M.reverseModeProduct a b k m n
        (M.embed (M.order a + M.order b + k) v) =
      M.embed k (M.mode b n (M.mode a m v)) := by
  rw [Model.reverseModeProduct, castSource_embed]
  simp only [ContinuousLinearMap.comp_apply, modeExtension_embed]

theorem modeCommutator_embed (a b : Charge M.D) (k : ℕ) (m n : ℤ)
    (v : Carrier M.D) :
    M.modeCommutator a b k m n (M.embed (M.order a + M.order b + k) v) =
      M.embed k (M.mode a m (M.mode b n v) - M.mode b n (M.mode a m v)) := by
  simp only [Model.modeCommutator, ContinuousLinearMap.sub_apply,
    modeProduct_embed, reverseModeProduct_embed, map_sub]

/-- A proved heterogeneous evaluation/translation bridge for every delta iterate.
    No endomorphism-specific delta-evaluation lemma is instantiated at B(H_R,H_k). -/
theorem modeCommutator_iterate_embed (a b : Charge M.D) (k j : ℕ) (m n : ℤ)
    (v : Carrier M.D) :
    (FieldNormalProductLocality.delta^[j] (M.modeCommutator a b k)) m n
        (M.embed (M.order a + M.order b + k) v) =
      M.embed k
        (((FieldNormalProductLocality.delta^[j]
          (FieldNormalProductLocality.commutator
            (LatticeGeneratingFieldLocality.actualField M.D a)
            (LatticeGeneratingFieldLocality.actualField M.D b)))
          (m + chargeEnergy M.D a - 1) (n + chargeEnergy M.D b - 1)) v) := by
  induction j generalizing m n with
  | zero =>
      simpa only [Function.iterate_zero_apply,
        FieldNormalProductLocality.commutator, LinearMap.sub_apply,
        Module.End.mul_apply, Model.mode] using modeCommutator_embed M a b k m n v
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [FieldNormalProductLocality.delta,
        ContinuousLinearMap.sub_apply, LinearMap.sub_apply, map_sub]
      rw [ih (m + 1) n, ih m (n + 1)]
      have hm : m + 1 + chargeEnergy M.D a - 1 =
          (m + chargeEnergy M.D a - 1) + 1 := by omega
      have hn : n + 1 + chargeEnergy M.D b - 1 =
          (n + chargeEnergy M.D b - 1) + 1 := by omega
      rw [hm, hn]

/-- Exact algebraic locality transferred by density, including exponent zero. -/
theorem modeCommutator_delta (a b : Charge M.D) (k : ℕ) :
    FieldNormalProductLocality.delta^[(-bilinear M.D a b).toNat]
      (M.modeCommutator a b k) = 0 := by
  funext m n
  apply ContinuousLinearMap.ext
  intro x
  refine (embed_dense M (M.order a + M.order b + k)).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro v
    rw [modeCommutator_iterate_embed,
      LatticeActualChargedLocality.actual_charged_charged_locality] <;> simp

/-- The first ordered product has the actual asymmetric mode bound. -/
theorem modeProduct_norm (a b : Charge M.D) (k : ℕ) (m n : ℤ) :
    ‖M.modeProduct a b k m n‖ ≤
      M.modeConstant a * M.modeConstant b *
        (1 + |(m : ℝ)|)^(M.order a + k) *
        (1 + |(n : ℝ)|)^(M.order a + M.order b + k) := by
  rw [Model.modeProduct, castSource_norm]
  have hCa := (modeConstant_pos M a).le
  calc
    _ ≤ ‖M.modeExtension a k m‖ * ‖M.modeExtension b (M.order a + k) n‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (M.modeConstant a * (1 + |(m : ℝ)|)^(M.order a + k)) *
        (M.modeConstant b * (1 + |(n : ℝ)|)^(M.order b + (M.order a + k))) :=
      mul_le_mul (modeExtension_norm M a k m)
        (modeExtension_norm M b (M.order a + k) n) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show M.order b + (M.order a + k) =
        M.order a + M.order b + k by omega]
      ring

/-- The second ordered product has the complementary asymmetric mode bound. -/
theorem reverseModeProduct_norm (a b : Charge M.D) (k : ℕ) (m n : ℤ) :
    ‖M.reverseModeProduct a b k m n‖ ≤
      M.modeConstant a * M.modeConstant b *
        (1 + |(m : ℝ)|)^(M.order a + M.order b + k) *
        (1 + |(n : ℝ)|)^(M.order b + k) := by
  rw [Model.reverseModeProduct, castSource_norm]
  have hCb := (modeConstant_pos M b).le
  calc
    _ ≤ ‖M.modeExtension b k n‖ * ‖M.modeExtension a (M.order b + k) m‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (M.modeConstant b * (1 + |(n : ℝ)|)^(M.order b + k)) *
        (M.modeConstant a * (1 + |(m : ℝ)|)^(M.order a + (M.order b + k))) :=
      mul_le_mul (modeExtension_norm M b k n)
        (modeExtension_norm M a (M.order b + k) m) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show M.order a + (M.order b + k) =
        M.order a + M.order b + k by omega]
      ring

/-- Locality exponent N costs no extra Sobolev order in the polynomial bound. -/
theorem modeCommutator_norm (a b : Charge M.D) (k : ℕ) (m n : ℤ) :
    ‖M.modeCommutator a b k m n‖ ≤
      2 * M.modeConstant a * M.modeConstant b *
        (1 + |(m : ℝ)|)^(M.order a + M.order b + k) *
        (1 + |(n : ℝ)|)^(M.order a + M.order b + k) := by
  have hC : 0 ≤ M.modeConstant a * M.modeConstant b :=
    mul_nonneg (modeConstant_pos M a).le (modeConstant_pos M b).le
  have hm : (1 + |(m : ℝ)|)^(M.order a + k) ≤
      (1 + |(m : ℝ)|)^(M.order a + M.order b + k) :=
    pow_le_pow_right₀ (by have := abs_nonneg (m : ℝ); linarith) (by omega)
  have hn : (1 + |(n : ℝ)|)^(M.order b + k) ≤
      (1 + |(n : ℝ)|)^(M.order a + M.order b + k) :=
    pow_le_pow_right₀ (by have := abs_nonneg (n : ℝ); linarith) (by omega)
  have hAB := (modeProduct_norm M a b k m n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hC)
      (by positivity : 0 ≤ (1 + |(n : ℝ)|)^(M.order a + M.order b + k)))
  have hBA := (reverseModeProduct_norm M a b k m n).trans
    (mul_le_mul_of_nonneg_left hn
      (mul_nonneg hC (by positivity :
        0 ≤ (1 + |(m : ℝ)|)^(M.order a + M.order b + k))))
  calc
    _ ≤ ‖M.modeProduct a b k m n‖ + ‖M.reverseModeProduct a b k m n‖ :=
      norm_sub_le _ _
    _ ≤ (M.modeConstant a * M.modeConstant b *
          (1 + |(m : ℝ)|)^(M.order a + M.order b + k) *
          (1 + |(n : ℝ)|)^(M.order a + M.order b + k)) +
        (M.modeConstant a * M.modeConstant b *
          (1 + |(m : ℝ)|)^(M.order a + M.order b + k) *
          (1 + |(n : ℝ)|)^(M.order a + M.order b + k)) :=
      add_le_add hAB hBA
    _ = _ := by ring

/-- The actual two-variable coefficient, with no Fourier sign reversal. -/
def Model.modeProductTerm (a b : Charge M.D) (f g : Test) (k : ℕ) (p : ℤ × ℤ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  (f.coefficient p.1 * g.coefficient p.2) • M.modeProduct a b k p.1 p.2

def Model.reverseModeProductTerm (a b : Charge M.D) (f g : Test) (k : ℕ)
    (p : ℤ × ℤ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  (f.coefficient p.1 * g.coefficient p.2) • M.reverseModeProduct a b k p.1 p.2

def Model.modeCommutatorTerm (a b : Charge M.D) (f g : Test) (k : ℕ) (p : ℤ × ℤ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  (f.coefficient p.1 * g.coefficient p.2) • M.modeCommutator a b k p.1 p.2

private theorem modeCommutatorTerm_eq_sub (a b : Charge M.D) (f g : Test)
    (k : ℕ) (p : ℤ × ℤ) :
    M.modeCommutatorTerm a b f g k p =
      M.modeProductTerm a b f g k p - M.reverseModeProductTerm a b f g k p := by
  simp only [Model.modeCommutatorTerm, Model.modeCommutator,
    Model.modeProductTerm, Model.reverseModeProductTerm, smul_sub]

private theorem weight_product_summable (f g : Test) (p q : ℕ) :
    Summable (fun z : ℤ × ℤ => f.weight p z.1 * g.weight q z.2) :=
  (weighted_summable f p).mul_of_nonneg (weighted_summable g q)
    (weight_nonneg f p) (weight_nonneg g q)

theorem modeProductTerm_le (a b : Charge M.D) (f g : Test) (k : ℕ) (p : ℤ × ℤ) :
    ‖M.modeProductTerm a b f g k p‖ ≤
      M.modeConstant a * M.modeConstant b *
        f.weight (M.order a + k) p.1 *
        g.weight (M.order a + M.order b + k) p.2 := by
  rw [Model.modeProductTerm, norm_smul, norm_mul]
  calc
    _ ≤ (‖f.coefficient p.1‖ * ‖g.coefficient p.2‖) *
        (M.modeConstant a * M.modeConstant b *
          (1 + |(p.1 : ℝ)|)^(M.order a + k) *
          (1 + |(p.2 : ℝ)|)^(M.order a + M.order b + k)) :=
      mul_le_mul_of_nonneg_left (modeProduct_norm M a b k p.1 p.2)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by dsimp [Test.weight]; ring

theorem reverseModeProductTerm_le (a b : Charge M.D) (f g : Test)
    (k : ℕ) (p : ℤ × ℤ) :
    ‖M.reverseModeProductTerm a b f g k p‖ ≤
      M.modeConstant a * M.modeConstant b *
        f.weight (M.order a + M.order b + k) p.1 *
        g.weight (M.order b + k) p.2 := by
  rw [Model.reverseModeProductTerm, norm_smul, norm_mul]
  calc
    _ ≤ (‖f.coefficient p.1‖ * ‖g.coefficient p.2‖) *
        (M.modeConstant a * M.modeConstant b *
          (1 + |(p.1 : ℝ)|)^(M.order a + M.order b + k) *
          (1 + |(p.2 : ℝ)|)^(M.order b + k)) :=
      mul_le_mul_of_nonneg_left (reverseModeProduct_norm M a b k p.1 p.2)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by dsimp [Test.weight]; ring

/-- Norm absolute convergence of AB on all of Z x Z, prior to any interchange. -/
theorem modeProduct_absolute (a b : Charge M.D) (f g : Test) (k : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖M.modeProductTerm a b f g k p‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (modeProductTerm_le M a b f g k)
  simpa only [mul_assoc] using
    (weight_product_summable f g (M.order a + k)
      (M.order a + M.order b + k)).mul_left (M.modeConstant a * M.modeConstant b)

/-- Norm absolute convergence of BA, with the complementary weights. -/
theorem reverseModeProduct_absolute (a b : Charge M.D) (f g : Test) (k : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖M.reverseModeProductTerm a b f g k p‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (reverseModeProductTerm_le M a b f g k)
  simpa only [mul_assoc] using
    (weight_product_summable f g (M.order a + M.order b + k)
      (M.order b + k)).mul_left (M.modeConstant a * M.modeConstant b)

theorem modeCommutator_absolute (a b : Charge M.D) (f g : Test) (k : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖M.modeCommutatorTerm a b f g k p‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => ?_)
    ((modeProduct_absolute M a b f g k).add
      (reverseModeProduct_absolute M a b f g k))
  rw [modeCommutatorTerm_eq_sub]
  exact norm_sub_le _ _

/-- Literal first composition of infinite smears, with canonical source transport. -/
def Model.smearComposition (a b : Charge M.D) (f g : Test) (k : ℕ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  M.castSource (by omega : M.order b + (M.order a + k) =
    M.order a + M.order b + k)
    ((M.smear a f k).comp (M.smear b g (M.order a + k)))

def Model.reverseSmearComposition (a b : Charge M.D) (f g : Test) (k : ℕ) :
    M.Sobolev (M.order a + M.order b + k) →L[ℂ] M.Sobolev k :=
  M.castSource (by omega : M.order a + (M.order b + k) =
    M.order a + M.order b + k)
    ((M.smear b g k).comp (M.smear a f (M.order b + k)))

private theorem modeProductTerm_cast (a b : Charge M.D) (f g : Test)
    (k : ℕ) (p : ℤ × ℤ) :
    M.modeProductTerm a b f g k p =
      M.castSource (by omega : M.order b + (M.order a + k) =
        M.order a + M.order b + k)
        ((M.operatorTerm a f k p.1).comp
          (M.operatorTerm b g (M.order a + k) p.2)) := by
  simp only [Model.modeProductTerm, Model.modeProduct, Model.operatorTerm,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, castSource_smul, mul_comm]

private theorem reverseModeProductTerm_cast (a b : Charge M.D) (f g : Test)
    (k : ℕ) (p : ℤ × ℤ) :
    M.reverseModeProductTerm a b f g k p =
      M.castSource (by omega : M.order a + (M.order b + k) =
        M.order a + M.order b + k)
        ((M.operatorTerm b g k p.2).comp
          (M.operatorTerm a f (M.order b + k) p.1)) := by
  simp only [Model.reverseModeProductTerm, Model.reverseModeProduct, Model.operatorTerm,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, castSource_smul]

/-- Expand AB by continuity of composition, after proving the joint norm sum. -/
theorem smearComposition_eq_tsum (a b : Charge M.D) (f g : Test) (k : ℕ) :
    M.smearComposition a b f g k = ∑' p : ℤ × ℤ, M.modeProductTerm a b f g k p := by
  have habsolute : Summable (fun p : ℤ × ℤ =>
      ‖(M.operatorTerm a f k p.1).comp
        (M.operatorTerm b g (M.order a + k) p.2)‖) := by
    simpa only [modeProductTerm_cast, castSource_norm] using
      modeProduct_absolute M a b f g k
  have hjoint : Summable (fun p : ℤ × ℤ =>
      (M.operatorTerm a f k p.1).comp
        (M.operatorTerm b g (M.order a + k) p.2)) :=
    habsolute.of_norm_bounded (fun _ => le_rfl)
  have hA : Summable (M.operatorTerm a f k) :=
    (((original_smooth_fields M a).choose_spec.2 f).1 k).of_norm_bounded
      (fun _ => le_rfl)
  have hB : Summable (M.operatorTerm b g (M.order a + k)) :=
    (((original_smooth_fields M b).choose_spec.2 g).1 (M.order a + k)).of_norm_bounded
      (fun _ => le_rfl)
  let L := ContinuousLinearMap.compL ℂ
    (M.Sobolev (M.order b + (M.order a + k)))
    (M.Sobolev (M.order a + k)) (M.Sobolev k)
  have hraw : (M.smear a f k).comp (M.smear b g (M.order a + k)) =
      ∑' p : ℤ × ℤ, (M.operatorTerm a f k p.1).comp
        (M.operatorTerm b g (M.order a + k) p.2) := by
    calc
      _ = ∑' m : ℤ, (M.operatorTerm a f k m).comp
          (M.smear b g (M.order a + k)) := by
        change L.flip (M.smear b g (M.order a + k))
            (∑' m : ℤ, M.operatorTerm a f k m) =
          ∑' m : ℤ, L.flip (M.smear b g (M.order a + k))
            (M.operatorTerm a f k m)
        exact (L.flip (M.smear b g (M.order a + k))).map_tsum
          hA
      _ = ∑' m : ℤ, ∑' n : ℤ, (M.operatorTerm a f k m).comp
          (M.operatorTerm b g (M.order a + k) n) := by
        apply tsum_congr
        intro m
        change L (M.operatorTerm a f k m)
            (∑' n : ℤ, M.operatorTerm b g (M.order a + k) n) =
          ∑' n : ℤ, L (M.operatorTerm a f k m)
            (M.operatorTerm b g (M.order a + k) n)
        exact (L (M.operatorTerm a f k m)).map_tsum
          hB
      _ = _ := hjoint.tsum_prod.symm
  rw [Model.smearComposition, hraw, castSource_tsum]
  exact tsum_congr (fun p => (modeProductTerm_cast M a b f g k p).symm)

/-- Expand BA on the same Z x Z indexing, again after joint absolute convergence. -/
theorem reverseSmearComposition_eq_tsum (a b : Charge M.D) (f g : Test) (k : ℕ) :
    M.reverseSmearComposition a b f g k =
      ∑' p : ℤ × ℤ, M.reverseModeProductTerm a b f g k p := by
  have habsolute : Summable (fun p : ℤ × ℤ =>
      ‖(M.operatorTerm b g k p.2).comp
        (M.operatorTerm a f (M.order b + k) p.1)‖) := by
    simpa only [reverseModeProductTerm_cast, castSource_norm] using
      reverseModeProduct_absolute M a b f g k
  have hjoint : Summable (fun p : ℤ × ℤ =>
      (M.operatorTerm b g k p.2).comp
        (M.operatorTerm a f (M.order b + k) p.1)) :=
    habsolute.of_norm_bounded (fun _ => le_rfl)
  have hB : Summable (M.operatorTerm b g k) :=
    (((original_smooth_fields M b).choose_spec.2 g).1 k).of_norm_bounded
      (fun _ => le_rfl)
  have hA : Summable (M.operatorTerm a f (M.order b + k)) :=
    (((original_smooth_fields M a).choose_spec.2 f).1 (M.order b + k)).of_norm_bounded
      (fun _ => le_rfl)
  let L := ContinuousLinearMap.compL ℂ
    (M.Sobolev (M.order a + (M.order b + k)))
    (M.Sobolev (M.order b + k)) (M.Sobolev k)
  have hraw : (M.smear b g k).comp (M.smear a f (M.order b + k)) =
      ∑' p : ℤ × ℤ, (M.operatorTerm b g k p.2).comp
        (M.operatorTerm a f (M.order b + k) p.1) := by
    calc
      _ = ∑' m : ℤ, (M.smear b g k).comp
          (M.operatorTerm a f (M.order b + k) m) := by
        change L (M.smear b g k)
            (∑' m : ℤ, M.operatorTerm a f (M.order b + k) m) =
          ∑' m : ℤ, L (M.smear b g k) (M.operatorTerm a f (M.order b + k) m)
        exact (L (M.smear b g k)).map_tsum
          hA
      _ = ∑' m : ℤ, ∑' n : ℤ, (M.operatorTerm b g k n).comp
          (M.operatorTerm a f (M.order b + k) m) := by
        apply tsum_congr
        intro m
        change L.flip (M.operatorTerm a f (M.order b + k) m)
            (∑' n : ℤ, M.operatorTerm b g k n) =
          ∑' n : ℤ, L.flip (M.operatorTerm a f (M.order b + k) m)
            (M.operatorTerm b g k n)
        exact (L.flip (M.operatorTerm a f (M.order b + k) m)).map_tsum
          hB
      _ = _ := hjoint.tsum_prod.symm
  rw [Model.reverseSmearComposition, hraw, castSource_tsum]
  exact tsum_congr (fun p => (reverseModeProductTerm_cast M a b f g k p).symm)

/-- Difference of the two literal infinite compositions in B(H_R,H_k).
    Both double series and their difference are norm absolutely summable by
    the preceding theorems. The coefficient is fhat(m)*ghat(n), with sign AB-BA. -/
theorem smear_comp_eq_double_tsum (a b : Charge M.D) (f g : Test) (k : ℕ) :
    M.castSource (by omega : M.order b + (M.order a + k) =
        M.order a + M.order b + k)
        ((M.smear a f k).comp (M.smear b g (M.order a + k))) -
      M.castSource (by omega : M.order a + (M.order b + k) =
        M.order a + M.order b + k)
        ((M.smear b g k).comp (M.smear a f (M.order b + k))) =
      ∑' p : ℤ × ℤ, (f.coefficient p.1 * g.coefficient p.2) •
        M.modeCommutator a b k p.1 p.2 := by
  have hAB : Summable (M.modeProductTerm a b f g k) :=
    (modeProduct_absolute M a b f g k).of_norm_bounded (fun _ => le_rfl)
  have hBA : Summable (M.reverseModeProductTerm a b f g k) :=
    (reverseModeProduct_absolute M a b f g k).of_norm_bounded (fun _ => le_rfl)
  change M.smearComposition a b f g k - M.reverseSmearComposition a b f g k =
    ∑' p : ℤ × ℤ, M.modeCommutatorTerm a b f g k p
  have hC : Summable (M.modeCommutatorTerm a b f g k) :=
    (modeCommutator_absolute M a b f g k).of_norm_bounded (fun _ => le_rfl)
  have hsum : HasSum (M.modeCommutatorTerm a b f g k)
      (M.smearComposition a b f g k - M.reverseSmearComposition a b f g k) := by
    rw [smearComposition_eq_tsum, reverseSmearComposition_eq_tsum]
    convert hAB.hasSum.sub hBA.hasSum using 1
    funext p
    exact modeCommutatorTerm_eq_sub M a b f g k p
  exact hsum.unique hC.hasSum

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
