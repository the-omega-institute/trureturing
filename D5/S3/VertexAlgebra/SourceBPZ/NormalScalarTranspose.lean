/- GID: D5/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/NormalScalarTranspose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: Finite scalar normal insertion transpose on the original integer lattice carrier. -/

import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.Intervals

/-!
Classical bilinear normal-order calculation on the original finite-charge
polynomial carrier. The current transpose is an explicit smaller supplier;
no all-source adjointness, symmetry or nondegeneracy of the form is assumed.
The normal product and divided derivative are the actual constructors of
FieldNormalProduct, retaining their Carnahan/native adaptation attribution.
The finite scalar cutoffs follow the structure of HalfFock.NormalScalarTranspose,
with integer reflection k ↦ -k and a separate charge-sensitive zero boundary.
The intended consumer is the cons step of the original wordField BPZ induction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.SourceBPZ
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents FieldNormalProduct

/-- Order p corresponds to insertion h_i(-(p+1)). -/
def insertion (D : LatticeData) (i : Fin D.rank) (p : ℕ)
    (F : VertexOperator ℂ (Carrier D)) : VertexOperator ℂ (Carrier D) :=
  (normalMinusOne (dividedDerivative p (neutralField D i)) F).1

private def coefficient (p : ℕ) (k : ℤ) : ℂ :=
  ((Ring.choose (-k-1) p : ℤ) : ℂ)

private theorem derivative_mode (D : LatticeData) (i : Fin D.rank) (p : ℕ) (m : ℤ) :
    ((dividedDerivative p (neutralField D i))[[m]]) =
      coefficient p (m-p) • neutralMode D i (m-p) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-m-1+p) p •
    HVertexOperator.coeff (neutralField D i) (-m-1+p) v = _
  rw [VertexOperator.coeff_eq_ncoeff, neutralField_ncoeff]
  rw [show -(-m-1+p)-1 = m-p by omega]
  simp only [coefficient, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  congr 2; omega

private theorem coefficient_zero_band (p : ℕ) (k : ℤ)
    (hk : -(p : ℤ) ≤ k) (hn : k < 0) : coefficient p k = 0 := by
  have ha : 0 ≤ -k-1 := by omega
  obtain ⟨a, he⟩ := Int.eq_ofNat_of_zero_le ha
  have hb : a < p := by omega
  simp [coefficient, he, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hb]

private theorem coefficient_reflection (p : ℕ) (j : ℤ) :
    -coefficient p (-j) = (-1 : ℂ)^(p+1) *
      ∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) * coefficient s j := by
  have h : Ring.choose (j-1) p = (-1 : ℤ)^p *
      ∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℤ) * Ring.choose (-j-1) s := by
    rw [show j-1 = -(-j+1) by ring, Ring.choose_neg]
    rw [show (-j+1)+(p : ℤ)-1 = (-j-1)+((p+1 : ℕ) : ℤ) by push_cast; ring]
    rw [Ring.add_choose_eq p (Commute.all _ _),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    have hs' : s ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    rw [Ring.choose_natCast, ← Nat.choose_symm (by omega : p-s ≤ p+1),
      show p+1-(p-s) = s+1 by omega]
    ring
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  simp only [coefficient, neg_neg]
  rw [hc, pow_succ]
  ring

private theorem coefficient_at_zero (p : ℕ) :
    coefficient p 0 = (-1 : ℂ)^p := by
  simp only [coefficient, neg_zero, zero_sub]
  rw [show (-1 : ℤ) = -(1 : ℤ) by rfl, Ring.choose_neg]
  simp [Units.smul_def, Ring.choose_natCast]

private theorem forward_finite (D : LatticeData) (L F : VertexOperator ℂ (Carrier D))
    (m : ℤ) (u : Carrier D) :
    Function.HasFiniteSupport (fun t : ℕ => (L[[-(t : ℤ)-1]]) ((F[[m+t]]) u)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (F u)).order-m).toNat, ?_⟩
  intro t ht
  contrapose! ht
  have hz : (F[[m+t]]) u = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

private theorem reverse_finite (D : LatticeData) (L F : VertexOperator ℂ (Carrier D))
    (m : ℤ) (u : Carrier D) :
    Function.HasFiniteSupport (fun t : ℕ => (F[[m-t-1]]) ((L[[t]]) u)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (L u)).order-1).toNat, ?_⟩
  intro t ht
  contrapose! ht
  have hz : (L[[t]]) u = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

private def cutoff (D : LatticeData) (u : Carrier D) : ℕ :=
  vectorFrequencyBound D u + 1

private theorem cutoff_pos (D : LatticeData) (u : Carrier D) : 0 < cutoff D u := by
  simp [cutoff]

private theorem cutoff_vanish (D : LatticeData) (i : Fin D.rank) (u : Carrier D)
    (k : ℤ) (hk : (cutoff D u : ℤ) ≤ k) : neutralMode D i k u = 0 := by
  apply neutralMode_vanish
  dsimp [cutoff] at hk
  omega

private theorem scalar_offsets (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (F : VertexOperator ℂ (Carrier D)) (m : ℤ) (u v : Carrier D) :
    B (((insertion D i p F)[[m]]) u) v =
      (∑ t ∈ Finset.range (cutoff D v),
        coefficient p (-(t : ℤ)-1-p) *
          B (neutralMode D i (-(t : ℤ)-1-p) ((F[[m+t]]) u)) v) +
      ∑ t ∈ Finset.range (cutoff D u+p),
        coefficient p ((t : ℤ)-p) *
          B ((F[[m-t-1]]) (neutralMode D i ((t : ℤ)-p) u)) v := by
  let L := dividedDerivative p (neutralField D i)
  rw [insertion, (normalMinusOne L F).2]
  change (B.flip v) (_+_) = _
  rw [map_add, map_finsum (B.flip v) (forward_finite D L F m u),
    map_finsum (B.flip v) (reverse_finite D L F m u)]
  simp only [L, derivative_mode, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply,
    map_smul, smul_eq_mul]
  congr 1
  · apply finsum_eq_sum_of_support_subset
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra ho
    have hz : neutralMode D i (-(-(t : ℤ)-1-p)) v = 0 := by
      apply cutoff_vanish
      omega
    exact ht (by dsimp only; rw [hB, hz, map_zero, neg_zero, mul_zero])
  · apply finsum_eq_sum_of_support_subset
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra ho
    have hz : neutralMode D i ((t : ℤ)-p) u = 0 := by
      apply cutoff_vanish
      omega
    exact ht (by dsimp only; simp [hz])

/- Both scalar intervals are independent of the tail field and the derivative
order. The omitted derivative bands vanish by integer binomial coefficients. -/
private theorem scalar_interval (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (F : VertexOperator ℂ (Carrier D)) (m : ℤ) (u v : Carrier D) :
    B (((insertion D i p F)[[m]]) u) v =
      (∑ k ∈ Finset.Icc (1-(cutoff D v : ℤ)) (-1),
        coefficient p k * B (neutralMode D i k ((F[[m-k-p-1]]) u)) v) +
      ∑ k ∈ Finset.Icc 0 ((cutoff D u : ℤ)-1),
        coefficient p k * B ((F[[m-k-p-1]]) (neutralMode D i k u)) v := by
  rw [scalar_offsets D B i hB]
  congr 1
  · apply Finset.sum_bij_ne_zero (fun (t : ℕ) _ _ => -(t : ℤ)-1-p)
    · intro t ht hn
      rw [Finset.mem_Icc]
      constructor
      · by_contra ho
        have hz : neutralMode D i (-(-(t : ℤ)-1-p)) v = 0 := by
          apply cutoff_vanish
          omega
        exact hn (by rw [hB, hz, map_zero, neg_zero, mul_zero])
      · omega
    · intro a ha hna b hb hnb he
      omega
    · intro k hk hn
      have hk' := Finset.mem_Icc.mp hk
      have below : k < -(p : ℤ) := by
        by_contra ho
        exact hn (by rw [coefficient_zero_band p k (by omega) (by omega), zero_mul])
      refine ⟨(-k-1-p).toNat, ?_, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hc := cutoff_pos D v
        omega
      · have he : (((-k-1-p).toNat : ℕ) : ℤ) = -k-1-p :=
          Int.toNat_of_nonneg (by omega)
        simpa only [he, show -(-k-1-p)-1-(p : ℤ) = k by omega,
          show m+(-k-1-p) = m-k-p-1 by omega] using hn
      · have he := Int.toNat_of_nonneg (show 0 ≤ -k-1-p by omega)
        omega
    · intro t ht hn
      simp only [show m-(-(t : ℤ)-1-p)-p-1 = m+t by omega]
  · apply Finset.sum_bij_ne_zero (fun (t : ℕ) _ _ => (t : ℤ)-p)
    · intro t ht hn
      have ht' := Finset.mem_range.mp ht
      rw [Finset.mem_Icc]
      constructor
      · by_contra ho
        exact hn (by rw [coefficient_zero_band p ((t : ℤ)-p) (by omega) (by omega),
          zero_mul])
      · omega
    · intro a ha hna b hb hnb he
      omega
    · intro k hk hn
      have hk' := Finset.mem_Icc.mp hk
      refine ⟨(k+p).toNat, ?_, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · have he : (((k+p).toNat : ℕ) : ℤ) = k+p := Int.toNat_of_nonneg (by omega)
        simpa only [he, show k+(p : ℤ)-p = k by omega,
          show m-(k+p)-1 = m-k-p-1 by omega] using hn
      · have he := Int.toNat_of_nonneg (show 0 ≤ k+p by omega)
        omega
    · intro t ht hn
      simp only [show m-((t : ℤ)-p)-p-1 = m-t-1 by omega]

private theorem flipped_current (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y)) :
    ∀ k x y, B.flip (neutralMode D i k x) y =
      -B.flip x (neutralMode D i (-k) y) := by
  intro k x y
  have h := hB (-k) y x
  simp only [neg_neg] at h
  change B y (neutralMode D i k x) = -B (neutralMode D i (-k) y) x
  linear_combination h

private theorem right_interval (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (G : VertexOperator ℂ (Carrier D)) (H : ℤ) (u v : Carrier D) :
    B u (((insertion D i p G)[[H+p+1]]) v) =
      (∑ j ∈ Finset.Icc (1-(cutoff D u : ℤ)) (-1),
        coefficient p j * B u (neutralMode D i j ((G[[H-j]]) v))) +
      ∑ j ∈ Finset.Icc 0 ((cutoff D v : ℤ)-1),
        coefficient p j * B u ((G[[H-j]]) (neutralMode D i j v)) := by
  have h := scalar_interval D B.flip i (flipped_current D B i hB) p G (H+p+1) v u
  simpa only [LinearMap.BilinForm.flip_apply,
    show ∀ j : ℤ, H+p+1-j-p-1 = H-j by intro j; omega] using h

private theorem reflect_interval (f : ℤ → ℂ) (a b : ℤ) :
    ∑ k ∈ Finset.Icc a b, f k = ∑ j ∈ Finset.Icc (-b) (-a), f (-j) := by
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk l hl he
    omega
  · intro j hj
    refine ⟨-j, ?_, by omega⟩
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro k hk
    simp

private theorem reflection_sum (p : ℕ) (J : Finset ℤ) (f : ℤ → ℂ) :
    (∑ j ∈ J, -coefficient p (-j) * f j) =
      (-1 : ℂ)^(p+1) * ∑ s ∈ Finset.range (p+1),
        ((p+1).choose (s+1) : ℂ) * ∑ j ∈ J, coefficient s j * f j := by
  simp only [coefficient_reflection, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem reflected_to_insertion (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (G : VertexOperator ℂ (Carrier D)) (κ : ℂ)
    (hzero : ∀ t x, neutralMode D i 0 ((G[[t]]) x) =
      (G[[t]]) (neutralMode D i 0 x) + κ • (G[[t]]) x)
    (H : ℤ) (u v : Carrier D) :
    (∑ j ∈ Finset.Icc 1 ((cutoff D v : ℤ)-1),
      -coefficient p (-j) * B u ((G[[H-j]]) (neutralMode D i j v))) +
    (∑ j ∈ Finset.Icc (1-(cutoff D u : ℤ)) 0,
      -coefficient p (-j) * B u (neutralMode D i j ((G[[H-j]]) v))) =
    (-1 : ℂ)^(p+1) *
      ((∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) *
        B u (((insertion D i s G)[[H+s+1]]) v)) + κ * B u ((G[[H]]) v)) := by
  classical
  let left := fun j : ℤ => B u (neutralMode D i j ((G[[H-j]]) v))
  let right := fun j : ℤ => B u ((G[[H-j]]) (neutralMode D i j v))
  have hl : Finset.Icc (1-(cutoff D u : ℤ)) 0 =
      insert 0 (Finset.Icc (1-(cutoff D u : ℤ)) (-1)) := by
    have h := cutoff_pos D u
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hr : Finset.Icc 0 ((cutoff D v : ℤ)-1) =
      insert 0 (Finset.Icc 1 ((cutoff D v : ℤ)-1)) := by
    have h := cutoff_pos D v
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hz : left 0 = right 0 + κ * B u ((G[[H]]) v) := by
    dsimp [left, right]
    rw [sub_zero, hzero]
    simp [map_add, map_smul, smul_eq_mul]
  have ordered :
      (∑ j ∈ Finset.Icc 1 ((cutoff D v : ℤ)-1), -coefficient p (-j) * right j) +
      (∑ j ∈ Finset.Icc (1-(cutoff D u : ℤ)) 0, -coefficient p (-j) * left j) =
      ((∑ j ∈ Finset.Icc (1-(cutoff D u : ℤ)) (-1), -coefficient p (-j) * left j) +
      (∑ j ∈ Finset.Icc 0 ((cutoff D v : ℤ)-1), -coefficient p (-j) * right j)) +
        (-1 : ℂ)^(p+1) * κ * B u ((G[[H]]) v) := by
    rw [hl, hr, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    rw [neg_zero, coefficient_at_zero, hz, pow_succ]
    ring
  rw [ordered, reflection_sum, reflection_sum, ← mul_add]
  have hsum :
      (∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) *
        ∑ j ∈ Finset.Icc (1-(cutoff D u : ℤ)) (-1), coefficient s j * left j) +
      (∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) *
        ∑ j ∈ Finset.Icc 0 ((cutoff D v : ℤ)-1), coefficient s j * right j) =
      ∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) *
        B u (((insertion D i s G)[[H+s+1]]) v) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [right_interval D B i hB]
    dsimp [left, right]
    ring
  rw [hsum]
  ring

/-- Finite original scalar insertion law. Here n=p+1, and the summation index
s=r-1 runs through 0,...,p. The last summand deletes the inserted oscillator.
Only the smaller current law, a finite tail transpose, and its zero-mode charge
covariance are premises. In particular the all-source BPZ law is not a premise. -/
theorem consumed_normal_product_form (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (F : VertexOperator ℂ (Carrier D))
    {σ : Type*} (S : Finset σ) (G : σ → VertexOperator ℂ (Carrier D))
    (weight : σ → ℂ) (K : σ → ℤ) (κ : ℂ)
    (htail : ∀ t x y, B ((F[[t]]) x) y =
      ∑ a ∈ S, weight a * B x (((G a)[[K a - t]]) y))
    (hzero : ∀ a ∈ S, ∀ t x, neutralMode D i 0 (((G a)[[t]]) x) =
      ((G a)[[t]]) (neutralMode D i 0 x) + κ • ((G a)[[t]]) x)
    (m : ℤ) (u v : Carrier D) :
    B (((insertion D i p F)[[m]]) u) v =
      (-1 : ℂ)^(p+1) * ∑ a ∈ S, weight a *
        ((∑ s ∈ Finset.range (p+1), ((p+1).choose (s+1) : ℂ) *
          B u (((insertion D i s (G a))[[K a+p+s+2-m]]) v)) +
          κ * B u (((G a)[[K a+p+1-m]]) v)) := by
  classical
  have negative (k : ℤ) :
      coefficient p k * B (neutralMode D i k ((F[[m-k-p-1]]) u)) v =
      ∑ a ∈ S, weight a * (-coefficient p k *
        B u (((G a)[[K a+p+1-m+k]]) (neutralMode D i (-k) v))) := by
    rw [hB, htail, ← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [show K a-(m-k-p-1) = K a+p+1-m+k by omega]
    ring
  have positive (k : ℤ) :
      coefficient p k * B ((F[[m-k-p-1]]) (neutralMode D i k u)) v =
      ∑ a ∈ S, weight a * (-coefficient p k *
        B u (neutralMode D i (-k) (((G a)[[K a+p+1-m+k]]) v))) := by
    rw [htail, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hB, show K a-(m-k-p-1) = K a+p+1-m+k by omega]
    ring
  rw [scalar_interval D B i hB]
  simp_rw [negative, positive]
  rw [Finset.sum_comm (s := Finset.Icc (1-(cutoff D v : ℤ)) (-1)) (t := S),
    Finset.sum_comm (s := Finset.Icc 0 ((cutoff D u : ℤ)-1)) (t := S),
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  rw [reflect_interval (fun k => -coefficient p k *
      B u (((G a)[[K a+p+1-m+k]]) (neutralMode D i (-k) v)))
      (1-(cutoff D v : ℤ)) (-1),
    reflect_interval (fun k => -coefficient p k *
      B u (neutralMode D i (-k) (((G a)[[K a+p+1-m+k]]) v)))
      0 ((cutoff D u : ℤ)-1)]
  simp only [neg_neg, neg_zero,
    show -(1-(cutoff D v : ℤ)) = (cutoff D v : ℤ)-1 by omega,
    show -((cutoff D u : ℤ)-1) = 1-(cutoff D u : ℤ) by omega,
    show ∀ j : ℤ, K a+p+1-m+-j = (K a+p+1-m)-j by intro j; omega]
  rw [reflected_to_insertion D B i hB p (G a) κ (hzero a ha)]
  have hm : ∀ s : ℕ, K a+p+1-m+s+1 = K a+p+s+2-m := by intro s; omega
  simp only [hm]
  ring

end D5.S3.VertexAlgebra.SourceBPZ
