/- GID: D5/S3/VertexAlgebra/StateField/SkewSymmetry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/StateField/SkewSymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-state skew symmetry and supported formal translation reversal. -/

import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra

/-! Classical skew symmetry, in the normalized mode convention a_n z^(-n-1).
Sources: Matsuo--Nagatomo, hep-th/9706118; Bakalov--Kac, math/0402315.
The actual-field Borcherds suppliers retain Scott Carnahan's attribution.
No nilpotence of translation, homogeneous-state hypothesis or sewing law is used.
proof_shape: creation_coeff, skew_symmetry: content
escape_witness: Induction from vacuum covariance gives every divided translation
coefficient. The p=-1,q=0 Borcherds specialization then collapses its two right
branches and identifies every signed mode with the supported reversal convolution.
admission_basis: escape-witness
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.StateField.SkewSymmetry
open LatticeActualVertexAlgebra
open StateFieldResidueReconstruction (integerBinomial epsilon)
open scoped VertexOperator
noncomputable section
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Every vacuum coefficient is a divided power of translation. -/
theorem creation_coeff (A : StateFieldVertexAlgebra V) (v : V) (j : ℕ) :
    ((A.stateField v)[[-(j : ℤ)-1]]) A.vacuum =
      (j.factorial : ℂ)⁻¹ • (A.translation ^ j) v := by
  induction j with
  | zero => simpa using A.creation v
  | succ j ih =>
    have law := congrArg (fun f : Module.End ℂ V => f A.vacuum)
      (A.covariance v (-(j : ℤ)-1))
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      A.translation_vacuum,
      map_zero, sub_zero, ih, map_smul] at law
    have hcast : (-((-(j : ℤ)-1 : ℤ) : ℂ)) = ((j+1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast] at law
    have hn : ((j+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have h := congrArg (fun w : V => (((j+1 : ℕ) : ℂ)⁻¹) • w) law
    simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at h
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, pow_succ',
      Module.End.mul_apply, Nat.cast_add, Nat.cast_one, mul_comm,
      show -(j : ℤ)-1-1 = -((j+1 : ℕ) : ℤ)-1 by omega] using h.symm

/-- The coefficient convolution for exp(zT) s(-z). -/
def reversalTerm (T : Module.End ℂ V) (s : HahnSeries ℤ V) (k : ℤ) (j : ℕ) : V :=
  (((-1 : ℂ) ^ (k-(j : ℤ))) / (j.factorial : ℂ)) •
    (T ^ j) (s.coeff (k-(j : ℤ)))

/-- Lower support of s makes each translation convolution finite. -/
theorem reversal_finite (T : Module.End ℂ V) (s : HahnSeries ℤ V) (k : ℤ) :
    Function.HasFiniteSupport (reversalTerm T s k) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(k-s.order).toNat, ?_⟩
  intro j hj
  contrapose! hj
  have hz : s.coeff (k-(j : ℤ)) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  simp [reversalTerm, hz]

/-- The convolution preserves the lower support bound; it is a formal series. -/
theorem reversal_bounded (T : Module.End ℂ V) (s : HahnSeries ℤ V) :
    BddBelow (Function.support (fun k : ℤ => ∑ᶠ j : ℕ, reversalTerm T s k j)) := by
  refine ⟨s.order, ?_⟩
  intro k hk
  by_contra h
  have hz : (∑ᶠ j : ℕ, reversalTerm T s k j) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hc : s.coeff (k-(j : ℤ)) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_order (by omega)
    simp [reversalTerm, hc]
  exact hk hz

/-- Statewise formal exponential reversal, without numerical operator exponentiation. -/
def reversal (T : Module.End ℂ V) (s : HahnSeries ℤ V) : HahnSeries ℤ V :=
  HahnSeries.ofSuppBddBelow (fun k => ∑ᶠ j : ℕ, reversalTerm T s k j)
    (reversal_bounded T s)

/-- Standard all-state skew symmetry, with finite sums and its formal-series meaning. -/
theorem skew_symmetry (A : StateFieldVertexAlgebra V) (a b : V) :
    (∀ n : ℤ,
      Function.HasFiniteSupport (fun j : ℕ =>
        (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
          (A.translation ^ j) (((A.stateField b)[[n+j]]) a)) ∧
      ((A.stateField a)[[n]]) b = ∑ᶠ j : ℕ,
        (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
          (A.translation ^ j) (((A.stateField b)[[n+j]]) a)) ∧
    (HahnModule.of ℂ).symm ((A.stateField a) b) =
      reversal A.translation ((HahnModule.of ℂ).symm ((A.stateField b) a)) := by
  classical
  have binom (j : ℕ) : integerBinomial (-1) j = (-1 : ℂ)^j := by
    simp [integerBinomial, Ring.choose_neg', Ring.multichoose_one,
      Units.smul_def]
  have term_reversal (n : ℤ) (j : ℕ) :
      (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
          (A.translation ^ j) (((A.stateField b)[[n+j]]) a) =
        reversalTerm A.translation
          ((HahnModule.of ℂ).symm ((A.stateField b) a)) (-n-1) j := by
    unfold reversalTerm
    have hc : ((HahnModule.of ℂ).symm ((A.stateField b) a)).coeff (-n-1-(j : ℤ)) =
        ((A.stateField b)[[n+j]]) a := by
      change (HVertexOperator.coeff (A.stateField b) (-n-1-(j : ℤ))) a = _
      rw [VertexOperator.coeff_eq_ncoeff]
      rw [show -(-n-1-(j : ℤ))-1 = n+(j : ℤ) by omega]
    rw [hc]
    have hs : (-1 : ℂ)^(-n-1-(j : ℤ)) = (-1 : ℂ)^(n+(j : ℤ)+1) := by
      rw [show -n-1-(j : ℤ) = -(n+(j : ℤ)+1) by omega, zpow_neg, ← inv_zpow]
      norm_num
    rw [hs]
  have modes (n : ℤ) :
      Function.HasFiniteSupport (fun j : ℕ =>
        (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
          (A.translation ^ j) (((A.stateField b)[[n+j]]) a)) ∧
      ((A.stateField a)[[n]]) b = ∑ᶠ j : ℕ,
        (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
          (A.translation ^ j) (((A.stateField b)[[n+j]]) a) := by
    have finite : Function.HasFiniteSupport (fun j : ℕ =>
        (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
          (A.translation ^ j) (((A.stateField b)[[n+j]]) a)) := by
      have he : (fun j : ℕ =>
          (((-1 : ℂ) ^ (n+(j : ℤ)+1)) / (j.factorial : ℂ)) •
            (A.translation ^ j) (((A.stateField b)[[n+j]]) a)) =
          reversalTerm A.translation
            ((HahnModule.of ℂ).symm ((A.stateField b) a)) (-n-1) :=
        funext (term_reversal n)
      rw [he]
      exact reversal_finite _ _ _
    refine ⟨finite, ?_⟩
    obtain ⟨leftFinite, firstFinite, secondFinite, law⟩ :=
      A.borcherds b a A.vacuum (-1) 0 n
    dsimp only at leftFinite firstFinite secondFinite law
    have rhs : (∑ᶠ i : ℕ,
        (((-1 : ℂ)^i)*integerBinomial n i) •
          (((A.stateField b)[[-1+n-i]]) (((A.stateField a)[[0+i]]) A.vacuum) -
            epsilon n • ((A.stateField a)[[0+n-i]])
              (((A.stateField b)[[-1+i]]) A.vacuum))) =
        -(epsilon n • ((A.stateField a)[[n]]) b) := by
      rw [finsum_eq_single _ 0]
      · simp [integerBinomial, A.creativity, A.creation]
      · intro i hi
        rw [A.creativity a (0+(i : ℤ)) (by omega), map_zero,
          A.creativity b (-1+(i : ℤ)) (by omega)]
        simp
    rw [rhs] at law
    have cancelSign : (-epsilon n)*(-epsilon n) = 1 := by
      simp only [epsilon, neg_mul_neg, ← mul_zpow]
      norm_num
    have scaled := congrArg (fun w : V => (-epsilon n) • w) law
    rw [smul_finsum' _ leftFinite] at scaled
    simp only [← neg_smul, smul_smul, cancelSign, one_smul] at scaled
    rw [← scaled]
    apply finsum_congr
    intro j
    rw [binom, show (-1 : ℤ)+0-(j : ℤ) = -(j : ℤ)-1 by omega,
      creation_coeff]
    simp only [smul_smul, div_eq_mul_inv]
    congr 1
    rw [epsilon, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
    simp
  refine ⟨modes, ?_⟩
  apply HahnSeries.ext
  funext k
  have h := (modes (-k-1)).2
  change _ = ∑ᶠ j : ℕ, reversalTerm A.translation _ k j
  change (HVertexOperator.coeff (A.stateField a) k) b = _
  rw [VertexOperator.coeff_eq_ncoeff]
  rw [h]
  apply finsum_congr
  intro j
  simpa only [show -(-k-1)-1 = k by omega] using term_reversal (-k-1) j

end
end D5.S3.VertexAlgebra.StateField.SkewSymmetry
