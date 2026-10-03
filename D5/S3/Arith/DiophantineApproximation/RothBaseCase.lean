/- GID: D5/S3/Arith/DiophantineApproximation/RothBaseCase
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RothBaseCase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A one-variable index estimate supplies the base case of the Roth argument. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.Gelfond
public import D5.S3.Arith.DiophantineApproximation.IndexRename

@[expose] public section

open Height AdmissibleAbsValues

open scoped ENNReal

namespace Polynomial

variable {K : Type*} [Field K] [NumberField K]


/-- **Roth's lemma in one variable** (Bombieri–Gubler, Lemma 6.3.9). -/
theorem rootMultiplicity_mul_logHeight₁_le {q : K[X]} (hq : q ≠ 0) (a : K) :
    (q.rootMultiplicity a : ℝ) * logHeight₁ a
      ≤ q.logHeight + (q.natDegree : ℝ) * totalWeight K * Real.log 2 := by
  obtain ⟨R, hR⟩ := pow_rootMultiplicity_dvd q a
  have hp0 : (((X : K[X]) - C a) ^ q.rootMultiplicity a) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero a)
  have hR0 : R ≠ 0 := fun h ↦ hq (by rw [hR, h, mul_zero])
  have hdegsum : (((X : K[X]) - C a) ^ q.rootMultiplicity a).natDegree + R.natDegree
      = q.natDegree := by
    conv_rhs => rw [hR]
    rw [natDegree_mul hp0 hR0]
  have hgel := mulHeight_mul_mulHeight_le hp0 hR0
  rw [hdegsum, ← hR] at hgel
  have hstep : mulHeight₁ a ^ q.rootMultiplicity a
      ≤ 2 ^ (q.natDegree * totalWeight K) * q.mulHeight := by
    refine le_trans ((open scoped Classical NumberField in (open Height AdmissibleAbsValues Finset Module Matrix Set Polynomial in (fun {K : Type _} [instK : Field K] [instN : NumberField K] (a : K) (k : ℕ) => (show mulHeight₁ a ^ k ≤ ((X - C a) ^ k).mulHeight from by
        have hmonic : (((X : K[X]) - C a) ^ k).Monic := (monic_X_sub_C a).pow k
        have hc0 : (((X : K[X]) - C a) ^ k).coeff 0 = (-a) ^ k := by
          rw [coeff_zero_eq_eval_zero]
          simp
        have hck : (((X : K[X]) - C a) ^ k).coeff (((X : K[X]) - C a) ^ k).natDegree = 1 :=
          hmonic.coeff_natDegree
        have hcomp : ![(-a) ^ k, (1 : K)]
            = (fun i : Fin ((((X : K[X]) - C a) ^ k).natDegree + 1) ↦
                (((X : K[X]) - C a) ^ k).coeff (i : ℕ))
              ∘ ![0, Fin.last _] := by
          funext i
          fin_cases i
          · simpa using hc0.symm
          · simpa using hck.symm
        have hle : Height.mulHeight ![(-a) ^ k, (1 : K)] ≤ ((X - C a) ^ k).mulHeight := by
          rw [(open scoped Classical NumberField in (open Height Module Matrix Set Polynomial in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] (p : K[X]) => (show p.mulHeight = Height.mulHeight fun i : Fin (p.natDegree + 1) ↦ p.coeff i.val from by
              simpa only [Polynomial.mulHeight, toFinsupp_apply] using
                (open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α)
                      (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
                    have hbij : Function.Bijective
                        (fun i : Function.support (fun i ↦ x (f i)) ↦
                          (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
                      refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
                      obtain ⟨i, rfl⟩ := hx a ha
                      exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
                    rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight,
                      ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
                    rfl)))) p.toFinsupp.coeff Fin.val Fin.val_injective
                  (fun n hn ↦ ⟨⟨n, Nat.lt_succ_of_le
                    (le_natDegree_of_mem_supp n (by simpa only [support_toFinsupp] using hn))⟩, rfl⟩))))), hcomp]
          exact Height.mulHeight_comp_le _ _
        refine le_of_eq_of_le ?_ hle
        rw [← mulHeight₁_eq_mulHeight, mulHeight₁_pow, mulHeight₁_neg])))) a _) (le_trans ?_ hgel)
    exact le_mul_of_one_le_right ((fun p : Polynomial K ↦ (show 0 < p.mulHeight from Height.mulHeight_pos (fun i : (p.toFinsupp.coeff).support ↦ (p.toFinsupp.coeff) i.val))) _).le ((fun p : Polynomial K ↦ (show 1 ≤ p.mulHeight from Height.one_le_mulHeight (fun i : (p.toFinsupp.coeff).support ↦ (p.toFinsupp.coeff) i.val))) R)
  have hlog := Real.log_le_log (by positivity) hstep
  rw [Real.log_pow, ← logHeight₁_eq_log_mulHeight₁, ← logHeight₁_pow,
    Real.log_mul (by positivity) ((fun p : Polynomial K ↦ (show p.mulHeight ≠ 0 from Height.mulHeight_ne_zero (fun i : (p.toFinsupp.coeff).support ↦ (p.toFinsupp.coeff) i.val))) q), Real.log_pow,
    ← Polynomial.logHeight] at hlog
  refine le_trans (le_of_eq ?_) (le_of_le_of_eq hlog (by push_cast; ring))
  rw [logHeight₁_pow]

end Polynomial

namespace MvPolynomial

variable {σ : Type*} [Unique σ] {K : Type*} [Field K] [NumberField K]

/-- The exponents of a polynomial in one variable are its degrees. -/
noncomputable def uniqueSingleEquiv (σ : Type*) [Unique σ] : ℕ ≃ (σ →₀ ℕ) where
  toFun n := Finsupp.single default n
  invFun ν := ν default
  left_inv n := by simp
  right_inv ν := (Finsupp.unique_single ν).symm



/-- **The base case of Roth's lemma**, in the shape the induction consumes. -/
theorem index_le_base {P : MvPolynomial σ K} (hP : P ≠ 0) {e : ℕ} (he : 1 ≤ e)
    (hdeg : P.degreeOf default ≤ e) (ξ : σ → K) {s : ℝ} (hs : 0 < s)
    (hheight : P.logHeight + 4 * e * totalWeight K ≤ s * (e * logHeight₁ (ξ default))) :
    index (fun _ ↦ (e : ℝ)) ξ P ≤ ENNReal.ofReal s := by
  set q : Polynomial K := uniqueAlgEquiv K σ P with hqdef
  have hq0 : q ≠ 0 := fun h ↦ hP ((uniqueAlgEquiv K σ).injective (by rw [← hqdef, h, map_zero]))
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have htw : (0 : ℝ) < totalWeight K := by
    rw [NumberField.totalWeight_eq_finrank]
    exact_mod_cast Module.finrank_pos
  have hL : 0 ≤ P.logHeight := (fun p : MvPolynomial _ K ↦ (show 0 ≤ p.logHeight from Real.log_nonneg (Height.one_le_mulHeight (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val)))) P
  have h4 : (0 : ℝ) < 4 * e * totalWeight K := by positivity
  have hh1 : 0 < logHeight₁ (ξ default) := by
    by_contra hle
    push Not at hle
    nlinarith [hheight, hL, h4, mul_pos hs hep, hle]
  have hsuppNat (x : ℕ →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hsuppMv (x : (σ →₀ ℕ) →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : σ →₀ ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hcoeNat (x : ℕ →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
    rcases eq_or_ne x 0 with rfl | hx
    · have : IsEmpty ((0 : ℕ →₀ K).support : Type _) := by
        simp only [Finsupp.support_zero]; infer_instance
      rw [Finsupp.coe_zero, Height.mulHeight_zero, Finsupp.mulHeight]
      exact (Height.mulHeight_eq_one_of_subsingleton _).symm
    have hx' : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
    have hxs : (fun i : x.support ↦ x i.val) ≠ 0 := by
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
      exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
    rw [Height.mulHeight_eq hx', Finsupp.mulHeight, Height.mulHeight_eq hxs]
    congr 1
    · congr 2
      ext1 v
      exact hsuppNat x v
    · exact finprod_congr fun v ↦ hsuppNat x v.val
  have hcoeMv (x : (σ →₀ ℕ) →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
    rcases eq_or_ne x 0 with rfl | hx
    · have : IsEmpty ((0 : (σ →₀ ℕ) →₀ K).support : Type _) := by
        simp only [Finsupp.support_zero]; infer_instance
      rw [Finsupp.coe_zero, Height.mulHeight_zero, Finsupp.mulHeight]
      exact (Height.mulHeight_eq_one_of_subsingleton _).symm
    have hx' : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
    have hxs : (fun i : x.support ↦ x i.val) ≠ 0 := by
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
      exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
    rw [Height.mulHeight_eq hx', Finsupp.mulHeight, Height.mulHeight_eq hxs]
    congr 1
    · congr 2
      ext1 v
      exact hsuppMv x v
    · exact finprod_congr fun v ↦ hsuppMv x v.val
  have hheightEquiv : (uniqueAlgEquiv K σ P).mulHeight = P.mulHeight := by
    rw [Polynomial.mulHeight, MvPolynomial.mulHeight,
      ← hcoeNat (uniqueAlgEquiv K σ P).toFinsupp.coeff,
      ← hcoeMv (AddMonoidAlgebra.coeff P),
      ← Height.mulHeight_comp_equiv (uniqueSingleEquiv σ)]
    exact congrArg Height.mulHeight
      (_root_.funext fun n ↦ coeff_uniqueAlgEquiv (R := K) (σ := σ) P n)
  have hbase := Polynomial.rootMultiplicity_mul_logHeight₁_le hq0 (ξ default)
  rw [Polynomial.logHeight, hheightEquiv, ← MvPolynomial.logHeight] at hbase
  have hdqNat : q.natDegree ≤ e := by
    change (uniqueAlgEquiv K σ P).natDegree ≤ e
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
    rw [coeff_uniqueAlgEquiv]
    by_contra hc
    have hle := degreeOf_le_iff.mp (le_refl (P.degreeOf default)) _
      (mem_support_iff.mpr hc)
    rw [Finsupp.single_eq_same] at hle
    omega
  have hdq : (q.natDegree : ℝ) ≤ e := by exact_mod_cast hdqNat
  have hlog2 : Real.log 2 ≤ 4 := le_trans (Real.log_le_sub_one_of_pos two_pos) (by norm_num)
  have hk : (q.rootMultiplicity (ξ default) : ℝ) ≤ s * e := by
    have h1 : (q.rootMultiplicity (ξ default) : ℝ) * logHeight₁ (ξ default)
        ≤ s * (e * logHeight₁ (ξ default)) := by
      refine le_trans hbase (le_trans ?_ hheight)
      have hlog0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hstep : (q.natDegree : ℝ) * Real.log 2 ≤ (e : ℝ) * 4 :=
        mul_le_mul hdq hlog2 hlog0 (by positivity)
      have hfin : (q.natDegree : ℝ) * totalWeight K * Real.log 2 ≤ 4 * e * totalWeight K := by
        nlinarith [hstep, htw.le]
      linarith
    nlinarith [h1, hh1]
  have hidx : index (fun _ ↦ (e : ℝ)) ξ P
      = ENNReal.ofReal (e : ℝ)⁻¹ * (q.rootMultiplicity (ξ default) : ℝ≥0∞) := by
    have hweightEq (d : σ → ℝ) (hd : ∀ j, 0 ≤ d j) (Q : MvPolynomial σ K) :
        index d ξ Q = weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) (taylorAt ξ Q) := by
      have hw (μ : σ →₀ ℕ) :
          Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) μ =
            ENNReal.ofReal (μ.sum fun j k ↦ k / d j) := by
        classical
        rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
          ENNReal.ofReal_sum_of_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (hd j)]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), div_eq_mul_inv]
      refine le_antisymm ?_ ?_
      · refine Finset.le_inf fun μ hμ ↦ ?_
        rw [hw]
        have hcoeff := MvPolynomial.mem_support_iff.mp hμ
        rw [coeff_taylorAt] at hcoeff
        exact iInf_le_of_le μ (iInf_le _ hcoeff)
      · refine le_iInf fun μ ↦ le_iInf fun hμ ↦ ?_
        rw [← hw]
        exact Finset.inf_le (MvPolynomial.mem_support_iff.mpr (by rwa [coeff_taylorAt]))
    have hscale : index (fun j ↦ (e : ℝ) * (1 : ℝ)) ξ P =
        ENNReal.ofReal (e : ℝ)⁻¹ * index (fun _ ↦ (1 : ℝ)) ξ P := by
      have hcd : ∀ _j : σ, 0 ≤ (e : ℝ) * (1 : ℝ) := fun _ ↦ by positivity
      have hw : (fun j : σ ↦ ENNReal.ofReal ((e : ℝ) * (1 : ℝ))⁻¹)
          = fun j ↦ ENNReal.ofReal (e : ℝ)⁻¹ * ENNReal.ofReal (1 : ℝ)⁻¹ := by
        funext j
        rw [mul_inv, ENNReal.ofReal_mul (by positivity)]
      rw [hweightEq _ hcd, hweightEq _ (fun _ ↦ zero_le_one), hw,
        weightedOrder_const_mul (ENNReal.ofReal_pos.mpr (inv_pos.mpr hep)).ne' _ _]
    have hξ : ξ = fun _ ↦ ξ default := funext fun j ↦ by rw [Subsingleton.elim j default]
    rw [show (fun _ : σ ↦ (e : ℝ)) = fun _ : σ ↦ (e : ℝ) * 1 by funext; ring,
      hscale, hξ, index_of_unique _ hP]
  rw [hidx, ← ENNReal.ofReal_natCast]
  calc ENNReal.ofReal (e : ℝ)⁻¹ * ENNReal.ofReal (q.rootMultiplicity (ξ default) : ℝ)
      ≤ ENNReal.ofReal (e : ℝ)⁻¹ * ENNReal.ofReal (s * e) := by
        gcongr
    _ = ENNReal.ofReal s := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end MvPolynomial
