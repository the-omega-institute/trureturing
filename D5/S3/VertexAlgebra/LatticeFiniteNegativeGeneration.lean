/- GID: D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeFiniteNegativeGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite family of actual lattice fields generates the full carrier by negative modes. -/

/-
proof_shape: finite_negative_generation: content
admission_basis: escape-witness
escape_witness: Sign-compatible quadratic descent puts every integral charge
state in the negative-word span of one fixed finite family of actual fields.
The induction constructs reachability on the unbounded charge group; ordinary
coefficient normalization and linear-span closure alone do not supply it.
The bilinear identities, positivity, finite-box, descent-step and coefficient
helpers are consumed proof organization, not separate new mathematical claims.
Direct frozen supplier:
  D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality.actual_creation_coefficient_transport:
  sha256:4442812cb5ae90872fb9b571adf34e18d7498324c6f46c07fefb7f8e0cb7c6b7.
  .actualField: sha256:db23a0480c1abf47b2c6b7cd3f7f4be30592ed0b506b751cf10bb0976daa91a3.
  .bilinear: sha256:fee6616d4d84c7c672be2490ede6d2420d87ffe28ad5f7c5fd93d145e3860d6b.
The current realization is described by Bakalov--Kac, arXiv math/0402315v1,
section 4.1, (4.4), (4.5), (4.10), (4.12). Its Theorem 4.1 uses all charges;
the finite negative-only family here is deduced using positive definiteness.
-/

import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

open LatticeGeneratingFieldLocality MvPolynomial Matrix
open scoped BigOperators

noncomputable section

/-- The neutral current on one charge sector, in normalized mode indexing. -/
def neutralPolynomialMode (D : LatticeData) (i : Fin D.rank) (δ : Charge D)
    (m : ℤ) : Module.End ℂ (Oscillator D) :=
  if m < 0 then LinearMap.mulLeft ℂ (X (i, (-m - 1).toNat))
  else if m = 0 then (bilinear D (unitCharge D i) δ : ℂ) • LinearMap.id
  else (m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) • (pderiv (j, (m - 1).toNat)).toLinearMap

/-- The actual Heisenberg mode preserves charge and acts on the oscillator polynomial. -/
def neutralMode (D : LatticeData) (i : Fin D.rank) (m : ℤ) :
    Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun δ => (Finsupp.lsingle δ).comp (neutralPolynomialMode D i δ m))

private theorem neutralMode_truncation (D : LatticeData) (i : Fin D.rank) (v : Carrier D) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) < m → neutralMode D i m v = 0 := by
  classical
  let N := v.support.sup (fun δ => (v δ).vars.sup (fun x => x.2)) + 1
  refine ⟨N, ?_⟩
  intro m hm
  have hmpos : 0 < m := by omega
  rw [neutralMode, Finsupp.lsum_apply]
  change (∑ δ ∈ v.support, _) = 0
  apply Finset.sum_eq_zero
  intro δ hδ
  have hderiv (j : Fin D.rank) : pderiv (j, (m - 1).toNat) (v δ) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro hj
    have h1 := Finset.le_sup (f := fun x : Index D => x.2) hj
    have h2 := Finset.le_sup (f := fun δ => (v δ).vars.sup (fun x => x.2)) hδ
    have h3 : (m - 1).toNat < N := lt_of_le_of_lt (le_trans h1 h2) (Nat.lt_succ_self _)
    have ht : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
    omega
  have hderiv' (j : Fin D.rank) : pderiv (j, m.toNat - 1) (v δ) = 0 := by
    simpa using hderiv j
  simp [neutralPolynomialMode, not_lt.mpr hmpos.le, ne_of_gt hmpos, hderiv']

/-- The finite neutral family has the full creation, charge, and annihilation modes. -/
def neutralField (D : LatticeData) (i : Fin D.rank) : VertexOperator ℂ (Carrier D) :=
  VertexOperator.of_coeff (fun k => neutralMode D i (-k - 1)) (by
    intro v
    obtain ⟨N, hN⟩ := neutralMode_truncation D i v
    refine ⟨-(N : ℤ) - 1, ?_⟩
    intro k hk
    by_contra h
    exact hk (hN (-k - 1) (by omega)))

/-- There are only finitely many field labels; negative mode orders are unrestricted. -/
abbrev Generator (D : LatticeData) (S : Finset (Charge D)) :=
  Fin D.rank ⊕ {β : Charge D // β ∈ S}

def generatingField (D : LatticeData) (S : Finset (Charge D)) :
    Generator D S → VertexOperator ℂ (Carrier D)
  | .inl i => neutralField D i
  | .inr β => actualField D β.1

/-- A right-nested word of actual negative normalized coefficients applied to vacuum. -/
def negativeWord (D : LatticeData) (S : Finset (Charge D)) :
    List (Generator D S × ℕ) → Carrier D
  | [] => Finsupp.single 0 1
  | (a, n) :: w => VertexOperator.ncoeff (generatingField D S a) (-(n : ℤ) - 1)
      (negativeWord D S w)

def negativeWordSpan (D : LatticeData) (S : Finset (Charge D)) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ (Set.range (negativeWord D S))

private theorem bilinear_unit (D : LatticeData) (i : Fin D.rank) (α : Charge D) :
    bilinear D (unitCharge D i) α = ∑ j, D.G i j * α j := by
  classical
  simp [bilinear, unitCharge]

private theorem bilinear_symmetric (D : LatticeData) (α β : Charge D) :
    bilinear D α β = bilinear D β α := by
  rw [bilinear, bilinear, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [D.symmetric j i]
  ring

private theorem bilinear_sub_left (D : LatticeData) (α β γ : Charge D) :
    bilinear D (α - β) γ = bilinear D α γ - bilinear D β γ := by
  simp [bilinear, sub_mul, Finset.sum_sub_distrib]

private theorem bilinear_sub_right (D : LatticeData) (α β γ : Charge D) :
    bilinear D α (β - γ) = bilinear D α β - bilinear D α γ := by
  simp [bilinear, mul_sub, Finset.sum_sub_distrib]

private theorem norm_positive (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (α : Charge D) (hα : α ≠ 0) :
    0 < bilinear D α α := by
  have hr : (fun i => (α i : ℝ)) ≠ 0 := by
    intro h
    apply hα
    ext i
    have hi : (α i : ℝ) = 0 := congrFun h i
    change α i = 0
    exact_mod_cast hi
  have h := hD.dotProduct_mulVec_pos hr
  have heq : (bilinear D α α : ℝ) =
      star (fun i => (α i : ℝ)) ⬝ᵥ ((D.G.map (Int.cast : ℤ → ℝ)) *ᵥ
        (fun i => (α i : ℝ))) := by
    simp [bilinear, dotProduct, Matrix.mulVec, Matrix.map_apply,
      Finset.mul_sum, Int.cast_sum, Int.cast_mul, mul_assoc]
  rw [← heq] at h
  exact_mod_cast h

private theorem norm_nonnegative (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (α : Charge D) :
    0 ≤ bilinear D α α := by
  by_cases hα : α = 0
  · simp [hα, bilinear]
  · exact (norm_positive D hD α hα).le

private theorem smallCharges_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    {α : Charge D | ∀ i, |bilinear D (unitCharge D i) α| < D.G i i}.Finite := by
  classical
  let f : Charge D → Charge D := fun α i => bilinear D (unitCharge D i) α
  have hf : Function.Injective f := by
    intro α β h
    by_contra hne
    have hn := norm_positive D hD (α - β) (sub_ne_zero.mpr hne)
    have hz : ∀ i, bilinear D (unitCharge D i) (α - β) = 0 := by
      intro i
      rw [bilinear_sub_right]
      exact sub_eq_zero.mpr (congrFun h i)
    have hq : bilinear D (α - β) (α - β) = 0 := by
      simp only [bilinear, Pi.sub_apply]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      have hz' : ∀ i, ∑ j, D.G i j * (α j - β j) = 0 := by
        simpa only [bilinear_unit, Pi.sub_apply] using hz
      simp [hz']
    omega
  have hb : {x : Charge D | ∀ i, x i ∈ Set.Ioo (-D.G i i) (D.G i i)}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Ioo _ _)
  have hp := hb.preimage hf.injOn
  apply hp.subset
  intro α hα
  change ∀ i, f α i ∈ Set.Ioo (-D.G i i) (D.G i i)
  intro i
  exact abs_lt.mp (hα i)


private theorem bilinear_neg_left (D : LatticeData) (α β : Charge D) :
    bilinear D (-α) β = -bilinear D α β := by
  simp [bilinear, Finset.sum_neg_distrib]

private theorem bilinear_neg_right (D : LatticeData) (α β : Charge D) :
    bilinear D α (-β) = -bilinear D α β := by
  simp [bilinear, Finset.sum_neg_distrib]

private theorem norm_sub (D : LatticeData) (α β : Charge D) :
    bilinear D (α - β) (α - β) =
      bilinear D α α - 2 * bilinear D β α + bilinear D β β := by
  rw [bilinear_sub_left, bilinear_sub_right, bilinear_sub_right,
    bilinear_symmetric D α β]
  ring

/-- Outside the finite Gram-coordinate box, a signed basis step reduces the full norm
and has nonnegative pairing with its predecessor. -/
private theorem charge_descent (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (α : Charge D)
    (hα : ¬ ∀ i, |bilinear D (unitCharge D i) α| < D.G i i) :
    ∃ (i : Fin D.rank) (β : Charge D),
      (β = unitCharge D i ∨ β = -unitCharge D i) ∧
      0 ≤ bilinear D β (α - β) ∧
      bilinear D (α - β) (α - β) < bilinear D α α := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hα
  have hd : 0 < D.G i i := by
    have he : unitCharge D i ≠ 0 := by
      intro h
      have := congrFun h i
      simp [unitCharge] at this
    simpa [bilinear_unit, unitCharge] using norm_positive D hD (unitCharge D i) he
  have hee : bilinear D (unitCharge D i) (unitCharge D i) = D.G i i := by
    simp [bilinear_unit, unitCharge]
  have hb : D.G i i ≤ |bilinear D (unitCharge D i) α| := le_of_not_gt hi
  by_cases hs : 0 ≤ bilinear D (unitCharge D i) α
  · refine ⟨i, unitCharge D i, Or.inl rfl, ?_, ?_⟩
    · rw [bilinear_sub_right, hee]
      rw [abs_of_nonneg hs] at hb
      omega
    · rw [norm_sub, hee]
      rw [abs_of_nonneg hs] at hb
      omega
  · refine ⟨i, -unitCharge D i, Or.inr rfl, ?_, ?_⟩
    · rw [bilinear_sub_right, bilinear_neg_left, bilinear_neg_left,
        bilinear_neg_right, hee]
      rw [abs_of_neg (lt_of_not_ge hs)] at hb
      omega
    · rw [norm_sub, bilinear_neg_left, bilinear_neg_left, bilinear_neg_right, hee]
      rw [abs_of_neg (lt_of_not_ge hs)] at hb
      omega

private theorem negativeWordSpan_closed (D : LatticeData) (S : Finset (Charge D))
    (a : Generator D S) (n : ℕ) (v : Carrier D) (hv : v ∈ negativeWordSpan D S) :
    VertexOperator.ncoeff (generatingField D S a) (-(n : ℤ) - 1) v ∈
      negativeWordSpan D S := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, rfl⟩ := hv
    exact Submodule.subset_span ⟨(a,n) :: w, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (negativeWordSpan D S).add_mem ihx ihy
  | smul c x hx ih => simpa using (negativeWordSpan D S).smul_mem c ih

private theorem neutral_negative_single (D : LatticeData) (i : Fin D.rank)
    (n : ℕ) (δ : Charge D) (p : Oscillator D) :
    VertexOperator.ncoeff (neutralField D i) (-(n : ℤ) - 1) (Finsupp.single δ p) =
      Finsupp.single δ (X (i,n) * p) := by
  rw [neutralField, VertexOperator.ncoeff_of_coeff]
  have heq : -(-(-(n : ℤ) - 1) - 1) - 1 = -(n : ℤ) - 1 := by omega
  rw [heq]
  simp [neutralMode, neutralPolynomialMode, show -(n : ℤ) - 1 < 0 by omega]

private theorem actual_negative_single (D : LatticeData) (β γ : Charge D)
    (_h : 0 ≤ bilinear D β γ) :
    VertexOperator.ncoeff (actualField D β) (-bilinear D β γ - 1)
      (Finsupp.single γ 1) = epsilon D β γ • Finsupp.single (β + γ) 1 := by
  classical
  have hc : creationCoeff D β 0 = 1 := by
    have hA : PowerSeries.constantCoeff (creationSeries D β) = 0 := by
      simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [creationCoeff, dif_neg (by omega)]
    simp only [Int.toNat_zero]
    rw [creationExponential, PowerSeries.coeff_subst'
      (PowerSeries.HasSubst.of_constantCoeff_zero' hA), finsum_eq_single _ 0]
    · simp
    · intro j hj
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hA]
      simp [hj]
  rw [actualField, VertexOperator.ncoeff_of_coeff]
  have hk : -(-bilinear D β γ - 1) - 1 = bilinear D β γ := by omega
  rw [hk, (actual_creation_coefficient_transport D β β).2.2.1]
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [rawSingle, translatedPolynomial, hs, hc]


/-- A finite charge set and the rank-many actual neutral currents generate every
finite-charge polynomial state by words whose normalized modes are all negative. -/
theorem finite_negative_generation (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ∃ S : Finset (Charge D), negativeWordSpan D S = ⊤ := by
  classical
  let A : Finset (Charge D) := (smallCharges_finite D hD).toFinset
  let S : Finset (Charge D) := A ∪
    (Finset.univ.image (unitCharge D) ∪ Finset.univ.image (fun i => -unitCharge D i))
  let W := negativeWordSpan D S
  have hsmall (α : Charge D) (hα : ∀ i, |bilinear D (unitCharge D i) α| < D.G i i) :
      α ∈ S := by
    apply Finset.mem_union_left
    exact (smallCharges_finite D hD).mem_toFinset.mpr hα
  have hstep (i : Fin D.rank) (β : Charge D)
      (hβ : β = unitCharge D i ∨ β = -unitCharge D i) : β ∈ S := by
    rcases hβ with rfl | rfl
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
  have hvac : Finsupp.single (0 : Charge D) (1 : Oscillator D) ∈ W :=
    Submodule.subset_span ⟨[], rfl⟩
  have hraise (β γ : Charge D) (hβ : β ∈ S) (hbg : 0 ≤ bilinear D β γ)
      (hγ : Finsupp.single γ (1 : Oscillator D) ∈ W) :
      Finsupp.single (β + γ) (1 : Oscillator D) ∈ W := by
    have hm := negativeWordSpan_closed D S (.inr ⟨β,hβ⟩)
      (bilinear D β γ).toNat _ hγ
    have hn : ((bilinear D β γ).toNat : ℤ) = bilinear D β γ := Int.toNat_of_nonneg hbg
    change VertexOperator.ncoeff (actualField D β) (-((bilinear D β γ).toNat : ℤ) - 1)
      (Finsupp.single γ 1) ∈ W at hm
    rw [hn, actual_negative_single D β γ hbg] at hm
    have hs := W.smul_mem (epsilon D β γ) hm
    have heps : epsilon D β γ * epsilon D β γ = 1 := by
      unfold epsilon paritySign
      split_ifs <;> norm_num
    simpa only [smul_smul, heps, one_smul] using hs
  have hcharge : ∀ q : ℕ, ∀ α : Charge D, (bilinear D α α).toNat = q →
      Finsupp.single α (1 : Oscillator D) ∈ W := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro α hq
      by_cases ha : ∀ i, |bilinear D (unitCharge D i) α| < D.G i i
      · have hz : bilinear D α 0 = 0 := by simp [bilinear]
        simpa using hraise α 0 (hsmall α ha) (by rw [hz]) hvac
      · obtain ⟨i, β, hβ, hbg, hlt⟩ := charge_descent D hD α ha
        have hnat : (bilinear D (α - β) (α - β)).toNat < q := by
          rw [← hq]
          have hg0 := norm_nonnegative D hD (α - β)
          omega
        have hg := ih _ hnat (α - β) rfl
        have hr := hraise β (α - β) (hstep i β hβ) hbg hg
        have heq : β + (α - β) = α := by abel
        rwa [heq] at hr
  have hpoly (α : Charge D) (p : Oscillator D) : Finsupp.single α p ∈ W := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      have hc := W.smul_mem c (hcharge _ α rfl)
      simpa [← Finsupp.single_smul, smul_eq_C_mul] using hc
    | add p q hp hq => simpa only [Finsupp.single_add] using W.add_mem hp hq
    | mul_X p x hp =>
      have hm := negativeWordSpan_closed D S (.inl x.1) x.2 _ hp
      change VertexOperator.ncoeff (neutralField D x.1) (-(x.2 : ℤ) - 1)
        (Finsupp.single α p) ∈ W at hm
      rw [neutral_negative_single] at hm
      simpa only [Prod.mk.eta, mul_comm] using hm
  refine ⟨S, top_unique ?_⟩
  intro v hv
  have hs : (∑ α ∈ v.support, Finsupp.single α (v α)) ∈ W :=
    W.sum_mem (fun α hα => hpoly α (v α))
  change v.sum (fun α p => Finsupp.single α p) ∈ W at hs
  simpa only [Finsupp.sum_single] using hs

end

end D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
