/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteInterpolation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteInterpolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bihomogeneous interpolation of selected first-order evaluations. -/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Bihomogeneous products isolate values and first derivatives at points in two pencils. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteInterpolation

open scoped BigOperators DualNumber
open TrivSqZeroExt

section

variable {K : Type*} [Field K] {σ τ ι : Type*}

/-- The two weights on coordinates of a pair of projective spaces. -/
def weight : σ ⊕ τ → ℕ × ℕ :=
  Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

private abbrev P (σ τ K : Type*) [Field K] := MvPolynomial (σ ⊕ τ) K

private lemma product_homogeneous (s : Finset ι) (p : ι → P σ τ K)
    (hp : ∀ j ∈ s, (p j).IsWeightedHomogeneous weight (1, 1)) :
    (∏ j ∈ s, p j).IsWeightedHomogeneous weight (s.card, s.card) := by
  convert MvPolynomial.IsWeightedHomogeneous.prod s p (fun _ => (1, 1)) hp using 1
  ext <;> simp

private lemma isolate_bilinear [Fintype ι]
    (eval : ι → P σ τ K →ₐ[K] K[ε]) (i : ι) (separate : ι → P σ τ K)
    (padding : P σ τ K)
    (hsep : ∀ j, j ≠ i → (separate j).IsWeightedHomogeneous weight (1, 1))
    (hvanish : ∀ j, j ≠ i → eval j (separate j) = 0)
    (hkeep : ∀ j, j ≠ i → (eval i (separate j)).fst ≠ 0)
    (hpad : padding.IsWeightedHomogeneous weight (1, 1)) :
    ∃ p : P σ τ K, p.IsWeightedHomogeneous weight (Fintype.card ι, Fintype.card ι) ∧
      (∀ j, j ≠ i → eval j p = 0) ∧
      ∃ u : K[ε], u.fst ≠ 0 ∧ eval i p = u * eval i padding := by
  classical
  let other := (Finset.univ : Finset ι).erase i
  let base := ∏ j ∈ other, separate j
  have hdegree : other.card + 1 = Fintype.card ι := by
    simpa only [other, Finset.card_univ] using
      Finset.card_erase_add_one (Finset.mem_univ i)
  have hb : base.IsWeightedHomogeneous weight (other.card, other.card) :=
    product_homogeneous other separate (fun j hj => hsep j (Finset.mem_erase.mp hj).1)
  have hbase_zero (j : ι) (hj : j ≠ i) : eval j base = 0 := by
    dsimp only [base]
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (hvanish j hj)
  have hbase_nonzero : (eval i base).fst ≠ 0 := by
    let evalFst := (fstHom K K K).toRingHom.comp (eval i).toRingHom
    change evalFst base ≠ 0
    dsimp only [base]
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j hj => hkeep j (Finset.mem_erase.mp hj).1)
  refine ⟨base * padding, ?_, ?_, eval i base, hbase_nonzero, map_mul _ _ _⟩
  · simpa only [Prod.mk_add_mk, hdegree] using hb.mul hpad
  · intro j hj
    rw [map_mul, hbase_zero j hj, zero_mul]

end

section Dimension

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Fintype ι]

/-- Values at all points and independently detected derivatives at selected points
give a lower bound for the dimension of any space carrying the evaluations. -/
theorem finrank_ge_values_and_derivatives (s : Finset ι)
    (value : ι → Module.Dual K V) (deriv : (↑s : Set ι) → Module.Dual K V)
    (hv : ∀ i, ∃ p : V, value i p ≠ 0 ∧ ∀ j, j ≠ i → value j p = 0)
    (hd : ∀ i, ∃ p : V, deriv i p ≠ 0 ∧ (∀ j, value j p = 0) ∧
      ∀ j, j ≠ i → deriv j p = 0) :
    Fintype.card ι + s.card ≤ Module.finrank K V := by
  classical
  let read := Sum.elim value deriv
  have hli : LinearIndependent K read := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have he (p : V) :
        (∑ i, c (Sum.inl i) * value i p) +
          (∑ i, c (Sum.inr i) * deriv i p) = 0 := by
      have hp := congrArg (fun f : Module.Dual K V => f p) hc
      simpa only [Fintype.sum_sum_type, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.zero_apply, smul_eq_mul, read, Sum.elim_inl, Sum.elim_inr] using hp
    have hc' (i : (↑s : Set ι)) : c (Sum.inr i) = 0 := by
      obtain ⟨p, hi, hp, hq⟩ := hd i
      have hrel := he p
      simp only [hp, mul_zero, Finset.sum_const_zero, zero_add] at hrel
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ hj => by rw [hq j hj, mul_zero])] at hrel
      exact (mul_eq_zero.mp hrel).resolve_right hi
    intro i
    rcases i with i | i
    · obtain ⟨p, hi, hp⟩ := hv i
      have hrel := he p
      simp only [hc', zero_mul, Finset.sum_const_zero, add_zero] at hrel
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ hj => by rw [hp j hj, mul_zero])] at hrel
      exact (mul_eq_zero.mp hrel).resolve_right hi
    · exact hc' i
  have hcard : Fintype.card (↑s : Set ι) = s.card := Fintype.card_coe s
  simpa only [Fintype.card_sum, hcard, Subspace.dual_finrank_eq] using
    hli.fintype_card_le_finrank

end Dimension

section Quotient

variable {K : Type*} [Field K] {σ τ ι : Type*} [Fintype ι]

private abbrev block (σ τ K : Type*) [Field K] (n : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule K (weight : σ ⊕ τ → ℕ × ℕ) (n, n)

/-- At each selected point, pairwise bilinear separators and a nonvanishing bilinear
form give an independent evaluation. A bilinear form with only a nonzero first-order
term gives an additional independent derivative in the same homogeneous quotient. -/
theorem finrank_quotient_ge_of_bilinear_separators
    [Module.Finite K (block σ τ K (Fintype.card ι))]
    (equations : Ideal (P σ τ K)) (s : Finset ι)
    (eval : ι → P σ τ K →ₐ[K] K[ε])
    (hvanish : ∀ i, ∀ p ∈ equations, (eval i p).fst = 0)
    (hvanishDeriv : ∀ i ∈ s, ∀ p ∈ equations, (eval i p).snd = 0)
    (hsep : ∀ i j, j ≠ i → ∃ p : P σ τ K,
      p.IsWeightedHomogeneous weight (1, 1) ∧ eval j p = 0 ∧ (eval i p).fst ≠ 0)
    (hvalue : ∀ i, ∃ p : P σ τ K,
      p.IsWeightedHomogeneous weight (1, 1) ∧ (eval i p).fst ≠ 0)
    (hderiv : ∀ i ∈ s, ∃ p : P σ τ K,
      p.IsWeightedHomogeneous weight (1, 1) ∧ (eval i p).fst = 0 ∧ (eval i p).snd ≠ 0) :
    Fintype.card ι + s.card ≤ Module.finrank K
      (block σ τ K (Fintype.card ι) ⧸
        (equations.restrictScalars K).comap (block σ τ K (Fintype.card ι)).subtype) := by
  classical
  let V := block σ τ K (Fintype.card ι)
  let J := (equations.restrictScalars K).comap V.subtype
  let valueMap (i : ι) : V →ₗ[K] K :=
    (fstHom K K K).toLinearMap.comp ((eval i).toLinearMap.comp V.subtype)
  let derivMap (i : ι) : V →ₗ[K] K :=
    (sndHom K K).comp ((eval i).toLinearMap.comp V.subtype)
  let value (i : ι) : V ⧸ J →ₗ[K] K :=
    J.liftQ (valueMap i) (fun p hp => hvanish i p.val hp)
  let deriv (i : (↑s : Set ι)) : V ⧸ J →ₗ[K] K :=
    J.liftQ (derivMap i.val) (fun p hp => hvanishDeriv i.val i.property p.val hp)
  have val_apply (i : ι) (p : V) : value i (J.mkQ p) = (eval i p.val).fst := rfl
  have der_apply (i : (↑s : Set ι)) (p : V) :
      deriv i (J.mkQ p) = (eval i.val p.val).snd := rfl
  have isolate (i : ι) (padding : P σ τ K)
      (hp : padding.IsWeightedHomogeneous weight (1, 1)) :
      ∃ p : V, (∀ j, j ≠ i → eval j p.val = 0) ∧
        ∃ u : K[ε], u.fst ≠ 0 ∧ eval i p.val = u * eval i padding := by
    have hex (j : ι) : ∃ p : P σ τ K, j ≠ i →
        p.IsWeightedHomogeneous weight (1, 1) ∧ eval j p = 0 ∧ (eval i p).fst ≠ 0 := by
      by_cases hj : j = i
      · exact ⟨0, fun h => (h hj).elim⟩
      · obtain ⟨p, h⟩ := hsep i j hj
        exact ⟨p, fun _ => h⟩
    choose sep hsep' using hex
    obtain ⟨p, hp', hz, u, hu, he⟩ := isolate_bilinear eval i sep padding
      (fun j hj => (hsep' j hj).1) (fun j hj => (hsep' j hj).2.1)
      (fun j hj => (hsep' j hj).2.2) hp
    exact ⟨⟨p, hp'⟩, hz, u, hu, he⟩
  apply finrank_ge_values_and_derivatives s value deriv
  · intro i
    obtain ⟨l, hl, hn⟩ := hvalue i
    obtain ⟨p, hz, u, hu, he⟩ := isolate i l hl
    refine ⟨J.mkQ p, ?_, ?_⟩
    · rw [val_apply, he, fst_mul]
      exact mul_ne_zero hu hn
    · intro j hj
      rw [val_apply, hz j hj, fst_zero]
  · intro i
    obtain ⟨l, hl, hfst, hsnd⟩ := hderiv i.val i.property
    obtain ⟨p, hz, u, hu, he⟩ := isolate i.val l hl
    refine ⟨J.mkQ p, ?_, ?_, ?_⟩
    · rw [der_apply, he, DualNumber.snd_mul, hfst, mul_zero, add_zero]
      exact mul_ne_zero hu hsnd
    · intro j
      rw [val_apply]
      by_cases hj : j = i.val
      · rw [hj, he, fst_mul, hfst, mul_zero]
      · rw [hz j hj, fst_zero]
    · intro j hj
      rw [der_apply, hz j.val (fun h => hj (Subtype.ext h)), snd_zero]

end Quotient

section Projective

variable {K : Type*} [Field K] {σ τ ι ρ : Type*}

private lemma exists_nonzero_coordinate (x : ρ → K) (hx : x ≠ 0) :
    ∃ a, x a ≠ 0 := by
  by_contra! hz
  exact hx (funext hz)

private lemma exists_nonzero_minor (x v : ρ → K) (hx : x ≠ 0)
    (h : ∀ c : K, v ≠ c • x) : ∃ a b, x a * v b - x b * v a ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_nonzero_coordinate x hx
  by_contra! hz
  apply h (v a / x a)
  funext b
  change v b = (v a / x a) * x b
  have he := sub_eq_zero.mp (hz a b)
  field_simp [ha]
  simpa only [mul_comm] using he

private noncomputable def coordinateMinor (side : ρ → σ ⊕ τ) (x : ρ → K) (a b : ρ) : P σ τ K :=
  MvPolynomial.C (x a) * MvPolynomial.X (side b) -
    MvPolynomial.C (x b) * MvPolynomial.X (side a)

private lemma minor_homogeneous (side : ρ → σ ⊕ τ) (x : ρ → K) (a b : ρ)
    (degree : ℕ × ℕ) (hside : ∀ j, weight (side j) = degree) :
    (coordinateMinor side x a b).IsWeightedHomogeneous weight degree := by
  unfold coordinateMinor
  have h (j : ρ) :
      (MvPolynomial.X (side j) : P σ τ K).IsWeightedHomogeneous weight degree := by
    simpa only [hside] using MvPolynomial.isWeightedHomogeneous_X K weight (side j)
  exact ((h b).C_mul _).sub ((h a).C_mul _)

private lemma eval_minor_fst (j : σ ⊕ τ → K[ε]) (side : ρ → σ ⊕ τ)
    (x : ρ → K) (a b : ρ) :
    (MvPolynomial.aeval j (coordinateMinor side x a b)).fst =
      x a * (j (side b)).fst - x b * (j (side a)).fst := by
  simp [coordinateMinor, algebraMap_eq_inl']

private lemma eval_minor_snd (j : σ ⊕ τ → K[ε]) (side : ρ → σ ⊕ τ)
    (x : ρ → K) (a b : ρ) :
    (MvPolynomial.aeval j (coordinateMinor side x a b)).snd =
      x a * (j (side b)).snd - x b * (j (side a)).snd := by
  simp [coordinateMinor, algebraMap_eq_inl']

private abbrev baseLeft (j : σ ⊕ τ → K[ε]) : σ → K := fun a => (j (.inl a)).fst
private abbrev baseRight (j : σ ⊕ τ → K[ε]) : τ → K := fun a => (j (.inr a)).fst

/-- At distinct projective projections, a product of linear forms vanishes to first
order at the unwanted point while keeping a nonzero value at the selected point. -/
theorem bilinear_separator (i j : σ ⊕ τ → K[ε])
    (hl : baseLeft j ≠ 0) (hr : baseRight j ≠ 0)
    (hleft : ∀ c : K, baseLeft i ≠ c • baseLeft j)
    (hright : ∀ c : K, baseRight i ≠ c • baseRight j) :
    ∃ p : P σ τ K, p.IsWeightedHomogeneous weight (1, 1) ∧
      MvPolynomial.aeval j p = 0 ∧ (MvPolynomial.aeval i p).fst ≠ 0 := by
  obtain ⟨a, b, hab⟩ := exists_nonzero_minor _ _ hl hleft
  obtain ⟨c, d, hcd⟩ := exists_nonzero_minor _ _ hr hright
  let l : P σ τ K := coordinateMinor Sum.inl (baseLeft j) a b
  let r : P σ τ K := coordinateMinor Sum.inr (baseRight j) c d
  refine ⟨l * r, ?_, ?_, ?_⟩
  · exact (minor_homogeneous _ _ _ _ (1, 0) (fun _ => rfl)).mul
      (minor_homogeneous _ _ _ _ (0, 1) (fun _ => rfl))
  · have h₁ : (MvPolynomial.aeval j l).fst = 0 := by
      simp [l, eval_minor_fst, mul_comm]
    have h₂ : (MvPolynomial.aeval j r).fst = 0 := by
      simp [r, eval_minor_fst, mul_comm]
    rw [map_mul]
    exact TrivSqZeroExt.ext
      (by simp [h₁, h₂]) (by simp [DualNumber.snd_mul, h₁, h₂])
  · rw [map_mul, fst_mul]
    exact mul_ne_zero (by simpa only [l, eval_minor_fst] using hab)
      (by simpa only [r, eval_minor_fst] using hcd)

private lemma bilinear_value (j : σ ⊕ τ → K[ε])
    (hl : baseLeft j ≠ 0) (hr : baseRight j ≠ 0) :
    ∃ p : P σ τ K, p.IsWeightedHomogeneous weight (1, 1) ∧
      (MvPolynomial.aeval j p).fst ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_nonzero_coordinate _ hl
  obtain ⟨b, hb⟩ := exists_nonzero_coordinate _ hr
  refine ⟨MvPolynomial.X (.inl a) * MvPolynomial.X (.inr b), ?_, ?_⟩
  · exact (MvPolynomial.isWeightedHomogeneous_X K weight (.inl a)).mul
      (MvPolynomial.isWeightedHomogeneous_X K weight (.inr b))
  · simpa only [map_mul, MvPolynomial.aeval_X, fst_mul] using mul_ne_zero ha hb

private lemma bilinear_derivative {side other : Type*}
    (j : σ ⊕ τ → K[ε]) (e : side → σ ⊕ τ) (f : other → σ ⊕ τ)
    (m n : ℕ × ℕ) (hm : ∀ a, weight (e a) = m) (hn : ∀ a, weight (f a) = n)
    (hdegree : m + n = (1, 1))
    (he : (fun a => (j (e a)).fst) ≠ 0) (hf : (fun a => (j (f a)).fst) ≠ 0)
    (hmove : ∀ c : K, (fun a => (j (e a)).snd) ≠ c • (fun a => (j (e a)).fst)) :
    ∃ p : P σ τ K, p.IsWeightedHomogeneous weight (1, 1) ∧
      (MvPolynomial.aeval j p).fst = 0 ∧ (MvPolynomial.aeval j p).snd ≠ 0 := by
  obtain ⟨a, b, hab⟩ := exists_nonzero_minor _ _ he hmove
  obtain ⟨c, hc⟩ := exists_nonzero_coordinate _ hf
  let l := coordinateMinor e (fun a => (j (e a)).fst) a b
  have hfst : (MvPolynomial.aeval j l).fst = 0 := by
    simp [l, eval_minor_fst, mul_comm]
  have hsnd : (MvPolynomial.aeval j l).snd ≠ 0 := by
    simpa only [l, eval_minor_snd] using hab
  refine ⟨l * MvPolynomial.X (f c), ?_, ?_, ?_⟩
  · have hl := minor_homogeneous e (fun a => (j (e a)).fst) a b m hm
    have hx : (MvPolynomial.X (f c) : P σ τ K).IsWeightedHomogeneous weight n := by
      simpa only [hn] using MvPolynomial.isWeightedHomogeneous_X K weight (f c)
    rw [← hdegree]
    exact hl.mul hx
  · rw [map_mul, fst_mul, hfst, zero_mul]
  · simpa only [map_mul, MvPolynomial.aeval_X, DualNumber.snd_mul, hfst, zero_mul, zero_add]
      using mul_ne_zero hsnd hc

/-- Distinct projections and a moving projective tangent give the indicated
lower bound on the dimension of the homogeneous component modulo the equations. -/
theorem finrank_quotient_ge_of_projective_points [Fintype ι]
    [Module.Finite K (block σ τ K (Fintype.card ι))]
    (equations : Ideal (P σ τ K)) (points : ι → σ ⊕ τ → K[ε]) (s : Finset ι)
    (hl : ∀ i, baseLeft (points i) ≠ 0) (hr : ∀ i, baseRight (points i) ≠ 0)
    (hleft : ∀ i j, j ≠ i → ∀ c : K, baseLeft (points i) ≠ c • baseLeft (points j))
    (hright : ∀ i j, j ≠ i → ∀ c : K, baseRight (points i) ≠ c • baseRight (points j))
    (hmove : ∀ i ∈ s,
      (∀ c : K, (fun a => (points i (.inl a)).snd) ≠ c • baseLeft (points i)) ∨
      (∀ c : K, (fun a => (points i (.inr a)).snd) ≠ c • baseRight (points i)))
    (hvanish : ∀ i, ∀ p ∈ equations, (MvPolynomial.aeval (points i) p).fst = 0)
    (hvanishDeriv : ∀ i ∈ s, ∀ p ∈ equations, (MvPolynomial.aeval (points i) p).snd = 0) :
    Fintype.card ι + s.card ≤ Module.finrank K
      (block σ τ K (Fintype.card ι) ⧸
        (equations.restrictScalars K).comap (block σ τ K (Fintype.card ι)).subtype) := by
  apply finrank_quotient_ge_of_bilinear_separators equations s
    (fun i => MvPolynomial.aeval (points i)) hvanish hvanishDeriv
  · intro i j hj
    exact bilinear_separator (points i) (points j) (hl j) (hr j)
      (hleft i j hj) (hright i j hj)
  · exact fun i => bilinear_value (points i) (hl i) (hr i)
  · intro i hi
    rcases hmove i hi with h | h
    · exact bilinear_derivative (points i) Sum.inl Sum.inr (1, 0) (0, 1)
        (fun _ => rfl) (fun _ => rfl) rfl (hl i) (hr i) h
    · exact bilinear_derivative (points i) Sum.inr Sum.inl (0, 1) (1, 0)
        (fun _ => rfl) (fun _ => rfl) rfl (hr i) (hl i) h

end Projective

section HomogeneousRank

open MvPolynomial

variable {K σ : Type*} [Field K] [Finite σ]

/-- If the degree-`n` part of a homogeneous quotient has dimension at most one,
projective evaluation separates any two nonproportional common zeros. -/
theorem common_zeros_proportional_of_finrank_le_one
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (hn : n ≠ 0) (x y : σ → K) (hx : x ≠ 0)
    (hitX : ∀ p ∈ I, aeval x p = 0) (hitY : ∀ p ∈ I, aeval y p = 0)
    (hD : Module.finrank K (LinearMap.range
      ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (homogeneousSubmodule σ K n).subtype)) ≤ 1) :
    ∃ c : K, y = c • x := by
  classical
  by_contra! notProportional
  obtain ⟨a, b, hab⟩ := exists_nonzero_minor x y hx notProportional
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate x hx
  let S := homogeneousSubmodule σ K n
  let q : MvPolynomial σ K →ₐ[K] MvPolynomial σ K ⧸ I := Ideal.Quotient.mkₐ K I
  let image : S →ₗ[K] MvPolynomial σ K ⧸ I := q.toLinearMap.comp S.subtype
  let W := LinearMap.range image
  let : Module.Finite K S := Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K n)
  let : Module.Finite K W := Module.Finite.of_surjective image.rangeRestrict
    (LinearMap.surjective_rangeRestrict image)
  let valueX : W →ₗ[K] K := (Ideal.Quotient.liftₐ I (aeval x) hitX).toLinearMap.comp W.subtype
  let valueY : W →ₗ[K] K := (Ideal.Quotient.liftₐ I (aeval y) hitY).toLinearMap.comp W.subtype
  have valueX_apply (f : S) : valueX (image.rangeRestrict f) = aeval x f.val := by
    exact congrFun (congrArg DFunLike.coe (Ideal.Quotient.liftₐ_comp I (aeval x) hitX)) f.val
  have valueY_apply (f : S) : valueY (image.rangeRestrict f) = aeval y f.val := by
    exact congrFun (congrArg DFunLike.coe (Ideal.Quotient.liftₐ_comp I (aeval y) hitY)) f.val
  let first : S := ⟨X i ^ n, isHomogeneous_X_pow i n⟩
  let linearForm : MvPolynomial σ K := C (x a) * X b - C (x b) * X a
  have hform : linearForm.IsHomogeneous 1 :=
    (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_C_mul_X _ _)
  let second : S := ⟨linearForm ^ n, by
    change (linearForm ^ n).IsHomogeneous n
    simpa only [one_mul] using hform.pow n⟩
  have hfirst : valueX (image.rangeRestrict first) ≠ 0 := by
    rw [valueX_apply]
    simpa [first, map_pow, aeval_X] using pow_ne_zero n hi
  have hsecondX : valueX (image.rangeRestrict second) = 0 := by
    rw [valueX_apply]
    simp [second, linearForm, mul_comm, hn]
  have hsecondY : valueY (image.rangeRestrict second) ≠ 0 := by
    rw [valueY_apply]
    simpa [second, linearForm, aeval_C] using pow_ne_zero n hab
  obtain ⟨generator, spans⟩ := finrank_le_one_iff.mp (show Module.finrank K W ≤ 1 from hD)
  obtain ⟨u, hu⟩ := spans (image.rangeRestrict first)
  obtain ⟨v, hv⟩ := spans (image.rangeRestrict second)
  have hgen : valueX generator ≠ 0 := by
    intro hzero
    apply hfirst
    rw [← hu, map_smul, hzero, smul_zero]
  have hvx : v * valueX generator = 0 := by
    rw [← smul_eq_mul, ← map_smul, hv, hsecondX]
  have hv0 := (mul_eq_zero.mp hvx).resolve_right hgen
  apply hsecondY
  rw [← hv, hv0, zero_smul, map_zero]

end HomogeneousRank

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteInterpolation
