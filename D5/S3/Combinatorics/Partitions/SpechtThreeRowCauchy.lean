/- GID: D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtThreeRowCauchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three-variable Cauchy kernel has isolated strictly decreasing double coefficients. -/

/-
Source only: native elaboration, axiom closure, liveness and admission are unverified.
Unfinished audit: https://github.com/the-omega-institute/trureturing/issues/24542.
Classical Cauchy identity, not an originality claim. The nine-edge coefficient count is identified with finite contingency tables.
No standalone firstfreeze. Arbitrary degrees, not a finite-degree certificate.
-/
import D5.S3.Combinatorics.Partitions.SpechtThreeRowMixed
import Mathlib.RingTheory.MvPowerSeries.Basic
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

open private solution_unique
  from D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open private right_coefficient ev_right triProd
  from D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti.ThreeRowGram
open _root_.Equiv _root_.Equiv.Perm Finset

private def deltaProduct {R : Type*} [CommRing R] (x : Fin 3 → R) : R :=
  (x 0 - x 1) * (x 0 - x 2) * (x 1 - x 2)

/-- The cleared three-by-three Cauchy numerator, evaluated over any commutative ring. -/
private theorem cauchy_numerator {R : Type*} [CommRing R] (x y : Fin 3 → R) :
    (fun i : Fin 3 =>
      ![(1-x i*y 1)*(1-x i*y 2), (1-x i*y 0)*(1-x i*y 2),
        (1-x i*y 0)*(1-x i*y 1)]).det = deltaProduct x * deltaProduct y := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, deltaProduct]
  ring

/-- Cauchy's identity with specified inverses. No field, convergence or character
orthogonality is used. The product has exactly the nine labelled factors. -/
private theorem cauchy_inverse_identity {R : Type*} [CommRing R]
    (x y : Fin 3 → R) (q : Matrix (Fin 3) (Fin 3) R)
    (hq : ∀ i j, (1-x i*y j)*q i j = 1) :
    deltaProduct x * deltaProduct y * (∏ i, ∏ j, q i j) = q.det := by
  let v : Fin 3 → R := fun i => (1-x i*y 0)*(1-x i*y 1)*(1-x i*y 2)
  let N : Matrix (Fin 3) (Fin 3) R := fun i =>
    ![(1-x i*y 1)*(1-x i*y 2), (1-x i*y 0)*(1-x i*y 2),
      (1-x i*y 0)*(1-x i*y 1)]
  have he : (Matrix.of fun i j => v i * q i j) = N := by
    ext i j
    fin_cases j
    · change v i * q i 0 = (1-x i*y 1)*(1-x i*y 2)
      calc
        _ = ((1-x i*y 0)*q i 0)*((1-x i*y 1)*(1-x i*y 2)) := by dsimp [v]; ring
        _ = _ := by rw [hq]; ring
    · change v i * q i 1 = (1-x i*y 0)*(1-x i*y 2)
      calc
        _ = ((1-x i*y 1)*q i 1)*((1-x i*y 0)*(1-x i*y 2)) := by dsimp [v]; ring
        _ = _ := by rw [hq]; ring
    · change v i * q i 2 = (1-x i*y 0)*(1-x i*y 1)
      calc
        _ = ((1-x i*y 2)*q i 2)*((1-x i*y 0)*(1-x i*y 1)) := by dsimp [v]; ring
        _ = _ := by rw [hq]; ring
  have hn : (∏ i, v i) * q.det = deltaProduct x * deltaProduct y := by
    rw [← Matrix.det_mul_column, he]
    exact cauchy_numerator x y
  have hk : (∏ i, v i) * (∏ i, ∏ j, q i j) = 1 := by
    rw [← prod_mul_distrib]
    have hi (i : Fin 3) : v i * (∏ j, q i j) = 1 := by
      rw [Fin.prod_univ_three]
      calc
        _ = ((1-x i*y 0)*q i 0)*((1-x i*y 1)*q i 1)*((1-x i*y 2)*q i 2) := by
          dsimp [v]; ring
        _ = 1 := by rw [hq, hq, hq]; ring
    simp_rw [hi]
    simp
  calc
    _ = ((∏ i, v i) * q.det) * (∏ i, ∏ j, q i j) := by rw [hn]
    _ = ((∏ i, v i) * (∏ i, ∏ j, q i j)) * q.det := by ring
    _ = _ := by rw [hk, one_mul]

private abbrev Variables := Fin 3 ⊕ Fin 3
private abbrev Series := MvPowerSeries Variables ℤ

private def edgeWeight (i j : Fin 3) (k : ℕ) : Variables →₀ ℕ :=
  Finsupp.single (Sum.inl i) k + Finsupp.single (Sum.inr j) k

private theorem edgeWeight_add (i j : Fin 3) (k l : ℕ) :
    edgeWeight i j (k+l) = edgeWeight i j k + edgeWeight i j l := by
  ext t
  simp only [edgeWeight, Finsupp.add_apply, Finsupp.single_add]
  omega

/-- The geometric series of a single labelled edge, defined by its monomials. -/
private def edgeSeries (i j : Fin 3) : Series :=
  fun d => if ∃ k : ℕ, d = edgeWeight i j k then 1 else 0

private theorem edgeSeries_inverse (i j : Fin 3) :
    (1 - MvPowerSeries.monomial (edgeWeight i j 1) (1 : ℤ)) * edgeSeries i j = 1 := by
  classical
  apply MvPowerSeries.ext
  intro d
  simp only [sub_mul, one_mul, map_sub, MvPowerSeries.coeff_monomial_mul, one_mul,
    MvPowerSeries.coeff_one, MvPowerSeries.coeff_apply]
  by_cases he : ∃ k : ℕ, d = edgeWeight i j k
  · obtain ⟨k, rfl⟩ := he
    have hsub : edgeWeight i j k - edgeWeight i j 1 = edgeWeight i j (k-1) := by
      ext t
      rcases t with t | t <;> by_cases ht : t = i <;> by_cases ht' : t = j <;>
        simp [edgeWeight, Finsupp.single_apply, ht, ht']
    by_cases hk : k = 0
    · subst k
      simp [edgeSeries, edgeWeight, Finsupp.le_def]
    · have hle : edgeWeight i j 1 ≤ edgeWeight i j k := by
        intro t
        rcases t with t | t <;> by_cases ht : t = i <;> by_cases ht' : t = j <;>
          simp [edgeWeight, Finsupp.single_apply, ht, ht'] <;> omega
      have hne : edgeWeight i j k ≠ 0 := by
        intro h
        have hx := congrArg (fun e : Variables →₀ ℕ => e (Sum.inl i)) h
        exact hk (by simpa [edgeWeight] using hx)
      simp [edgeSeries, hle, hsub, hne]
  · have hd : d ≠ 0 := by
      intro h
      apply he
      exact ⟨0, by simp [h, edgeWeight]⟩
    have hsub : edgeWeight i j 1 ≤ d → ¬ ∃ k : ℕ, d-edgeWeight i j 1 = edgeWeight i j k := by
      intro hle
      rintro ⟨k, hk⟩
      apply he
      refine ⟨k+1, ?_⟩
      rw [edgeWeight_add, ← hk, tsub_add_cancel_of_le hle]
    by_cases hle : edgeWeight i j 1 ≤ d <;> simp [edgeSeries, he, hd, hle, hsub]

def doubleWeight (u v : Fin 3 → ℕ) : Variables →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim u v)

private theorem matching_product_coefficient (σ : Perm (Fin 3)) (u v : Fin 3 → ℕ) :
    MvPowerSeries.coeff (doubleWeight u v) (∏ i, edgeSeries i (σ i)) =
      if ∀ i, u i = v (σ i) then (1 : ℤ) else 0 := by
  classical
  let d := doubleWeight u v
  let L : Fin 3 →₀ (Variables →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm fun i => edgeWeight i (σ i) (u i)
  rw [MvPowerSeries.coeff_prod]
  have hnonzero (l : Fin 3 →₀ (Variables →₀ ℕ))
      (hl : l ∈ finsuppAntidiag univ d)
      (hp : (∏ i : Fin 3, MvPowerSeries.coeff (l i) (edgeSeries i (σ i))) ≠ 0) :
      l = L ∧ ∀ i, u i = v (σ i) := by
    have hk (i : Fin 3) : ∃ k : ℕ, l i = edgeWeight i (σ i) k := by
      have hi : MvPowerSeries.coeff (l i) (edgeSeries i (σ i)) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hp) i (mem_univ i)
      by_contra hn
      exact hi (by simp [MvPowerSeries.coeff_apply, edgeSeries, hn])
    choose k hk using hk
    have hs : ∑ i, l i = d := (mem_finsuppAntidiag.mp hl).1
    have hx (i : Fin 3) : k i = u i := by
      have h := congrArg (fun e : Variables →₀ ℕ => e (Sum.inl i)) hs
      simpa [hk, edgeWeight, d, doubleWeight] using h
    have hy (i : Fin 3) : k i = v (σ i) := by
      have h := congrArg (fun e : Variables →₀ ℕ => e (Sum.inr (σ i))) hs
      simpa [hk, edgeWeight, σ.injective.eq_iff, d, doubleWeight] using h
    refine ⟨?_, fun i => (hx i).symm.trans (hy i)⟩
    ext i t
    simp only [L, hk, hx]
  by_cases hm : ∀ i, u i = v (σ i)
  · rw [if_pos hm]
    have hL : L ∈ finsuppAntidiag univ d := by
      rw [mem_finsuppAntidiag]
      refine ⟨?_, subset_univ _⟩
      ext t
      rcases t with i | j
      · simp [L, edgeWeight, d, doubleWeight]
      · rw [← σ.apply_symm_apply j]
        simp [L, edgeWeight, σ.injective.eq_iff, d, doubleWeight, hm]
    rw [Finset.sum_eq_single L]
    · simp [L, MvPowerSeries.coeff_apply, edgeSeries]
    · intro l hl hne
      by_contra hp
      exact hne (hnonzero l hl hp).1
    · exact fun h => (h hL).elim
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro l hl
    by_contra hp
    exact hm (hnonzero l hl hp).2

private theorem strict_matching_unique (u v : Fin 3 → ℕ)
    (hu01 : u 1 < u 0) (hu12 : u 2 < u 1)
    (hv01 : v 1 < v 0) (hv12 : v 2 < v 1) (σ : Perm (Fin 3))
    (hm : ∀ i, u i = v (σ i)) : σ = 1 ∧ u = v := by
  have hne01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hne02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hne12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have hid : σ = 1 := by
    generalize e0 : σ 0 = i0 at *
    generalize e1 : σ 1 = i1 at *
    generalize e2 : σ 2 = i2 at *
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp_all
    all_goals first | omega | (ext i; fin_cases i <;> assumption)
  refine ⟨hid, funext fun i => ?_⟩
  simpa [hid] using hm i

/-- The geometric kernel on all nine labelled edges. -/
def cauchyKernel : Series := ∏ i : Fin 3, ∏ j : Fin 3, edgeSeries i j

/-- The two Vandermonde factors in six disjoint variables. -/
def doubleVandermonde : Series :=
  deltaProduct (fun i => MvPowerSeries.X (Sum.inl i)) *
    deltaProduct (fun j => MvPowerSeries.X (Sum.inr j))

private theorem coeff_cauchyKernel (n : ℕ) (a b : Fin 3 → ℕ) (ha : ∑ i, a i = n) :
    MvPowerSeries.coeff (doubleWeight a b) cauchyKernel =
      (contingencyCount n (fun i => (a i : ℤ)) (fun j => (b j : ℤ)) : ℤ) := by
  classical
  let d := doubleWeight a b
  let S := (finsuppAntidiag (univ : Finset (Fin 3 × Fin 3)) d).filter
    fun l => ∀ e, ∃ k : ℕ, l e = edgeWeight e.1 e.2 k
  let T := contingencyTables n (fun i => (a i : ℤ)) (fun j => (b j : ℤ))
  let toTable (l : (Fin 3 × Fin 3) →₀ (Variables →₀ ℕ)) : Fin 3 × Fin 3 → ℕ :=
    fun e => l e (Sum.inl e.1)
  let toDecomp (A : Fin 3 × Fin 3 → ℕ) : (Fin 3 × Fin 3) →₀ (Variables →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm fun e => edgeWeight e.1 e.2 (A e)
  have recover (l : (Fin 3 × Fin 3) →₀ (Variables →₀ ℕ)) (hl : l ∈ S) (e) :
      l e = edgeWeight e.1 e.2 (toTable l e) := by
    obtain ⟨k, hk⟩ := (mem_filter.mp hl).2 e
    have hx : toTable l e = k := by simp [toTable, hk, edgeWeight]
    rw [hx]
    exact hk
  have to_mem (l : (Fin 3 × Fin 3) →₀ (Variables →₀ ℕ)) (hl : l ∈ S) : toTable l ∈ T := by
    have hs := (mem_finsuppAntidiag.mp (mem_filter.mp hl).1).1
    have hrow (i : Fin 3) : ∑ j, toTable l (i,j) = a i := by
      have h := congrArg (fun e : Variables →₀ ℕ => e (Sum.inl i)) hs
      simpa [recover l hl, edgeWeight, Fintype.sum_prod_type, d, doubleWeight] using h
    have hcol (j : Fin 3) : ∑ i, toTable l (i,j) = b j := by
      have h := congrArg (fun e : Variables →₀ ℕ => e (Sum.inr j)) hs
      simpa [recover l hl, edgeWeight, Fintype.sum_prod_type, d, doubleWeight] using h
    apply mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_piAntidiag]
      refine ⟨?_, fun _ _ => mem_univ _⟩
      rw [Fintype.sum_prod_type]
      simp_rw [hrow]
      exact ha
    · intro i
      exact_mod_cast hrow i
    · intro j
      exact_mod_cast hcol j
  have from_mem (A : Fin 3 × Fin 3 → ℕ) (hA : A ∈ T) : toDecomp A ∈ S := by
    obtain ⟨-, hrow, hcol⟩ := mem_filter.mp hA
    apply mem_filter.mpr
    refine ⟨?_, fun e => ⟨A e, rfl⟩⟩
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    ext t
    rcases t with i | j
    · have h : ∑ j, A (i,j) = a i := by exact_mod_cast hrow i
      simpa [toDecomp, edgeWeight, Fintype.sum_prod_type, d, doubleWeight] using h
    · have h : ∑ i, A (i,j) = b j := by exact_mod_cast hcol j
      simpa [toDecomp, edgeWeight, Fintype.sum_prod_type, d, doubleWeight] using h
  have hcard : S.card = T.card := by
    apply card_bij' (fun l _ => toTable l) (fun A _ => toDecomp A) to_mem from_mem
    · intro l hl
      ext e t
      simpa only [toDecomp] using congrArg (fun w : Variables →₀ ℕ => w t) (recover l hl e).symm
    · intro A _
      funext e
      simp [toTable, toDecomp, edgeWeight]
  rw [cauchyKernel, ← Fintype.prod_prod_type, MvPowerSeries.coeff_prod]
  simp only [MvPowerSeries.coeff_apply, edgeSeries, prod_boole, mem_univ, forall_true_left]
  rw [sum_boole]
  change (S.card : ℤ) = (T.card : ℤ)
  exact_mod_cast hcard

/-- The Cauchy coefficient at two strictly decreasing triples is their Kronecker
 delta, uniformly in the size of the entries. This uses no Specht or Schur statement. -/
theorem cauchy_coefficient_delta (u v : Fin 3 → ℕ)
    (hu01 : u 1 < u 0) (hu12 : u 2 < u 1)
    (hv01 : v 1 < v 0) (hv12 : v 2 < v 1) :
    MvPowerSeries.coeff (doubleWeight u v) (doubleVandermonde * cauchyKernel) =
      if u = v then (1 : ℤ) else 0 := by
  classical
  have hid : doubleVandermonde * cauchyKernel =
      (fun i j : Fin 3 => edgeSeries i j).det := by
    apply cauchy_inverse_identity
    intro i j
    have hm : (MvPowerSeries.X (Sum.inl i) : Series) * MvPowerSeries.X (Sum.inr j) =
        MvPowerSeries.monomial (edgeWeight i j 1) (1 : ℤ) := by
      simp [MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, edgeWeight]
    rw [hm]
    exact edgeSeries_inverse i j
  rw [hid, Matrix.det_apply, map_sum]
  have hterm (σ : Perm (Fin 3)) :
      MvPowerSeries.coeff (doubleWeight u v)
        (sign σ • ∏ i, edgeSeries (σ i) i) =
        if σ = 1 ∧ u = v then (1 : ℤ) else 0 := by
    have hp : (∏ i, edgeSeries (σ i) i) = ∏ i, edgeSeries i (σ⁻¹ i) := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ (fun i => edgeSeries i (σ⁻¹ i))).symm
    simp only [Units.smul_def]
    rw [hp, map_smul, matching_product_coefficient]
    by_cases hm : ∀ i, u i = v (σ⁻¹ i)
    · obtain ⟨hs, he⟩ := strict_matching_unique u v hu01 hu12 hv01 hv12 σ⁻¹ hm
      have hs' : σ = 1 := by simpa using congrArg Inv.inv hs
      simp [hm, hs', he]
    · have hn : ¬ (σ = 1 ∧ u = v) := by rintro ⟨rfl, rfl⟩; exact hm (by simp)
      simp [hm, hn]
  simp_rw [hterm]
  by_cases he : u = v <;> simp [he]

private theorem side_vandermonde (f : Fin 3 → Variables) :
    deltaProduct (fun i => (MvPowerSeries.X (f i) : Series)) =
      ∑ σ : Perm (Fin 3), (sign σ : ℤ) •
        MvPowerSeries.monomial (Finsupp.mapDomain f (permutedStaircase σ)) (1 : ℤ) := by
  let φ : MvPolynomial (Fin 3) ℤ →+* Series :=
    MvPolynomial.coeToMvPowerSeries.ringHom.comp (MvPolynomial.rename f).toRingHom
  have h := congrArg φ vandermonde_eq_signed_monomials
  simpa [φ, D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3,
    deltaProduct, Units.smul_def] using h

private theorem sideWeights (σ τ : Perm (Fin 3)) :
    Finsupp.mapDomain Sum.inl (permutedStaircase σ) +
      Finsupp.mapDomain Sum.inr (permutedStaircase τ) =
        doubleWeight (fun i => staircase (σ i)) (fun j => staircase (τ j)) := by
  ext t
  rcases t with i | j
  · rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
    simp [doubleWeight, permutedStaircase]
  · rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inr_injective,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
    simp [doubleWeight, permutedStaircase]

private theorem doubleVandermonde_expansion :
    doubleVandermonde = ∑ σ : Perm (Fin 3), ∑ τ : Perm (Fin 3),
      ((sign σ : ℤ)*(sign τ : ℤ)) •
        MvPowerSeries.monomial
          (doubleWeight (fun i => staircase (σ i)) (fun j => staircase (τ j))) (1 : ℤ) := by
  rw [doubleVandermonde, side_vandermonde, side_vandermonde, sum_mul]
  simp_rw [mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    MvPowerSeries.monomial_mul_monomial, one_mul, sideWeights]

private theorem contingencyCount_zero_of_negative (n : ℕ) (a b : Fin 3 → ℤ)
    (h : (∃ i, a i < 0) ∨ (∃ j, b j < 0)) : contingencyCount n a b = 0 := by
  rw [contingencyCount, card_eq_zero, contingencyTables, filter_eq_empty_iff]
  intro A _ hA
  rcases h with ⟨i, hi⟩ | ⟨j, hj⟩
  · have ha := hA.1 i
    have hn := Int.natCast_nonneg (∑ j, A (i,j))
    omega
  · have hb := hA.2 j
    have hn := Int.natCast_nonneg (∑ i, A (i,j))
    omega

private theorem coeff_shifted_kernel {n : ℕ} (r q : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (σ τ : Perm (Fin 3)) :
    MvPowerSeries.coeff
      (doubleWeight (fun i => r i + staircase i) (fun j => q j + staircase j))
      (MvPowerSeries.monomial
        (doubleWeight (fun i => staircase (σ i)) (fun j => staircase (τ j))) (1 : ℤ) *
          cauchyKernel) = (contingencyCount n (shifted r σ) (shifted q τ) : ℤ) := by
  classical
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases h : doubleWeight (fun i => staircase (σ i)) (fun j => staircase (τ j)) ≤
      doubleWeight (fun i => r i + staircase i) (fun j => q j + staircase j)
  · rw [if_pos h, one_mul]
    let a : Fin 3 → ℕ := fun i => r i + staircase i - staircase (σ i)
    let b : Fin 3 → ℕ := fun i => q i + staircase i - staircase (τ i)
    have ha (i : Fin 3) : (a i : ℤ) = shifted r σ i := by
      have hi := h (Sum.inl i)
      have h₁ := i.isLt
      have h₂ := (σ i).isLt
      dsimp [doubleWeight, a, staircase, shifted] at *
      omega
    have hb (j : Fin 3) : (b j : ℤ) = shifted q τ j := by
      have hj := h (Sum.inr j)
      have h₁ := j.isLt
      have h₂ := (τ j).isLt
      dsimp [doubleWeight, b, staircase, shifted] at *
      omega
    have han : ∀ i, 0 ≤ shifted r σ i := fun i => (ha i) ▸ Int.natCast_nonneg (a i)
    have hat : ∑ i, a i = n := by
      have he : a = fun i => (shifted r σ i).toNat := by
        ext i
        rw [← ha]
        simp
      rw [he]
      exact shifted_nat_sum r hr σ han
    have he : doubleWeight (fun i => r i + staircase i) (fun j => q j + staircase j) -
        doubleWeight (fun i => staircase (σ i)) (fun j => staircase (τ j)) =
          doubleWeight a b := by
      ext t
      rcases t with i | j <;> rfl
    rw [he, coeff_cauchyKernel n a b hat]
    congr 2
    · exact funext ha
    · exact funext hb
  · rw [if_neg h]
    have hn : (∃ i, shifted r σ i < 0) ∨ (∃ j, shifted q τ j < 0) := by
      change ¬ ∀ t, _ at h
      obtain ⟨t, ht⟩ := not_forall.mp h
      rcases t with i | j
      · left
        refine ⟨i, ?_⟩
        have h₁ := i.isLt
        have h₂ := (σ i).isLt
        dsimp [doubleWeight, staircase, shifted] at *
        omega
      · right
        refine ⟨j, ?_⟩
        have h₁ := j.isLt
        have h₂ := (τ j).isLt
        dsimp [doubleWeight, staircase, shifted] at *
        omega
    rw [contingencyCount_zero_of_negative n _ _ hn, Nat.cast_zero]

/-- The signed six-by-six contingency matrix is exactly a double kernel
coefficient. Both margins are shifted in the integers before negative cases vanish. -/
private theorem signedContingencyGram_eq_kernelCoeff {n : ℕ} (r q : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) :
    signedContingencyGram n r q =
      MvPowerSeries.coeff
        (doubleWeight (fun i => r i + staircase i) (fun j => q j + staircase j))
        (doubleVandermonde * cauchyKernel) := by
  rw [doubleVandermonde_expansion, sum_mul]
  simp_rw [sum_mul, smul_mul_assoc, map_sum, map_smul, coeff_shifted_kernel r q hr,
    smul_eq_mul]
  rfl

/-- The finite signed contingency Gram is the Kronecker delta for decreasing
natural triples of every degree. No Specht assumption enters this identity. -/
theorem signedContingencyGram_eq_delta {n : ℕ} (r q : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (hr01 : r 1 ≤ r 0) (hr12 : r 2 ≤ r 1)
    (hq01 : q 1 ≤ q 0) (hq12 : q 2 ≤ q 1) :
    signedContingencyGram n r q = if r = q then 1 else 0 := by
  rw [signedContingencyGram_eq_kernelCoeff r q hr,
    cauchy_coefficient_delta _ _ (by simp [staircase]; omega) (by simp [staircase]; omega)
      (by simp [staircase]; omega) (by simp [staircase]; omega)]
  have he : (fun i => r i + staircase i) = (fun i => q i + staircase i) ↔ r = q := by
    constructor
    · intro h
      ext i
      have hi := congrFun h i
      omega
    · rintro rfl
      rfl
  simp only [he]

/-- The independently defined actual complex polytabloid trace of the literal
sort/delete-zero three-row partition equals the existing HSW alternant coefficient. -/
theorem ordinaryTrace_eq_frobChar {n : ℕ} (r : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1)
    (ρ : n.Partition) {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {τ : List ℕ}
    (hτ : (τ : Multiset ℕ) = ρ.parts) :
    LinearMap.trace ℂ _ ((spechtModuleℂ (tripleShape r hr)).ρ π) =
      (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ : ℂ) := by
  apply ordinaryTrace_eq_frobChar_of_selfGram r hr h01 h12 _ ρ hπ hτ
  simpa using signedContingencyGram_eq_delta r r hr h01 h12 h01 h12

/-- Class values of the unchanged actual Specht module, for use in finite sums. -/
theorem spechtCharValue_eq_frobChar {n : ℕ} (r : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1)
    (ρ : n.Partition) {τ : List ℕ} (hτ : (τ : Multiset ℕ) = ρ.parts) :
    spechtCharValue (tripleShape r hr) ρ =
      D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ := by
  obtain ⟨π, hπ⟩ := (partitionEquivConjClasses n ρ).exists_rep
  have h := ordinaryTrace_eq_frobChar r hr h01 h12 ρ hπ hτ
  change (spechtModuleℂ (tripleShape r hr)).character π = _ at h
  rw [character_spechtModuleℂ_intCast,
    ← spechtCharValue_eq_spechtChar _ _ hπ] at h
  exact_mod_cast h

private theorem evTypes_parts {n : ℕ} (λ : n.Partition) {τ : List ℕ}
    (hτ : τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList) :
    τ.sum = 2*n ∧ ∀ a ∈ τ, 0 < a := by
  have hgeneral (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
      ∀ τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes l,
        τ.sum = 2*l.sum ∧ ∀ a ∈ τ, 0 < a := by
    induction l with
    | nil => simp [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes]
    | cons a l ih =>
      intro τ ht
      have ha := hl a (by simp)
      have hrest := ih (fun b hb => hl b (by simp [hb]))
      simp only [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes,
        List.mem_append, List.mem_map] at ht
      rcases ht with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · obtain ⟨hs, hp⟩ := hrest v hv
        constructor
        · simp only [List.sum_cons]; omega
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro (by omega : 0 < 2*a) hp
      · obtain ⟨hs, hp⟩ := hrest v hv
        constructor
        · simp only [List.sum_cons]; omega
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro ha (And.intro ha hp)
  simpa [λ.parts_sum] using hgeneral λ.parts.toList (fun a ha => λ.parts_pos (by simpa using ha)) τ hτ

/-- The complete Ev list defines a partition of 2n, including every one-cycle. -/
def evPartition {n : ℕ} (λ : n.Partition)
    (τ : {τ // τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList}) :
    (2*n).Partition where
  parts := τ.val
  parts_pos := by
    intro a ha
    exact (evTypes_parts λ τ.property).2 a (by simpa using ha)
  parts_sum := by simpa using (evTypes_parts λ τ.property).1

private theorem rows_total {m : ℕ} {r : Fin 3 → ℕ}
    (hr : r ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 m) : ∑ i, r i = m :=
  Finset.Nat.mem_antidiagonalTuple.mp (mem_filter.mp hr).1

/-- The signed even-row sum of actual ordinary character values, with Ev multiplicity. -/
def signedEvSpechtSum {n : ℕ} (λ : n.Partition) : ℤ :=
  ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList).attach.map
    fun τ => ∑ r ∈ (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 (2*n)).attach,
      (-1 : ℤ)^τ.val.length *
        spechtCharValue (tripleShape r.val (rows_total r.property)) (evPartition λ τ)).sum

/-- The rectangle sum of actual ordinary character values; odd n is included. -/
def rectangleEvSpechtSum {n : ℕ} (λ : n.Partition) : ℤ :=
  ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList).attach.map
    fun τ => spechtCharValue (tripleShape ![n,n,0] (by simp [Fin.sum_univ_three]; omega))
      (evPartition λ τ)).sum

/-- Both original inner Ev sums consume the actual same-partition trace bridge. -/
theorem evSpechtSums_eq_coefficients {n : ℕ} (λ : n.Partition) :
    signedEvSpechtSum λ =
      ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList).map
        fun τ => ∑ r ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 (2*n),
          (-1 : ℤ)^τ.length *
            D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ).sum ∧
    rectangleEvSpechtSum λ =
      ((D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList).map
        fun τ => D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar ![n,n,0] τ).sum := by
  have hrow (τ : {τ // τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList})
      (r : {r // r ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.R3 (2*n)}) :
      spechtCharValue (tripleShape r.val (rows_total r.property)) (evPartition λ τ) =
        D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r.val τ.val :=
    spechtCharValue_eq_frobChar r.val (rows_total r.property)
      (mem_filter.mp r.property).2.1 (mem_filter.mp r.property).2.2.1 _ rfl
  have hrect (τ : {τ // τ ∈ D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.evTypes λ.parts.toList}) :
      spechtCharValue (tripleShape ![n,n,0] (by simp [Fin.sum_univ_three]; omega))
        (evPartition λ τ) =
        D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar ![n,n,0] τ.val :=
    spechtCharValue_eq_frobChar ![n,n,0] _ (by simp) (by simp) _ rfl
  constructor
  · simp only [signedEvSpechtSum, hrow]
    simp
  · simp only [rectangleEvSpechtSum, hrect]
    simp

/-- Actual ordinary characters satisfy the original per-partition Ev identity.
Its weighted consumers below evaluate both reciprocal-centralizer averages. -/
theorem ordinaryEv_identity {n : ℕ} (hn : 1 ≤ n) (λ : n.Partition) :
    signedEvSpechtSum λ = rectangleEvSpechtSum λ := by
  rw [(evSpechtSums_eq_coefficients λ).1, (evSpechtSums_eq_coefficients λ).2]
  exact D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.result n hn λ

/-- The two reciprocal-centralizer weighted averages of actual ordinary characters
are equal; the evaluated consumers below give their common value. -/
theorem ordinaryWeightedEv_identity (n : ℕ) (hn : 1 ≤ n) :
    (∑ λ : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition λ : ℚ)⁻¹ *
        (signedEvSpechtSum λ : ℚ)) =
    ∑ λ : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition λ : ℚ)⁻¹ *
        (rectangleEvSpechtSum λ : ℚ) := by
  apply sum_congr rfl
  intro λ _
  rw [ordinaryEv_identity hn λ]

open PowerSeries
open D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

/-- The rectangular ordinary average in the full original HSW conjecture.
The partition sum, Laurent series and coefficient maps below are local to this
consumer. ODE uniqueness and the rectangular coefficient identity are reused
from their existing owners, with no new coefficient-character definition. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem ordinaryWeightedRectangleEv_evaluated (n : ℕ) (hn : 1 ≤ n) :
    (∑ λ : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition λ : ℚ)⁻¹ *
        (rectangleEvSpechtSum λ : ℚ)) =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  classical
  let cycleWeight (k : ℕ) : LaurentPolynomial ℚ :=
    2 * (LaurentPolynomial.T (k : ℤ) + 1 + LaurentPolynomial.T (-(k : ℤ)))
  let term {d : ℕ} (λ : d.Partition) : LaurentPolynomial ℚ :=
    (zPartition λ : ℚ)⁻¹ • (λ.parts.map cycleWeight).prod
  let A (d : ℕ) : LaurentPolynomial ℚ := ∑ λ : d.Partition, term λ

  have partition_exponent_count {n : ℕ} (p : Nat.Partition n)
      (k : ℕ) (hk : 0 < k) : partitionExponent p (k - 1) = p.parts.count k := by
    have h := congrArg (Multiset.count k) (exponentParts_partitionExponent p)
    rw [exponentParts, show k = Nat.succ (k - 1) by omega,
      Multiset.count_map_eq_count' Nat.succ _ Nat.succ_injective,
      Finsupp.count_toMultiset] at h
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using h

  have z_partition_cons {n m k : ℕ}
      (p : Nat.Partition n) (q : Nat.Partition m)
      (hk : 0 < k) (hp : p.parts = k ::ₘ q.parts) :
      zPartition p = k * (q.parts.count k + 1) * zPartition q := by
    have he : partitionExponent p = partitionExponent q + Finsupp.single (k - 1) 1 := by
      simp only [partitionExponent, hp, Multiset.map_cons]
      rw [← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]
      exact add_comm _ _
    rw [zPartition, he, zExponent_add_single, partition_exponent_count q k hk]
    congr 2
    omega

  have cycle_term_cons {n m k : ℕ}
      (p : Nat.Partition n) (q : Nat.Partition m)
      (hk : 0 < k) (hp : p.parts = k ::ₘ q.parts) :
      ((k : ℚ) * (q.parts.count k + 1)) • term p = cycleWeight k * term q := by
    have hz : (zPartition q : ℚ) ≠ 0 := by
      exact_mod_cast (zExponent_pos (partitionExponent q)).ne'
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    have hc : (q.parts.count k + 1 : ℚ) ≠ 0 := by positivity
    have hs : ((k : ℚ) * (q.parts.count k + 1)) * (zPartition p : ℚ)⁻¹ =
        (zPartition q : ℚ)⁻¹ := by
      rw [z_partition_cons p q hk hp]
      push_cast
      field_simp
    simp only [term, hp, Multiset.map_cons, Multiset.prod_cons, smul_smul, hs]
    exact (mul_smul_comm _ _ _).symm

  have marked_cycle_sum (n k : ℕ)
      (hk : 0 < k) (hkn : k ≤ n) :
      (∑ p : Nat.Partition n, ((k : ℚ) * p.parts.count k) • term p) =
        cycleWeight k * A (n - k) := by
    let e := Nat.Partition.partitionWithPartEquiv hk hkn
    calc
      _ = ∑ p : {p : Nat.Partition n // k ∈ p.parts},
          ((k : ℚ) * p.val.parts.count k) • term p.val := by
        apply Finset.sum_congr_set {p : Nat.Partition n | k ∈ p.parts}
        · intro p hp
          rfl
        · intro p hp
          simp [Multiset.count_eq_zero_of_notMem hp]
      _ = ∑ q : Nat.Partition (n - k), cycleWeight k * term q := by
        apply Fintype.sum_equiv e
        intro p
        have hp : p.val.parts = k ::ₘ (e p).parts := by
          dsimp [e]
          rw [Nat.Partition.partitionWithPartEquiv_apply_parts]
          exact (Multiset.cons_erase p.property).symm
        have hc : p.val.parts.count k = (e p).parts.count k + 1 := by
          rw [hp]
          simp
        rw [hc, Nat.cast_add, Nat.cast_one]
        exact cycle_term_cons p.val (e p) hk hp
      _ = _ := by rw [A, Finset.mul_sum]

  have cycle_average_recursion (n : ℕ) :
      (n : ℚ) • A n =
        ∑ k ∈ Finset.Icc 1 n, cycleWeight k * A (n - k) := by
    have hdeg (p : Nat.Partition n) :
        (∑ k ∈ Finset.Icc 1 n, k * p.parts.count k) = n := by
      calc
        _ = ∑ k ∈ p.parts.toFinset, p.parts.count k * k := by
          symm
          calc
            _ = ∑ k ∈ p.parts.toFinset, k * p.parts.count k := by
              apply Finset.sum_congr rfl
              intro k _
              exact mul_comm _ _
            _ = _ := by
              apply Finset.sum_subset
              · intro k hk
                have hk' := Multiset.mem_toFinset.mp hk
                exact Finset.mem_Icc.mpr ⟨p.parts_pos hk', p.le_of_mem_parts hk'⟩
              · intro k hk hnot
                simp [Multiset.count_eq_zero_of_notMem (by simpa using hnot)]
        _ = n := by
          simpa only [nsmul_eq_mul, id_eq, Multiset.map_id, Multiset.map_id', Nat.cast_id,
            p.parts_sum] using
            (Finset.sum_multiset_map_count p.parts id).symm
    calc
      _ = ∑ p : Nat.Partition n, ∑ k ∈ Finset.Icc 1 n,
          ((k : ℚ) * p.parts.count k) • term p := by
        rw [A, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.sum_smul]
        congr 1
        exact_mod_cast (hdeg p).symm
      _ = ∑ k ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n,
          ((k : ℚ) * p.parts.count k) • term p := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hk, hkn⟩ := Finset.mem_Icc.mp hk
        exact marked_cycle_sum n k hk hkn

  have cycle_average_zero : A 0 = 1 := by
    simp [A, term, zPartition, partitionExponent, zExponent]

  have cycle_average_derivative :
      PowerSeries.derivative (PowerSeries.mk (A)) =
        (PowerSeries.mk fun k => cycleWeight (k + 1)) * PowerSeries.mk (A) := by
    ext n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
    rw [show A (n + 1) * (n + 1 : LaurentPolynomial ℚ) =
        ((n + 1 : ℕ) : ℚ) • A (n + 1) by simp [Algebra.smul_def, mul_comm]]
    rw [cycle_average_recursion]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i hi
    congr 2 <;> omega

  have square_series :
      (PowerSeries.mk fun n => (n + 1 : ℚ) ^ 2) =
        2 * (invOneSubPow ℚ 3).val - (invOneSubPow ℚ 2).val := by
    ext n
    simp only [invOneSubPow, coeff_mk, map_sub, mul_comm (2 : PowerSeries ℚ),
      coeff_mul_ofNat]
    simp only [Nat.cast_choose_two, Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat]
    ring

  have consecutive_series :
      (PowerSeries.mk fun n => (n + 1 : ℚ) * (n + 2 : ℚ)) =
        2 * (invOneSubPow ℚ 3).val := by
    ext n
    simp only [invOneSubPow, coeff_mk, mul_comm (2 : PowerSeries ℚ), coeff_mul_ofNat]
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
    ring

  have constant_term_cancellation :
      (invOneSubPow ℚ 2).val *
        ((expand 2 (by decide) (PowerSeries.mk fun n => (n + 1 : ℚ) ^ 2)) -
          X * (expand 2 (by decide)
            (PowerSeries.mk fun n => (n + 1 : ℚ) * (n + 2 : ℚ)))) =
        expand 2 (by decide) (invOneSubPow ℚ 3).val := by
    have hrel : (1 - X : PowerSeries ℚ) * (invOneSubPow ℚ 3).val =
        (invOneSubPow ℚ 2).val := by
      simpa using one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ 2 1
    have he := congrArg (expand 2 (by decide)) hrel
    simp only [map_mul, map_sub, map_one, expand_X] at he
    rw [square_series, consecutive_series, map_sub, map_mul, map_ofNat]
    calc
      _ = (invOneSubPow ℚ 2).val *
          ((1 - X) ^ 2 * expand 2 (by decide) (invOneSubPow ℚ 3).val) := by
        rw [← he]
        ring
      _ = _ := by
        rw [← mul_assoc, show (invOneSubPow ℚ 2).val * (1 - X) ^ 2 = 1 from (invOneSubPow ℚ
          2).val_inv, one_mul]

  have coefficient_even_cube (n : ℕ) :
      (expand 2 (by decide) (invOneSubPow ℚ 3).val).coeff n =
        if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
    rw [coeff_expand]
    simp only [invOneSubPow, coeff_mk, Nat.add_comm 2, even_iff_two_dvd]

  have geometric_square (r : LaurentPolynomial ℚ) : (rescale r (invOneSubPow _ 1).val) ^ 2 = (rescale r
    (invOneSubPow _ 2).val) := by
    rw [← map_pow]
    congr 1
    simpa [pow_two, invOneSubPow_add, Units.val_mul] using
      (congrArg Units.val (invOneSubPow_add (LaurentPolynomial ℚ) 1 1)).symm

  have coeff_geometric (r : LaurentPolynomial ℚ) (n : ℕ) : coeff n ((rescale r (invOneSubPow _ 1).val)) =
    r ^ n := by
    simp [coeff_rescale, invOneSubPow]

  have coeff_geometricSquare (r : LaurentPolynomial ℚ) (n : ℕ) :
      coeff n ((rescale r (invOneSubPow _ 2).val)) = r ^ n * (n + 1) := by
    simp [coeff_rescale, invOneSubPow, Nat.add_comm]

  have geometric_derivative (r : LaurentPolynomial ℚ) :
      derivative ((rescale r (invOneSubPow _ 1).val)) = C r * (rescale r (invOneSubPow _ 2).val)
        := by
    ext n
    simp only [coeff_derivative, coeff_geometric, coeff_C_mul, coeff_geometricSquare,
      pow_succ]
    ring

  have geometricSquare_derivative (r : LaurentPolynomial ℚ) :
      derivative ((rescale r (invOneSubPow _ 2).val)) =
        (rescale r (invOneSubPow _ 2).val) * (C (2 * r) * (rescale r (invOneSubPow _ 1).val)) := by
    rw [← geometric_square, derivative_pow, geometric_derivative, ← geometric_square]
    norm_num
    simp only [map_ofNat]
    ring

  have three_square_derivative (r s t : LaurentPolynomial ℚ) :
      derivative ((rescale r (invOneSubPow _ 2).val) * (rescale s (invOneSubPow _ 2).val) *
        (rescale t (invOneSubPow _ 2).val)) =
        ((rescale r (invOneSubPow _ 2).val) * (rescale s (invOneSubPow _ 2).val) * (rescale t
          (invOneSubPow _ 2).val)) *
          PowerSeries.mk (fun k => 2 * (r ^ (k + 1) + s ^ (k + 1) + t ^ (k + 1))) := by
    have he : PowerSeries.mk (fun k => 2 * (r ^ (k + 1) + s ^ (k + 1) + t ^ (k + 1))) =
        C (2 * r) * (rescale r (invOneSubPow _ 1).val) + C (2 * s) * (rescale s (invOneSubPow _
          1).val) + C (2 * t) * (rescale t (invOneSubPow _ 1).val) := by
      ext n
      simp only [coeff_mk, map_add, coeff_C_mul, coeff_geometric, pow_succ]
      ring
    rw [he, derivative.leibniz, derivative.leibniz]
    simp only [smul_eq_mul, geometricSquare_derivative]
    ring

  let constantTermSeries (f : PowerSeries (LaurentPolynomial ℚ)) : PowerSeries ℚ :=
    PowerSeries.mk fun n => ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv
      ℚ).toLinearMap) (PowerSeries.coeff n f)

  have constantTerm_C_mul (a : ℚ) (f : (LaurentPolynomial ℚ)) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
        (LaurentPolynomial.C a * f) = a * ((Finsupp.lapply (R := ℚ) 0).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) f := by
    exact AddMonoidAlgebra.coeff_single_zero_mul f a 0

  have constantTermSeries_sub (f g : PowerSeries (LaurentPolynomial ℚ)) :
      constantTermSeries (f - g) = constantTermSeries f - constantTermSeries g := by
    ext n
    simp [constantTermSeries]

  have constantTermSeries_map_mul (f : PowerSeries ℚ) (g : PowerSeries
    (LaurentPolynomial ℚ)) :
      constantTermSeries ((PowerSeries.map LaurentPolynomial.C f) * g) =
        f * constantTermSeries g := by
    ext n
    simp only [constantTermSeries, coeff_mk, coeff_mul, coeff_map, map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact constantTerm_C_mul _ _

  have constantTerm_shift (f : (LaurentPolynomial ℚ)) (k : ℤ) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
        (LaurentPolynomial.T k * f) = f.coeff (-k) := by
    change (LaurentPolynomial.T k * f).coeff 0 = _
    simpa only [zero_sub, add_zero, one_mul, LaurentPolynomial.T] using
      AddMonoidAlgebra.coeff_single_mul_apply f (1 : ℚ) k (0 : ℤ)

  have laurent_geometric_pair_term (i j : ℕ) :
      (LaurentPolynomial.T (1 : ℤ) ^ i * (i + 1 : (LaurentPolynomial ℚ))) *
        (LaurentPolynomial.T (-1 : ℤ) ^ j * (j + 1 : (LaurentPolynomial ℚ))) =
        LaurentPolynomial.C ((i + 1 : ℚ) * (j + 1 : ℚ)) *
          LaurentPolynomial.T ((i : ℤ) - j) := by
    simp only [LaurentPolynomial.T_pow, mul_one, mul_neg_one]
    rw [map_mul]
    have hi : (i + 1 : (LaurentPolynomial ℚ)) = LaurentPolynomial.C (i + 1 : ℚ) := by simp
    have hj : (j + 1 : (LaurentPolynomial ℚ)) = LaurentPolynomial.C (j + 1 : ℚ) := by simp
    rw [hi, hj, sub_eq_add_neg, LaurentPolynomial.T_add]
    ring

  have pair_coefficient (n : ℕ) (e : ℤ) :
      (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
          2).val))).coeff e =
        ∑ i ∈ Finset.range (n + 1),
          if (i : ℤ) - (n - i : ℕ) = e then
            (i + 1 : ℚ) * (((n - i : ℕ) : ℚ) + 1) else 0 := by
    let c : (LaurentPolynomial ℚ) →ₗ[ℚ] ℚ := {
      toFun := fun p => p.coeff e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    change c _ = _
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coeff_geometricSquare, coeff_geometricSquare, laurent_geometric_pair_term]
    change (LaurentPolynomial.C _ * LaurentPolynomial.T _).coeff e = _
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

  have pair_coefficient_zero (n : ℕ) :
      (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
          2).val))).coeff 0 =
        if Even n then (((n / 2 : ℕ) : ℚ) + 1) ^ 2 else 0 := by
    rw [pair_coefficient]
    split_ifs with hn
    · have he : n % 2 = 0 := Nat.even_iff.mp hn
      rw [Finset.sum_eq_single (n / 2)]
      · have hnat : n - n / 2 = n / 2 := by omega
        simp [hnat, pow_two]
      · intro b hb hne
        have hb' := Finset.mem_range.mp hb
        have hne' : (b : ℤ) - (n - b : ℕ) ≠ 0 := by omega
        simp [hne']
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    · apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have he : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hn
      have hne : (i : ℤ) - (n - i : ℕ) ≠ 0 := by omega
      simp [hne]

  have pair_coefficient_one (n : ℕ) :
      (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
          2).val))).coeff 1 =
        if Even n then 0 else (((n / 2 : ℕ) : ℚ) + 1) * (((n / 2 : ℕ) : ℚ) + 2) := by
    rw [pair_coefficient]
    split_ifs with hn
    · apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have he : n % 2 = 0 := Nat.even_iff.mp hn
      have hne : (i : ℤ) - (n - i : ℕ) ≠ 1 := by omega
      simp [hne]
    · have he : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hn
      rw [Finset.sum_eq_single (n / 2 + 1)]
      · have hnat : n - (n / 2 + 1) = n / 2 := by omega
        have heq : ((n / 2 + 1 : ℕ) : ℤ) - (n - (n / 2 + 1) : ℕ) = 1 := by omega
        rw [ite_eq_left heq, hnat]
        push_cast
        ring
      · intro b hb hne
        have hb' := Finset.mem_range.mp hb
        have hne' : (b : ℤ) - (n - b : ℕ) ≠ 1 := by omega
        simp [hne']
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

  have constantTerm_pair :
      constantTermSeries ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ))
        (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val)) =
        expand 2 (by decide) (mk fun j => (j + 1 : ℚ) ^ 2) := by
    ext n
    simp only [constantTermSeries, coeff_mk]
    change (coeff n ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow
      _ 2).val) *
      (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
        2).val))).coeff 0 = _
    simpa only [coeff_expand, coeff_mk, ← even_iff_two_dvd] using pair_coefficient_zero n

  have constantTerm_shift_pair :
      constantTermSeries (C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) *
        ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
          (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val))) =
        X * expand 2 (by decide) (mk fun j => (j + 1 : ℚ) * (j + 2 : ℚ)) := by
    ext n
    simp only [constantTermSeries, coeff_mk, coeff_C_mul, constantTerm_shift, neg_neg]
    rw [pair_coefficient_one]
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul, coeff_expand, coeff_mk]
      by_cases he : Even n
      · have ho : ¬ Even (n + 1) := by rw [Nat.even_iff] at he ⊢; omega
        have hdiv : (n + 1) / 2 = n / 2 := by have := Nat.even_iff.mp he; omega
        simp [he, ho, hdiv, ← even_iff_two_dvd]
      · have ho : Even (n + 1) := Nat.even_add_one.mpr he
        simp [he, ho, ← even_iff_two_dvd]

  -- Both differential equations use the same literal positive-cycle driver.
  have hseries : PowerSeries.mk A =
      (rescale (1 : LaurentPolynomial ℚ) (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℚ)
          (invOneSubPow _ 2).val) *
        (rescale (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℚ)
          (invOneSubPow _ 2).val) := by
    letI : HasUniqueDiv (LaurentPolynomial ℚ) := .of_module_rat _
    apply solution_unique
      (PowerSeries.mk A) _ (PowerSeries.mk fun k => cycleWeight (k + 1))
    · simpa only [mul_comm] using cycle_average_derivative
    · have h := three_square_derivative (1 : LaurentPolynomial ℚ)
        (LaurentPolynomial.T (1 : ℤ)) (LaurentPolynomial.T (-1 : ℤ))
      simpa only [cycleWeight, one_pow, LaurentPolynomial.T_pow, mul_one, mul_neg_one,
        add_comm, add_left_comm, Nat.cast_add, Nat.cast_one] using h
    · simp only [coeff_mk, cycle_average_zero, map_mul]
      simp [← coeff_zero_eq_constantCoeff, invOneSubPow]

  have geometricSquare_one :
      (rescale (1 : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) =
        PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val := by
    ext n
    simp [invOneSubPow, Nat.add_comm]

  have weighted_constant_term_series :
      constantTermSeries ((1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ))) *
        PowerSeries.mk A) =
        expand 2 (by decide) (invOneSubPow ℚ 3).val := by
    rw [hseries, geometricSquare_one]
    have he :
        (1 - C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ))) *
          (PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val *
            (rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
            (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
              2).val)) =
        PowerSeries.map LaurentPolynomial.C (invOneSubPow ℚ 2).val *
          (((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _ 2).val) *
            (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
              2).val)) -
            C (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) *
              ((rescale (LaurentPolynomial.T (1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
                2).val) *
                (rescale (LaurentPolynomial.T (-1 : ℤ) : (LaurentPolynomial ℚ)) (invOneSubPow _
                  2).val))) := by ring
    rw [he, constantTermSeries_map_mul, constantTermSeries_sub,
      constantTerm_pair, constantTerm_shift_pair]
    exact constant_term_cancellation

  have laurent_coefficient_nat (P : Polynomial ℚ) (n : ℕ) :
      P.toLaurent.coeff (n : ℤ) = P.coeff n := by
    exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => Int.natCast_inj.mp h)
      P.toFinsupp.coeff n

  have constantTerm_polynomial_shift (P : Polynomial ℚ) (n : ℕ) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
        (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))) = P.coeff n := by
    change (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))).coeff 0 = _
    simpa only [LaurentPolynomial.T, zero_sub, neg_neg, zero_add, mul_one,
      laurent_coefficient_nat] using
      AddMonoidAlgebra.coeff_mul_single_apply P.toLaurent (1 : ℚ) (-(n : ℤ)) (0 : ℤ)

  have constantTerm_polynomial_difference (P : Polynomial ℚ) (n : ℕ) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ((1 -
        LaurentPolynomial.T (-1 : ℤ)) *
        (P.toLaurent * LaurentPolynomial.T (-(n : ℤ)))) =
        P.coeff n - P.coeff (n + 1) := by
    rw [sub_mul, one_mul, map_sub, constantTerm_polynomial_shift]
    have he : LaurentPolynomial.T (-1 : ℤ) *
        (P.toLaurent * LaurentPolynomial.T (-(n : ℤ))) =
        P.toLaurent * LaurentPolynomial.T (-((n + 1 : ℕ) : ℤ)) := by
      rw [mul_left_comm, ← LaurentPolynomial.T_add]
      congr 2
      push_cast
      ring
    rw [he, constantTerm_polynomial_shift]

  have laurent_trinomial (a : ℕ) :
      Polynomial.toLaurent (Polynomial.X ^ (2 * a) + Polynomial.X ^ a + 1 : Polynomial ℚ) *
        LaurentPolynomial.T (-(a : ℤ)) =
        LaurentPolynomial.T (a : ℤ) + 1 + LaurentPolynomial.T (-(a : ℤ)) := by
    simp only [map_add, Polynomial.toLaurent_X_pow, map_one, add_mul, one_mul,
      ← LaurentPolynomial.T_add]
    have h2 : (2 : ℤ) * a + -(a : ℤ) = (a : ℤ) := by omega
    simp only [Nat.cast_mul, Nat.cast_ofNat, h2, add_neg_cancel, LaurentPolynomial.T_zero]

  have laurent_product (l : List ℕ) :
      (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) + 1 +
        LaurentPolynomial.T (-(a : ℤ)) : List (LaurentPolynomial ℚ)).prod =
        ((triProd l).map (Int.castRingHom ℚ)).toLaurent *
          LaurentPolynomial.T (-((l.sum : ℕ) : ℤ)) := by
    induction l with
    | nil => simp [triProd]
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, triProd, Polynomial.map_mul, map_mul,
        Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
        Nat.cast_add, neg_add] at ih ⊢
      rw [← laurent_trinomial a, ih, LaurentPolynomial.T_add]
      ring

  have input_product (l : List ℕ) :
      (l.map cycleWeight).prod =
        LaurentPolynomial.C ((2 : ℚ) ^ l.length) *
          (((triProd l).map (Int.castRingHom ℚ)).toLaurent *
            LaurentPolynomial.T (-((l.sum : ℕ) : ℤ))) := by
    have he : (l.map cycleWeight).prod =
        (2 : (LaurentPolynomial ℚ)) ^ l.length * (l.map fun a : ℕ => LaurentPolynomial.T (a : ℤ) +
          1 +
          LaurentPolynomial.T (-(a : ℤ))).prod := by
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.prod_cons, List.length_cons, cycleWeight, ih, pow_succ]
        ring
    rw [he, laurent_product]
    congr 1
    exact (map_pow LaurentPolynomial.C (2 : ℚ) l.length).trans (by simp only [map_ofNat]) |>.symm

  have character_constantTerm (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) :
      ((Finsupp.lapply (R := ℚ) 0).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) ((1 -
        LaurentPolynomial.T (-1 : ℤ)) *
        (p.parts.map cycleWeight).prod) =
        (rectangleEvSpechtSum p : ℚ) := by
    have he := input_product p.parts.toList
    have hsum : p.parts.toList.sum = n := by simpa using p.parts_sum
    rw [Multiset.prod_map_toList, hsum, Multiset.length_toList] at he
    rw [(evSpechtSums_eq_coefficients p).2]
    have hpos : ∀ b ∈ p.parts.toList, 0 < b := by
      intro b hb
      exact p.parts_pos (by simpa using hb)
    have hrect := right_coefficient p.parts.toList (by omega : 1 ≤ p.parts.toList.sum) hpos
    rw [← ev_right] at hrect
    rw [he, mul_left_comm, constantTerm_C_mul, constantTerm_polynomial_difference,
      show ((evTypes p.parts.toList).map fun τ => frobChar ![n,n,0] τ).sum =
        (2 : ℤ)^p.parts.card *
          ((triProd p.parts.toList).coeff n - (triProd p.parts.toList).coeff (n+1)) by
        simpa only [hsum, Multiset.length_toList] using hrect]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_sub, Polynomial.coeff_map,
      Int.coe_castRingHom]

  have haverage :
      (∑ λ : n.Partition, (zPartition λ : ℚ)⁻¹ * (rectangleEvSpechtSum λ : ℚ)) =
      ((Finsupp.lapply (R := ℚ) 0).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)
          ((1 - LaurentPolynomial.T (-1 : ℤ)) * A n) := by
    simp only [A, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro λ _
    rw [term, mul_smul_comm, map_smul, character_constantTerm n hn λ]
    rfl
  rw [haverage]
  have he := congrArg (coeff n) weighted_constant_term_series
  simp only [constantTermSeries, coeff_mk] at he
  have hc : (1 - C (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℚ) :
      PowerSeries (LaurentPolynomial ℚ)) =
      C (1 - LaurentPolynomial.T (-1 : ℤ)) := by simp
  rw [hc, coeff_C_mul, coeff_mk, coefficient_even_cube] at he
  exact he

/-- The signed ordinary average has the same evaluated value, with all even
three-row shapes and all occurrence-wise Ev outcomes retained. -/
theorem ordinaryWeightedSignedEv_evaluated (n : ℕ) (hn : 1 ≤ n) :
    (∑ λ : n.Partition,
      (D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2.zPartition λ : ℚ)⁻¹ *
        (signedEvSpechtSum λ : ℚ)) =
      if Even n then (((n / 2 + 2).choose 2 : ℕ) : ℚ) else 0 := by
  rw [ordinaryWeightedEv_identity n hn]
  exact ordinaryWeightedRectangleEv_evaluated n hn

end TauCeti.ThreeRowGram
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
