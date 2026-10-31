/- GID: D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchyKernel
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtThreeRowCauchyKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite three-variable Cauchy kernel gives the signed contingency Gram delta. -/

/-
Classical Cauchy identity, with the nine labelled edge coefficients counted by finite contingency tables.
The ordinary-character consumer uses the signed Gram delta. No standalone firstfreeze is proposed.
Unfinished public-declaration audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtThreeRowMixed
import Mathlib.RingTheory.MvPowerSeries.Basic

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti.ThreeRowGram
open _root_.Equiv _root_.Equiv.Perm Finset

private def deltaProduct {R : Type*} [CommRing R] (x : Fin 3 → R) : R :=
  (x 0 - x 1) * (x 0 - x 2) * (x 1 - x 2)

/-- The cleared three-by-three Cauchy numerator, evaluated over any commutative ring. -/
private theorem cauchy_numerator {R : Type*} [CommRing R] (x y : Fin 3 → R) :
    Matrix.det (Matrix.of fun i : Fin 3 =>
      ![(1-x i*y 1)*(1-x i*y 2), (1-x i*y 0)*(1-x i*y 2),
        (1-x i*y 0)*(1-x i*y 1)]) = deltaProduct x * deltaProduct y := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, deltaProduct]
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
private def edgeSeries (i j : Fin 3) : Series := by
  classical
  exact fun d => if ∃ k : ℕ, d = edgeWeight i j k then 1 else 0

private theorem edgeSeries_inverse (i j : Fin 3) :
    (1 - MvPowerSeries.monomial (edgeWeight i j 1) (1 : ℤ)) * edgeSeries i j = 1 := by
  classical
  apply MvPowerSeries.ext
  intro d
  rw [sub_mul, one_mul, map_sub, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_one]
  simp only [one_mul, MvPowerSeries.coeff_apply]
  by_cases he : ∃ k : ℕ, d = edgeWeight i j k
  · obtain ⟨k, rfl⟩ := he
    have hsub : edgeWeight i j k - edgeWeight i j 1 = edgeWeight i j (k-1) := by
      ext t
      rcases t with t | t <;> by_cases ht : t = i <;> by_cases ht' : t = j <;>
        simp [edgeWeight, Finsupp.single_apply, ht, ht']
    by_cases hk : k = 0
    · subst k
      simp [edgeSeries, edgeWeight]
      exact ⟨0, by simp⟩
    · have hle : edgeWeight i j 1 ≤ edgeWeight i j k := by
        intro t
        rcases t with t | t
        · by_cases ht : i = t <;> simp [edgeWeight, Finsupp.single_apply, ht] <;> omega
        · by_cases ht : j = t <;> simp [edgeWeight, Finsupp.single_apply, ht] <;> omega
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
      simpa [hk, edgeWeight, Finsupp.single_apply, d, doubleWeight] using h
    have hy (i : Fin 3) : k i = v (σ i) := by
      have h := congrArg (fun e : Variables →₀ ℕ => e (Sum.inr (σ i))) hs
      simpa [hk, edgeWeight, Finsupp.single_apply, σ.injective.eq_iff, d, doubleWeight] using h
    refine ⟨?_, fun i => (hx i).symm.trans (hy i)⟩
    ext i t
    simp only [L, Finsupp.coe_equivFunOnFinite_symm, hk, hx]
  by_cases hm : ∀ i, u i = v (σ i)
  · rw [if_pos hm]
    have hL : L ∈ finsuppAntidiag univ d := by
      rw [mem_finsuppAntidiag]
      refine ⟨?_, subset_univ _⟩
      ext t
      rcases t with i | j
      · simp [L, edgeWeight, Finsupp.single_apply, d, doubleWeight]
      · rw [← σ.apply_symm_apply j]
        simp [L, edgeWeight, Finsupp.single_apply, d, doubleWeight, hm]
        simpa using (Equiv.sum_comp σ (fun x => if x = j then v x else 0))
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
    all_goals first | omega | (apply Equiv.ext; intro i; fin_cases i <;> simp_all)
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
      simpa [recover l hl, edgeWeight, Finsupp.single_apply, Fintype.sum_prod_type, d, doubleWeight] using h
    have hcol (j : Fin 3) : ∑ i, toTable l (i,j) = b j := by
      have h := congrArg (fun e : Variables →₀ ℕ => e (Sum.inr j)) hs
      simpa [recover l hl, edgeWeight, Finsupp.single_apply, Fintype.sum_prod_type, d, doubleWeight] using h
    apply mem_filter.mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_piAntidiag]
      refine ⟨?_, fun _ _ => mem_univ _⟩
      calc
        (∑ e : Fin 3 × Fin 3, toTable l e) =
            ∑ i : Fin 3, ∑ j : Fin 3, toTable l (i,j) := Fintype.sum_prod_type _
        _ = ∑ i : Fin 3, a i := sum_congr rfl (fun i _ => hrow i)
        _ = n := ha
    · intro i
      exact congrArg (fun k : ℕ => (k : ℤ)) (hrow i)
    · intro j
      exact congrArg (fun k : ℕ => (k : ℤ)) (hcol j)
  have from_mem (A : Fin 3 × Fin 3 → ℕ) (hA : A ∈ T) : toDecomp A ∈ S := by
    obtain ⟨-, hrow, hcol⟩ := mem_filter.mp hA
    apply mem_filter.mpr
    refine ⟨?_, fun e => ⟨A e, rfl⟩⟩
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    ext t
    rcases t with i | j
    · have h : ∑ j, A (i,j) = a i := Int.natCast_inj.mp (hrow i)
      simpa [toDecomp, edgeWeight, Finsupp.single_apply, Fintype.sum_prod_type, d, doubleWeight] using h
    · have h : ∑ i, A (i,j) = b j := Int.natCast_inj.mp (hcol j)
      simpa [toDecomp, edgeWeight, Finsupp.single_apply, Fintype.sum_prod_type, d, doubleWeight] using h
  have hcard : S.card = T.card := by
    apply card_bij' (fun l _ => toTable l) (fun A _ => toDecomp A) to_mem from_mem
    · intro l hl
      ext e t
      simpa only [toDecomp, Finsupp.coe_equivFunOnFinite_symm] using congrArg (fun w : Variables →₀ ℕ => w t) (recover l hl e).symm
    · intro A _
      funext e
      simp [toTable, toDecomp, edgeWeight]
  rw [cauchyKernel, ← Fintype.prod_prod_type', MvPowerSeries.coeff_prod]
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
      Matrix.det (Matrix.of fun i j : Fin 3 => edgeSeries i j) := by
    apply cauchy_inverse_identity
    intro i j
    have hm : (MvPowerSeries.X (Sum.inl i) : Series) * MvPowerSeries.X (Sum.inr j) =
        MvPowerSeries.monomial (edgeWeight i j 1) (1 : ℤ) := by
      simp [MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, edgeWeight]
    rw [hm]
    exact edgeSeries_inverse i j
  rw [hid, Matrix.det_apply, map_sum]
  simp only [Matrix.of_apply]
  have hterm (σ : Perm (Fin 3)) :
      MvPowerSeries.coeff (doubleWeight u v)
        (sign σ • ∏ i, edgeSeries (σ i) i) =
        if σ = 1 ∧ u = v then (1 : ℤ) else 0 := by
    have hp : (∏ i, edgeSeries (σ i) i) = ∏ i, edgeSeries i (σ⁻¹ i) := by
      simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ (fun i => edgeSeries i (σ⁻¹ i)))
    simp only [Units.smul_def]
    rw [hp, map_smul, matching_product_coefficient]
    by_cases hm : ∀ i, u i = v (σ⁻¹ i)
    · obtain ⟨hs, he⟩ := strict_matching_unique u v hu01 hu12 hv01 hv12 σ⁻¹ hm
      have hs' : σ = 1 := by simpa using congrArg Inv.inv hs
      simp [hm, hs', he]
    · have hn : ¬ (σ = 1 ∧ u = v) := by rintro ⟨rfl, rfl⟩; exact hm (by simp)
      simp only [Equiv.Perm.inv_def] at hm
      simp [hm, hn]
  simp_rw [hterm]
  by_cases he : u = v <;> simp [he]

private theorem side_vandermonde (f : Fin 3 → Variables) :
    deltaProduct (fun i => (MvPowerSeries.X (f i) : Series)) =
      ∑ σ : Perm (Fin 3), (sign σ : ℤ) •
        MvPowerSeries.monomial (Finsupp.mapDomain f (permutedStaircase σ)) (1 : ℤ) := by
  let φ : MvPolynomial (Fin 3) ℤ →+* Series :=
    MvPolynomial.coeToMvPowerSeries.ringHom.comp (MvPolynomial.rename f).toRingHom
  have hX (i : Fin 3) : φ (MvPolynomial.X i) = MvPowerSeries.X (f i) := by
    simp [φ]
  have hm (e : Fin 3 →₀ ℕ) (c : ℤ) : φ (MvPolynomial.monomial e c) =
      MvPowerSeries.monomial (Finsupp.mapDomain f e) c := by
    simp [φ, MvPolynomial.rename_monomial]
  have h := congrArg φ vandermonde_eq_signed_monomials
  simpa only [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3,
    map_mul, map_sub, map_sum, map_zsmul, hX, hm, deltaProduct] using h

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
  simp only [sum_mul, smul_mul_assoc, map_sum, map_zsmul, coeff_shifted_kernel r q hr,
    smul_eq_mul, signedContingencyGram]

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

end TauCeti.ThreeRowGram
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
