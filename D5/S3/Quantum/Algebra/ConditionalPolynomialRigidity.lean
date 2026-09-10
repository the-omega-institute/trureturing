/- GID: D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ConditionalPolynomialRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional polynomial rigidity for subspaces of dimension at least two. -/

import D5.S3.Quantum.Algebra.PolynomialTangentDescent
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Data.Nat.Find

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity

open MvPolynomial

variable {K sigma : Type*} [Field K] [CharZero K]

private theorem eq_constant_of_partials_zero (p : MvPolynomial sigma K)
    (h : ∀ i, pderiv i p = 0) : p = C (constantCoeff p) := by
  apply MvPolynomial.coe_injective sigma K
  apply MvPowerSeries.pderiv.ext
  · intro i
    simp [MvPowerSeries.pderiv_coe, h i]
  · simp only [MvPolynomial.coe_C, MvPowerSeries.constantCoeff_C]
    rfl

omit [CharZero K] in
private theorem partials_commute (p : MvPolynomial sigma K) (i j : sigma) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  have h : ⁅pderiv (R := K) i, pderiv (R := K) j⁆ = (0 : Derivation K (MvPolynomial sigma K)
      (MvPolynomial sigma K)) := by
    apply MvPolynomial.derivation_ext
    intro k
    simp [Derivation.commutator_apply, pderiv_X, Pi.single_apply, apply_ite]
  have he := DFunLike.congr_fun h p
  simpa [Derivation.commutator_apply, sub_eq_zero] using he

omit [CharZero K] in
private theorem totalDegree_pderiv_lt (p : MvPolynomial sigma K) (i : sigma)
    (hd : pderiv i p ≠ 0) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hp : 0 < p.totalDegree := by
    by_contra hn
    have he : p.totalDegree = 0 := Nat.eq_zero_of_not_pos hn
    exact hd (by rw [totalDegree_eq_zero_iff_eq_C.mp he, pderiv_C])
  rw [totalDegree]
  apply (Finset.sup_lt_iff hp).2
  intro d hdmem
  have hcoeff : coeff (d + Finsupp.single i 1) p ≠ 0 := by
    have h := mem_support_iff.mp hdmem
    rw [coeff_pderiv] at h
    exact (mul_ne_zero_iff.mp h).1
  have hdeg := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hsum : (d + Finsupp.single i 1).sum (fun _ e => e) =
      d.sum (fun _ e => e) + 1 := by
    simp [Finsupp.sum_add_index']
  rw [hsum] at hdeg
  omega

omit [CharZero K] in
private theorem exists_minimum_degree (P : MvPolynomial sigma K → Prop)
    (hP : ∃ p, P p) :
    ∃ p, P p ∧ ∀ r, P r → p.totalDegree ≤ r.totalDegree := by
  classical
  have hex : ∃ n, ∃ p, P p ∧ p.totalDegree = n := by
    obtain ⟨p, hp⟩ := hP
    exact ⟨p.totalDegree, p, hp, rfl⟩
  obtain ⟨p, hp, hdeg⟩ := Nat.find_spec hex
  refine ⟨p, hp, ?_⟩
  intro r hr
  rw [hdeg]
  exact Nat.find_min' hex ⟨r, hr, rfl⟩

omit [CharZero K] in
private theorem exists_nonzero_evaluation_kernel
    (L : Submodule K (MvPolynomial sigma K)) [FiniteDimensional K L]
    (hdim : 2 ≤ Module.finrank K L) :
    ∃ q : MvPolynomial sigma K, q ∈ L ∧ q ≠ 0 ∧ constantCoeff q = 0 := by
  let e : L →ₗ[K] K := (MvPolynomial.aeval (0 : sigma → K)).toLinearMap.domRestrict L
  have hk : LinearMap.ker e ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simpa only [Module.finrank_self] using (show 1 < Module.finrank K L by omega))
  obtain ⟨q, hq, hqne⟩ := (LinearMap.ker e).ne_bot_iff.mp hk
  refine ⟨q, q.property, ?_, ?_⟩
  · intro hz
    exact hqne (Subtype.ext hz)
  · have he := LinearMap.mem_ker.mp hq
    simpa [e, MvPolynomial.aeval_zero] using he

private theorem minimum_has_nonzero_constantCoeff
    (L : Submodule K (MvPolynomial sigma K))
    (hclosed : ∀ p ∈ L, constantCoeff p = 0 → ∀ i, pderiv i p ∈ L)
    (p : MvPolynomial sigma K) (hp : p ∈ L) (hpne : p ≠ 0)
    (hmin : ∀ r ∈ L, r ≠ 0 → p.totalDegree ≤ r.totalDegree) :
    constantCoeff p ≠ 0 := by
  intro hz
  have hD : ∀ i, pderiv i p = 0 := by
    intro i
    by_contra hi
    exact (not_le_of_gt (totalDegree_pderiv_lt p i hi))
      (hmin _ (hclosed p hp hz i) hi)
  have he := eq_constant_of_partials_zero p hD
  exact hpne (by simpa [hz] using he)

omit [CharZero K] in
private theorem small_degree_dependence
    (L : Submodule K (MvPolynomial sigma K))
    (p q : MvPolynomial sigma K) (hp : p ∈ L)
    (hp0 : constantCoeff p ≠ 0) (hpq : p.totalDegree < q.totalDegree)
    (hqmin : ∀ s ∈ L, s ≠ 0 → constantCoeff s = 0 → q.totalDegree ≤ s.totalDegree)
    (r : MvPolynomial sigma K) (hr : r ∈ L) (hrdeg : r.totalDegree < q.totalDegree) :
    r = (constantCoeff r / constantCoeff p) • p := by
  -- Normalize evaluation before applying minimality in its kernel.
  let s := r - (constantCoeff r / constantCoeff p) • p
  have hs : s ∈ L := L.sub_mem hr (L.smul_mem _ hp)
  have hs0 : constantCoeff s = 0 := by
    dsimp [s]
    simp [constantCoeff_smul, div_mul_cancel₀ _ hp0]
  have hsdeg : s.totalDegree < q.totalDegree := by
    exact (totalDegree_sub _ _).trans_lt
      (max_lt hrdeg ((totalDegree_smul_le _ _).trans_lt hpq))
  have hsz : s = 0 := by
    by_contra hn
    exact (not_le_of_gt hsdeg) (hqmin s hs hn hs0)
  exact sub_eq_zero.mp hsz

variable [Fintype sigma]

private theorem exists_rigid_minimum
    (L : Submodule K (MvPolynomial sigma K)) [FiniteDimensional K L]
    (hclosed : ∀ p ∈ L, constantCoeff p = 0 → ∀ i, pderiv i p ∈ L)
    (hdim : 2 ≤ Module.finrank K L) :
    ∃ c : sigma → K, c ≠ 0 ∧ ∃ p : MvPolynomial sigma K,
      p ∈ L ∧ constantCoeff p ≠ 0 ∧
      (∀ r ∈ L, r ≠ 0 → p.totalDegree ≤ r.totalDegree) ∧
      ∃ F : Polynomial K, p = Polynomial.aeval (∑ i, c i • (X i : MvPolynomial sigma K)) F := by
  classical
  obtain ⟨q₀, hq₀, hq₀ne, hq₀0⟩ := exists_nonzero_evaluation_kernel L hdim
  obtain ⟨p, ⟨hp, hpne⟩, hpmin⟩ := exists_minimum_degree
    (fun p : MvPolynomial sigma K => p ∈ L ∧ p ≠ 0) ⟨q₀, hq₀, hq₀ne⟩
  have hpmin' : ∀ r ∈ L, r ≠ 0 → p.totalDegree ≤ r.totalDegree :=
    fun r hr hn => hpmin r ⟨hr, hn⟩
  have hp0 := minimum_has_nonzero_constantCoeff L hclosed p hp hpne hpmin'
  obtain ⟨q, ⟨hq, hqne, hq0⟩, hqmin⟩ := exists_minimum_degree
    (fun q : MvPolynomial sigma K => q ∈ L ∧ q ≠ 0 ∧ constantCoeff q = 0)
    ⟨q₀, hq₀, hq₀ne, hq₀0⟩
  have hqmin' : ∀ s ∈ L, s ≠ 0 → constantCoeff s = 0 → q.totalDegree ≤ s.totalDegree :=
    fun s hs hn hz => hqmin s ⟨hs, hn, hz⟩
  obtain ⟨j, hj⟩ : ∃ j, pderiv j q ≠ 0 := by
    by_contra hn
    have hD : ∀ j, pderiv j q = 0 := by simpa using hn
    exact hqne (by simpa [hq0] using eq_constant_of_partials_zero q hD)
  have hpq : p.totalDegree < q.totalDegree :=
    (hpmin' _ (hclosed q hq hq0 j) hj).trans_lt (totalDegree_pderiv_lt q j hj)
  -- The least kernel degree forces every partial into one scalar direction.
  let c : sigma → K := fun i => constantCoeff (pderiv i q) / constantCoeff p
  have hDq : ∀ i, pderiv i q = c i • p := by
    intro i
    by_cases hi : pderiv i q = 0
    · simp [hi, c]
    · exact small_degree_dependence L p q hp hp0 hpq hqmin' _
        (hclosed q hq hq0 i) (totalDegree_pderiv_lt q i hi)
  have hc : c ≠ 0 := by
    intro hz
    apply hj
    rw [hDq j, hz]
    simp
  have hDp : ∀ i j, c j • pderiv i p = c i • pderiv j p := by
    intro i j
    calc
      c j • pderiv i p = pderiv i (pderiv j q) := by rw [hDq j, Derivation.map_smul]
      _ = pderiv j (pderiv i q) := partials_commute q i j
      _ = c i • pderiv j p := by rw [hDq i, Derivation.map_smul]
  exact ⟨c, hc, p, hp, hp0, hpmin', (PolynomialTangentDescent.tangent_descent c hc p).mp hDp⟩

/-- Conditional derivative closure and exclusion of constants force a subspace
of dimension at least two into polynomials in one nonzero linear form. -/
theorem conditional_derivative_closed_subspace_rigidity
    (L : Submodule K (MvPolynomial sigma K)) [FiniteDimensional K L]
    (hconst : ∀ a : K, C a ∈ L → a = 0)
    (hclosed : ∀ p ∈ L, constantCoeff p = 0 → ∀ i, pderiv i p ∈ L)
    (hdim : 2 ≤ Module.finrank K L) :
    ∃ c : sigma → K, c ≠ 0 ∧ ∀ p ∈ L, ∃ F : Polynomial K,
      p = Polynomial.aeval (∑ i, c i • (X i : MvPolynomial sigma K)) F := by
  classical
  obtain ⟨c, hc, p, hp, hp0, hpmin, hpF⟩ := exists_rigid_minimum L hclosed hdim
  let ell : MvPolynomial sigma K := ∑ i, c i • X i
  let A : Subalgebra K (MvPolynomial sigma K) := Algebra.adjoin K {ell}
  have hpA : p ∈ A := by
    obtain ⟨F, rfl⟩ := hpF
    exact Polynomial.aeval_mem_adjoin_singleton K ell
  have hAll : ∀ h ∈ L, h ∈ A := by
    by_contra hn
    obtain ⟨h, ⟨hh, hhout⟩, hhmin⟩ := exists_minimum_degree
      (fun h : MvPolynomial sigma K => h ∈ L ∧ h ∉ A) (by simpa using hn)
    -- Normalization preserves the least-degree obstruction outside the subalgebra.
    let t : K := constantCoeff h / constantCoeff p
    let g := h - t • p
    have hg : g ∈ L := L.sub_mem hh (L.smul_mem t hp)
    have hg0 : constantCoeff g = 0 := by
      dsimp [g, t]
      simp [constantCoeff_smul, div_mul_cancel₀ _ hp0]
    have hhne : h ≠ 0 := by
      intro hz
      exact hhout (hz ▸ A.zero_mem)
    have hgdeg : g.totalDegree ≤ h.totalDegree := by
      exact (totalDegree_sub _ _).trans
        (max_le le_rfl ((totalDegree_smul_le t p).trans (hpmin h hh hhne)))
    have hgout : g ∉ A := by
      intro hgA
      apply hhout
      have he : h = g + t • p := by dsimp [g]; abel
      rw [he]
      exact A.add_mem hgA (A.smul_mem hpA t)
    have hdA : ∀ i, pderiv i g ∈ A := by
      intro i
      by_contra hi
      have hdne : pderiv i g ≠ 0 := by
        intro hz
        exact hi (hz ▸ A.zero_mem)
      have hdeg := (totalDegree_pderiv_lt g i hdne).trans_le hgdeg
      exact (not_le_of_gt hdeg) (hhmin _ ⟨hclosed g hg hg0 i, hi⟩)
    have hgradD : ∀ k i j, c j • pderiv i (pderiv k g) = c i • pderiv j (pderiv k g) := by
      intro k
      obtain ⟨F, hF⟩ := Algebra.adjoin_mem_exists_aeval K ell (hdA k)
      exact (PolynomialTangentDescent.tangent_descent c hc _).mpr ⟨F, hF.symm⟩
    have hgradg : ∀ i j, c j • pderiv i g = c i • pderiv j g := by
      intro i j
      let v := c j • pderiv i g - c i • pderiv j g
      have hvL : v ∈ L := L.sub_mem
        (L.smul_mem _ (hclosed g hg hg0 i)) (L.smul_mem _ (hclosed g hg hg0 j))
      have hvD : ∀ k, pderiv k v = 0 := by
        intro k
        dsimp [v]
        rw [map_sub, Derivation.map_smul, Derivation.map_smul,
          partials_commute g k i, partials_commute g k j]
        exact sub_eq_zero.mpr (hgradD k i j)
      have hvC := eq_constant_of_partials_zero v hvD
      have hv0 : constantCoeff v = 0 := hconst _ (hvC ▸ hvL)
      have hvz : v = 0 := by simpa [hv0] using hvC
      exact sub_eq_zero.mp hvz
    apply hgout
    obtain ⟨F, hF⟩ := (PolynomialTangentDescent.tangent_descent c hc g).mp hgradg
    rw [hF]
    exact Polynomial.aeval_mem_adjoin_singleton K ell
  refine ⟨c, hc, ?_⟩
  intro h hh
  obtain ⟨F, hF⟩ := Algebra.adjoin_mem_exists_aeval K ell (hAll h hh)
  exact ⟨F, hF.symm⟩

end D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity
