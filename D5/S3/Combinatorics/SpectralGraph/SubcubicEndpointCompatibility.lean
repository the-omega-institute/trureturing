/- GID: D5/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SubcubicEndpointCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite moments classify rational endpoint compatibility of subcubic trees. -/
import D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates

/-! Rational symmetric competitors of every finite order and actual rooted tree geometry. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility

open Matrix Polynomial Finset SimpleGraph
open D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Agreement through the stated index at the actual port and the competitor's first endpoint.
Every positive finite order occurs as `n+1`, including order one. -/
def MatchesThrough (M : Matrix V V ℚ) (o : V) {n : ℕ}
    (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (d : ℕ) : Prop :=
  ∀ k ≤ d, (M ^ k) o o = (J ^ k) 0 0

/-- Exact agreement of every moment, without an order bound. -/
def Compatible (M : Matrix V V ℚ) (o : V) : Prop :=
  ∃ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ),
    PositiveJacobi J ∧ ∀ k, (M ^ k) o o = (J ^ k) 0 0

/-- The uniform rational endpoint path matrix of the indicated actual order. -/
def pathMatrix (n : ℕ) (a c : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  uniformMatrix (pathGraph n) a c

private theorem path_positive (n : ℕ) (a c : ℚ) (hc : 0 < c) :
    PositiveJacobi (pathMatrix n a c) := by
  constructor
  · exact (Matrix.isSymm_one.smul a).add (((pathGraph n).isSymm_adjMatrix).smul c)
  · intro i j hfar
    have hne : i ≠ j := by intro h; subst j; omega
    have hn : ¬(pathGraph n).Adj i j := by rw [pathGraph_adj]; omega
    simp [pathMatrix, uniformMatrix, hne, hn]
  · intro j hj
    have hne : (⟨j, by omega⟩ : Fin n) ≠ ⟨j + 1, hj⟩ := by
      intro h
      have hh : j = j + 1 := congrArg Fin.val h
      omega
    have ha : (pathGraph n).Adj ⟨j, by omega⟩ ⟨j + 1, hj⟩ := by
      rw [pathGraph_adj]; exact Or.inl rfl
    simpa [pathMatrix, uniformMatrix, Matrix.one_apply, hne, ha] using hc

omit [Fintype V] in
private theorem path_reindex {n : ℕ} (e : G ≃g pathGraph (n + 1)) (a c : ℚ) :
    (uniformMatrix G a c).reindex e.toEquiv e.toEquiv = pathMatrix (n + 1) a c := by
  ext i j
  have hij : e.toEquiv.symm i = e.toEquiv.symm j ↔ i = j :=
    e.toEquiv.symm.injective.eq_iff
  have hadj : G.Adj (e.toEquiv.symm i) (e.toEquiv.symm j) ↔ (pathGraph (n + 1)).Adj i j := by
    exact e.symm.map_rel_iff
  simp only [uniformMatrix, pathMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, adjMatrix_apply]
  simp only [hij, hadj]

private theorem reindex_moments {n : ℕ} (M : Matrix V V ℚ) (o : V)
    (e : V ≃ Fin (n + 1)) (ho : e o = 0) (k : ℕ) :
    (M ^ k) o o = ((M.reindex e e) ^ k) 0 0 := by
  have hp := (Matrix.reindexAlgEquiv ℚ ℚ e).map_pow M k
  have hz : e.symm 0 = o := by rw [← ho, e.symm_apply_apply]
  change (M ^ k).reindex e e = (M.reindex e e) ^ k at hp
  have hh := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ => A 0 0) hp
  change (M ^ k) (e.symm 0) (e.symm 0) = _ at hh
  simpa only [hz] using hh

private theorem endpoint_compatible (o : V) (a c : ℚ) (hc : 0 < c)
    (hp : EndpointPath G o) : Compatible (uniformMatrix G a c) o := by
  obtain ⟨n, e, ho⟩ := hp
  refine ⟨n, pathMatrix (n + 1) a c, path_positive _ a c hc, ?_⟩
  intro k
  rw [← path_reindex e a c]
  exact reindex_moments _ o e.toEquiv ho k

private theorem prefix_rigidity {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n r : ℕ} (hr : 0 < r) (a c : K) (hc : 0 < c)
    (o : V) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hJ : PositiveJacobi J)
    (hm : ∀ k ≤ 2 * r, ((uniformMatrix G a c) ^ k) o o = (J ^ k) 0 0)
    (hu : ∀ j < r, chainNorm (uniformMatrix G a c) o a c j = 1)
    (hd : ∀ j < r, chainVector (uniformMatrix G a c) o a c j ⬝ᵥ
      (uniformMatrix G a c *ᵥ chainVector (uniformMatrix G a c) o a c j) = a) :
    r ≤ n + 1 ∧ (∀ j < r, diagonalAt J j = a) ∧
      (∀ j, j + 1 < r → nextLink J j = c) ∧
      chainNorm (uniformMatrix G a c) o a c r =
        (c⁻¹ * nextLink J (r - 1)) ^ 2 * (if r < n + 1 then 1 else 0) := by
  have hs : (uniformMatrix G a c).IsSymm :=
    (Matrix.isSymm_one.smul a).add ((G.isSymm_adjMatrix).smul c)
  have hun : ∀ j < r, chainVector J 0 a c j ⬝ᵥ chainVector J 0 a c j = 1 := by
    intro j hj
    rw [← prefix_chain_pairing _ J hs hJ.symmetric o 0 a c (2 * r) j j hm (by omega)]
    exact hu j hj
  have hdn : ∀ j < r, chainVector J 0 a c j ⬝ᵥ (J *ᵥ chainVector J 0 a c j) = a := by
    intro j hj
    rw [← prefix_chain_diagonal _ J hs hJ.symmetric o 0 a c (2 * r) j hm (by omega)]
    exact hd j hj
  obtain ⟨hb, hdi, hli, hnorm⟩ :=
    positive_jacobi_prefix_rigidity (Nat.zero_lt_succ n) hr J hJ a c hc hun hdn
  refine ⟨hb, hdi, hli, ?_⟩
  rw [chainNorm, prefix_chain_pairing _ J hs hJ.symmetric o 0 a c (2 * r) r r hm (by omega)]
  exact hnorm

private theorem rational_boundary_zero {n r b : ℕ} (hr : 0 < r)
    (a c : ℚ) (hc : 0 < c) (o : V)
    (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hJ : PositiveJacobi J)
    (hm : MatchesThrough (uniformMatrix G a c) o J (2 * r))
    (hu : ∀ j < r, chainNorm (uniformMatrix G a c) o a c j = 1)
    (hd : ∀ j < r, chainVector (uniformMatrix G a c) o a c j ⬝ᵥ
      (uniformMatrix G a c *ᵥ chainVector (uniformMatrix G a c) o a c j) = a)
    (hb : b = 0 ∨ b = 2 ∨ b = 3)
    (hnorm : chainNorm (uniformMatrix G a c) o a c r = (b : ℚ)) : b = 0 := by
  obtain ⟨hbound, _, _, hh⟩ := prefix_rigidity hr a c hc o J hJ hm hu hd
  by_cases he : r = n + 1
  · rw [ite_eq_right (by omega : ¬r < n + 1), mul_zero, hnorm] at hh
    exact_mod_cast hh
  · have hlt : r < n + 1 := by omega
    rw [ite_eq_left hlt, mul_one, hnorm] at hh
    have hsquare : IsSquare (b : ℚ) := ⟨c⁻¹ * nextLink J (r - 1), by simpa [pow_two] using hh⟩
    have hsq : IsSquare b := Rat.isSquare_natCast_iff.mp hsquare
    rcases hb with h0 | h2 | h3
    · exact h0
    · exact False.elim (Nat.prime_two.not_isSquare (h2 ▸ hsq))
    · exact False.elim (Nat.prime_three.not_isSquare (h3 ▸ hsq))

private theorem coefficients_unique {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hJ : PositiveJacobi J) (a c : ℚ)
    (hd : ∀ j < n + 1, diagonalAt J j = a)
    (hl : ∀ j, j + 1 < n + 1 → nextLink J j = c) :
    J = pathMatrix (n + 1) a c := by
  ext i j
  by_cases he : i = j
  · subst j
    have hh := hd i.val i.isLt
    simpa [diagonalAt, i.isLt, pathMatrix, uniformMatrix] using hh
  · by_cases hn : i.val + 1 = j.val
    · have hj : i.val + 1 < n + 1 := by omega
      have hh := hl i.val hj
      have hje : (⟨i.val + 1, hj⟩ : Fin (n + 1)) = j := Fin.ext hn
      have ha : (pathGraph (n + 1)).Adj i j := by rw [pathGraph_adj]; exact Or.inl hn
      simpa [nextLink, hj, hje, pathMatrix, uniformMatrix, Matrix.one_apply, he, ha] using hh
    · by_cases hp : j.val + 1 = i.val
      · have hi : j.val + 1 < n + 1 := by omega
        have hh := hl j.val hi
        have hie : (⟨j.val + 1, hi⟩ : Fin (n + 1)) = i := Fin.ext hp
        have ha : (pathGraph (n + 1)).Adj i j := by rw [pathGraph_adj]; exact Or.inr hp
        rw [hJ.symmetric.apply]
        simpa [nextLink, hi, hie, pathMatrix, uniformMatrix, Matrix.one_apply, he, ha] using hh
      · have hf : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
          have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
          omega
        have ha : ¬(pathGraph (n + 1)).Adj i j := by rw [pathGraph_adj]; tauto
        rw [hJ.band i j hf]
        simp [pathMatrix, uniformMatrix, he, ha]

private theorem zero_prefix_unique {n r : ℕ} (hr : 0 < r)
    (a c : ℚ) (hc : 0 < c) (o : V)
    (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hJ : PositiveJacobi J)
    (hm : MatchesThrough (uniformMatrix G a c) o J (2 * r))
    (hu : ∀ j < r, chainNorm (uniformMatrix G a c) o a c j = 1)
    (hd : ∀ j < r, chainVector (uniformMatrix G a c) o a c j ⬝ᵥ
      (uniformMatrix G a c *ᵥ chainVector (uniformMatrix G a c) o a c j) = a)
    (hz : chainNorm (uniformMatrix G a c) o a c r = 0) :
    n + 1 = r ∧ J = pathMatrix (n + 1) a c := by
  obtain ⟨hb, hdi, hli, hh⟩ := prefix_rigidity hr a c hc o J hJ hm hu hd
  have he : n + 1 = r := by
    by_contra hne
    have hlt : r < n + 1 := by omega
    have hj : r - 1 + 1 < n + 1 := by omega
    have hp : 0 < nextLink J (r - 1) := by
      simpa only [nextLink, dite_eq_left hj] using hJ.positive (r - 1) hj
    rw [hz, ite_eq_left hlt, mul_one] at hh
    have hpos : 0 < (c⁻¹ * nextLink J (r - 1)) ^ 2 :=
      sq_pos_of_pos (mul_pos (inv_pos.mpr hc) hp)
    linarith
  refine ⟨he, coefficients_unique J hJ a c ?_ ?_⟩
  · simpa only [he] using hdi
  · simpa only [he] using hli

/-- Complete rational endpoint compatibility, with the actual first-departure prefix,
all finite competitor orders, and the genuine positive coordinate permutation. -/
theorem complete78_3 (hG : G.IsTree) (hdeg : ∀ x, G.degree x ≤ 3)
    (o : V) (a c : ℚ) (hc : 0 < c) :
    ∃ r : ℕ, ∃ hr : 0 < r, r ≤ Fintype.card V ∧
      (∀ j < r, chainNorm (uniformMatrix G a c) o a c j = 1) ∧
      chainNorm (uniformMatrix G a c) o a c r ≠ 1 ∧
      (chainNorm (uniformMatrix G a c) o a c r = 0 ↔ EndpointPath G o) ∧
      (chainNorm (uniformMatrix G a c) o a c r = 0 ∨
        chainNorm (uniformMatrix G a c) o a c r = 2 ∨
        chainNorm (uniformMatrix G a c) o a c r = 3) ∧
      (Compatible (uniformMatrix G a c) o ↔ EndpointPath G o) ∧
      (¬ EndpointPath G o → ∀ (n : ℕ)
        (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ), PositiveJacobi J →
          ¬ MatchesThrough (uniformMatrix G a c) o J (2 * r)) ∧
      (EndpointPath G o → r = Fintype.card V ∧
        (∃ e : G ≃g pathGraph r, e o = ⟨0, hr⟩ ∧
          (uniformMatrix G a c).reindex e.toEquiv e.toEquiv = pathMatrix r a c ∧
          (Pi.single o (1 : ℚ)) ∘ e.toEquiv.symm = Pi.single ⟨0, hr⟩ 1 ∧
          (∀ v : V → ℚ, pathMatrix r a c *ᵥ (v ∘ e.toEquiv.symm) =
            (uniformMatrix G a c *ᵥ v) ∘ e.toEquiv.symm) ∧
          ∀ k, ((uniformMatrix G a c) ^ k) o o =
            ((pathMatrix r a c) ^ k) ⟨0, hr⟩ ⟨0, hr⟩) ∧
        ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ),
          PositiveJacobi J → MatchesThrough (uniformMatrix G a c) o J (2 * r) →
            n + 1 = r ∧ J = pathMatrix (n + 1) a c) := by
  obtain ⟨z, p, hp, hs, hr, hbound, hgram, hdiag, hnorm, hcard, _, hpath, _, _⟩ :=
    tree_first_departure hG hdeg o a c hc
  have hu : ∀ j < p.length + 1, chainNorm (uniformMatrix G a c) o a c j = 1 := by
    intro j hj
    simpa only [chainNorm, ite_true] using hgram j hj j hj
  have compatible_zero : Compatible (uniformMatrix G a c) o → (forward p).card = 0 := by
    rintro ⟨n, J, hJ, hm⟩
    exact rational_boundary_zero hr a c hc o J hJ (fun k _ => hm k) hu hdiag hcard hnorm
  have zero_path : (forward p).card = 0 → EndpointPath G o := by
    intro hz
    obtain ⟨e, ho⟩ := hpath hz
    exact ⟨p.length, e, ho⟩
  have path_zero : EndpointPath G o → (forward p).card = 0 := by
    intro he
    exact compatible_zero (endpoint_compatible o a c hc he)
  have hziff : chainNorm (uniformMatrix G a c) o a c (p.length + 1) = 0 ↔
      EndpointPath G o := by
    rw [hnorm]
    constructor
    · intro hz
      exact zero_path (by exact_mod_cast hz)
    · intro he
      rw [path_zero he, Nat.cast_zero]
  refine ⟨p.length + 1, hr, hbound, hu, ?_, hziff, ?_, ?_, ?_, ?_⟩
  · rw [hnorm]
    rcases hcard with hh | hh | hh <;> rw [hh] <;> norm_num
  · rw [hnorm]
    rcases hcard with hh | hh | hh
    · exact Or.inl (by rw [hh]; rfl)
    · exact Or.inr (Or.inl (by rw [hh]; rfl))
    · exact Or.inr (Or.inr (by rw [hh]; rfl))
  · exact ⟨fun h => zero_path (compatible_zero h), endpoint_compatible o a c hc⟩
  · intro hnot n J hJ hm
    exact hnot (zero_path (rational_boundary_zero hr a c hc o J hJ hm hu hdiag hcard hnorm))
  · intro he
    have hz := path_zero he
    have hn : chainNorm (uniformMatrix G a c) o a c (p.length + 1) = 0 := hziff.mpr he
    obtain ⟨e, ho⟩ := hpath hz
    have hsize : p.length + 1 = Fintype.card V := by
      simpa only [Fintype.card_fin] using (Fintype.card_congr e.toEquiv).symm
    refine ⟨hsize, ⟨e, ho, path_reindex e a c, ?_, ?_, ?_⟩, ?_⟩
    · ext i
      have heo : e.toEquiv.symm 0 = o := by rw [← ho]; exact e.toEquiv.symm_apply_apply o
      have hi : e.toEquiv.symm i = o ↔ i = 0 := by
        constructor
        · intro h
          exact e.toEquiv.symm.injective (h.trans heo.symm)
        · intro h
          exact (congrArg e.toEquiv.symm h).trans heo
      have hzfin : (0 : Fin (p.length + 1)) = ⟨0, hr⟩ := by ext; simp
      simp only [Function.comp_apply, Pi.single_apply, hi, hzfin]
    · intro v
      rw [← path_reindex e a c]
      change (uniformMatrix G a c).submatrix e.toEquiv.symm e.toEquiv.symm *ᵥ
        (v ∘ e.toEquiv.symm) = _
      rw [Matrix.submatrix_mulVec_equiv]
      have hv : (v ∘ e.toEquiv.symm) ∘ e.toEquiv = v := by
        funext x
        exact congrArg v (e.toEquiv.symm_apply_apply x)
      change (uniformMatrix G a c *ᵥ ((v ∘ e.toEquiv.symm) ∘ e.toEquiv)) ∘
        e.toEquiv.symm = _
      rw [hv]
    · intro k
      rw [← path_reindex e a c]
      exact reindex_moments _ o e.toEquiv ho k
    · intro n J hJ hm
      exact zero_prefix_unique hr a c hc o J hJ hm hu hdiag hn

end D5.S3.Combinatorics.SpectralGraph.SubcubicEndpointCompatibility
