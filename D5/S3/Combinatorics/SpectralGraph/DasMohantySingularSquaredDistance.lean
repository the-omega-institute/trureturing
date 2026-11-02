/- GID: D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal multipartite squared-distance matrices and the singular source Laplacian rank-one bridge. -/

import D5.S3.QuadraticForms.StructuredRankOneInertia

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.SpectralGraph.DasMohantySingularSquaredDistance

variable {t : ℕ} (n : Fin t → ℕ)

/-- The actual vertices, with each part retaining its own finite carrier. -/
abbrev Vertex := Σ i : Fin t, Fin (n i)

def d (i : Fin t) : ℝ := 3 * (n i : ℝ) - 4

/-- Restriction to a set of parameters implements literal omission of parameters. -/
def phi (S : Finset (Fin t)) : ℝ := ∏ i ∈ S, d n i

def psi (S : Finset (Fin t)) : ℝ := ∑ i ∈ S, (n i : ℝ) * phi n (S.erase i)

def theta (S : Finset (Fin t)) : ℝ := phi n S + psi n S

def ratio : ℝ := ∑ i, (n i : ℝ) / d n i

/-- Squared shortest-path distances for a complete multipartite graph with at least two nonempty parts. -/
def delta : Matrix (Vertex n) (Vertex n) ℝ :=
  fun u v => if u = v then 0 else if u.1 = v.1 then 4 else 1

/-- Sum of all cofactors, equivalently the sum of all entries of the adjugate. -/
def cofactorSum : ℝ := ∑ u, ∑ v, (delta n).adjugate u v

/-- The three literal entry cases of equation (3.6), using omitted-list functions. -/
def sourceL : Matrix (Vertex n) (Vertex n) ℝ := fun u v =>
  if u = v then
    (((n u.1 : ℝ) - 1) / 2 * theta n (Finset.univ.erase u.1) +
      ((n u.1 : ℝ) - 3) * psi n (Finset.univ.erase u.1)) / (2 * psi n Finset.univ)
  else if u.1 = v.1 then
    -(theta n (Finset.univ.erase u.1) / 2 + psi n (Finset.univ.erase u.1)) /
      (2 * psi n Finset.univ)
  else phi n ((Finset.univ.erase u.1).erase v.1) / psi n Finset.univ

def blockBase : Matrix (Vertex n) (Vertex n) ℝ :=
  fun u v => (if u.1 = v.1 then 3 else 0) - if u = v then 4 else 0

/-- Explicit inverse candidate for the block base. -/
def blockInverse : Matrix (Vertex n) (Vertex n) ℝ :=
  fun u v => (if u.1 = v.1 then 3 / (4 * d n u.1) else 0) -
    if u = v then 1 / 4 else 0

def A : Matrix (Vertex n) (Vertex n) ℝ := -blockInverse n

def z : Vertex n → ℝ := fun u => 1 / d n u.1

private theorem d_ne_zero (hn : ∀ i, 0 < n i) (i : Fin t) : d n i ≠ 0 := by
  have hi := hn i
  by_cases h : n i = 1
  · simp [d, h]
  · have htwo : 2 ≤ n i := by omega
    have hreal : (2 : ℝ) ≤ n i := by exact_mod_cast htwo
    dsimp [d]
    linarith

private theorem phi_ne_zero (hn : ∀ i, 0 < n i) (S : Finset (Fin t)) :
    phi n S ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => d_ne_zero n hn i)

private theorem phi_erase (S : Finset (Fin t)) (i : Fin t) (hi : i ∈ S) :
    phi n S = d n i * phi n (S.erase i) := by
  exact (Finset.mul_prod_erase S (fun i => d n i) hi).symm

private theorem psi_ratio (hn : ∀ i, 0 < n i) (S : Finset (Fin t)) :
    psi n S = phi n S * ∑ i ∈ S, (n i : ℝ) / d n i := by
  rw [psi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [phi_erase n S i hi]
  field_simp [d_ne_zero n hn i]

private theorem omitted_ratio (hn : ∀ i, 0 < n i) (i : Fin t) :
    ∑ j ∈ Finset.univ.erase i, (n j : ℝ) / d n j = ratio n - (n i : ℝ) / d n i := by
  have h := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => (n j : ℝ) / d n j) (Finset.mem_univ i)
  dsimp [ratio]
  linarith

private theorem source_entries (hn : ∀ i, 0 < n i) (hr : ratio n = -1) :
    sourceL n = A n - vecMulVec (z n) (z n) := by
  have hp : psi n Finset.univ = -phi n Finset.univ := by
    rw [psi_ratio n hn]
    change phi n Finset.univ * ratio n = _
    rw [hr]
    ring
  have he (i : Fin t) : phi n (Finset.univ.erase i) = phi n Finset.univ / d n i := by
    rw [phi_erase n Finset.univ i (Finset.mem_univ i)]
    field_simp [d_ne_zero n hn i]
  have hpsi (i : Fin t) : psi n (Finset.univ.erase i) =
      phi n Finset.univ / d n i * (-1 - (n i : ℝ) / d n i) := by
    rw [psi_ratio n hn, he, omitted_ratio n hn, hr]
  have hee (i j : Fin t) (hij : i ≠ j) :
      phi n ((Finset.univ.erase i).erase j) = phi n Finset.univ / (d n i * d n j) := by
    have h := phi_erase n (Finset.univ.erase i) j (by simp [hij.symm])
    rw [he] at h
    apply (eq_div_iff (mul_ne_zero (d_ne_zero n hn i) (d_ne_zero n hn j))).mpr
    field_simp [d_ne_zero n hn i] at h
    nlinarith [h]
  ext u v
  have hu := d_ne_zero n hn u.1
  have hv := d_ne_zero n hn v.1
  have hP := phi_ne_zero n hn Finset.univ
  by_cases huv : u = v
  · subst v
    simp only [sourceL, if_pos rfl, theta, he, hpsi, hp, A, blockInverse,
      neg_apply, sub_apply, vecMulVec_apply, z]
    dsimp [d] at *
    field_simp
    <;> ring
  · by_cases hij : u.1 = v.1
    · simp only [sourceL, if_neg huv, if_pos hij, theta, he, hpsi, hp, A,
        blockInverse, neg_apply, sub_apply, vecMulVec_apply, z, hij]
      dsimp [d] at *
      field_simp
      <;> ring
    · simp only [sourceL, if_neg huv, if_neg hij, hee _ _ hij, hp, A,
        blockInverse, neg_apply, sub_apply, vecMulVec_apply, z]
      field_simp
      <;> ring

private theorem inverse_mul_one (hn : ∀ i, 0 < n i) :
    blockInverse n *ᵥ (fun _ => 1) = z n := by
  funext u
  simp only [mulVec, dotProduct, blockInverse, mul_one, z]
  rw [Finset.sum_sub_distrib, Fintype.sum_sigma]
  simp only [Finset.sum_ite_irrel, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.sum_eq_single u.1]
  · simp only [ite_true]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    dsimp [d]
    field_simp [d_ne_zero n hn u.1]
    <;> ring
  · intro j _ hj
    simp [hj.symm]
  · simp

private theorem inverse_mul_base (hn : ∀ i, 0 < n i) :
    blockInverse n * blockBase n = 1 := by
  ext u v
  simp only [mul_apply, blockInverse, blockBase]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  have hs : (∑ x : Vertex n,
      (if u.1 = x.1 then 3 / (4 * d n u.1) else 0) * (if x.1 = v.1 then 3 else 0)) =
      if u.1 = v.1 then (n u.1 : ℝ) * (3 / (4 * d n u.1)) * 3 else 0 := by
    rw [Fintype.sum_sigma]
    by_cases h : u.1 = v.1
    · subst h
      simp [Finset.mul_sum, ← mul_assoc, eq_comm]
    · simp [h, eq_comm]
  rw [hs]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ite_mul, zero_mul, Finset.sum_ite_eq]
  by_cases huv : u = v
  · subst v
    simp only [ite_true, Matrix.one_apply_eq]
    dsimp [d]
    field_simp [d_ne_zero n hn u.1]
    <;> ring
  · by_cases hij : u.1 = v.1 <;> simp [huv, hij, Matrix.one_apply, d]
    field_simp [d_ne_zero n hn u.1]
    <;> ring

private theorem delta_decomposition :
    delta n = blockBase n +
      replicateCol Unit (fun _ => (1 : ℝ)) * replicateRow Unit (fun _ => (1 : ℝ)) := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp [delta, blockBase, mul_apply]
  · by_cases hij : u.1 = v.1 <;> simp [delta, blockBase, mul_apply, huv, hij]

private theorem singular_ratio (hn : ∀ i, 0 < n i) (hs : (delta n).det = 0) :
    ratio n = -1 := by
  have hm : blockInverse n * delta n = 1 +
      replicateCol Unit (z n) * replicateRow Unit (fun _ => (1 : ℝ)) := by
    rw [delta_decomposition, Matrix.mul_add, inverse_mul_base n hn,
      ← Matrix.mul_assoc, Matrix.mul_replicateCol, inverse_mul_one n hn]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, hs, mul_zero,
    Matrix.det_one_add_replicateCol_mul_replicateRow] at hd
  have hz : (fun _ : Vertex n => (1 : ℝ)) ⬝ᵥ z n = ratio n := by
    simp [dotProduct, z, ratio, Fintype.sum_sigma, div_eq_mul_inv]
  rw [hz] at hd
  linarith

private theorem a_hermitian : (A n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro u v
  by_cases h : u.1 = v.1
  · simp [A, blockInverse, h, h.symm, eq_comm]
  · simp [A, blockInverse, h, h.symm, eq_comm]

private theorem pivot_one (hn : ∀ i, 0 < n i) (hr : ratio n = -1) :
    D5.S3.QuadraticForms.StructuredRankOneInertia.pivot (A n) (fun _ => 1) = 1 := by
  rw [D5.S3.QuadraticForms.StructuredRankOneInertia.pivot, A, neg_mulVec,
    inverse_mul_one n hn]
  have hz : (fun _ : Vertex n => (1 : ℝ)) ⬝ᵥ z n = ratio n := by
    simp [dotProduct, z, ratio, Fintype.sum_sigma, div_eq_mul_inv]
  rw [dotProduct_neg, hz, hr]
  norm_num

/-- The literal singular source matrix is the structured downdate with pivot exactly one. -/
theorem singular_source_downdate (hn : ∀ i, 0 < n i) (hs : (delta n).det = 0) :
    psi n Finset.univ ≠ 0 ∧
    D5.S3.QuadraticForms.StructuredRankOneInertia.pivot (A n) (fun _ => 1) = 1 ∧
    sourceL n = D5.S3.QuadraticForms.StructuredRankOneInertia.downdate
      (A n) (fun _ => 1) := by
  have hr := singular_ratio n hn hs
  have hp := pivot_one n hn hr
  refine ⟨?_, hp, ?_⟩
  · rw [psi_ratio n hn]
    change phi n Finset.univ * ratio n ≠ 0
    rw [hr]
    exact mul_ne_zero (phi_ne_zero n hn _) (by norm_num)
  · rw [source_entries n hn hr,
      D5.S3.QuadraticForms.StructuredRankOneInertia.downdate, hp]
    simp only [inv_one, one_smul, A, neg_mulVec, inverse_mul_one n hn]
    congr 1
    ext u v
    simp [vecMulVec]

#print axioms singular_source_downdate

end D5.S3.Combinatorics.SpectralGraph.DasMohantySingularSquaredDistance
