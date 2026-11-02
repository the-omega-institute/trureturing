/- GID: D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal multipartite squared-distance matrices and the singular source Laplacian rank-one bridge. -/

import D5.S3.QuadraticForms.StructuredRankOneInertia

/-! Literal source functions and their singular rank-one identity. -/

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
  · norm_num [d, h]
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

private theorem omitted_ratio (i : Fin t) :
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
    rw [psi_ratio n hn, he, omitted_ratio n, hr]
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
    simp only [sourceL, ite_true, theta, he, hpsi, hp, A, blockInverse,
      Matrix.neg_apply, Matrix.sub_apply, vecMulVec_apply, z]
    field_simp [hu, hv, hP]
    <;> (dsimp [d]; ring)
  · by_cases hij : u.1 = v.1
    · simp only [sourceL, ite_eq_right huv, theta, he, hpsi, hp, A,
        blockInverse, Matrix.neg_apply, Matrix.sub_apply, vecMulVec_apply, z, hij]
      dsimp [d] at *
      field_simp
      <;> ring
    · simp only [sourceL, ite_eq_right huv, ite_eq_right hij, hee _ _ hij, hp, A,
        blockInverse, Matrix.neg_apply, Matrix.sub_apply, vecMulVec_apply, z]
      field_simp
      <;> ring

private theorem inverse_action (f : Vertex n → ℝ) (u : Vertex n) :
    (blockInverse n *ᵥ f) u =
      3 / (4 * d n u.1) * (∑ j : Fin (n u.1), f ⟨u.1, j⟩) - f u / 4 := by
  have hfirst : (∑ x : Vertex n,
      (if u.1 = x.1 then 3 / (4 * d n u.1) else 0) * f x) =
      3 / (4 * d n u.1) * ∑ j : Fin (n u.1), f ⟨u.1, j⟩ := by
    rw [Fintype.sum_sigma]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_eq_single u.1]
    · simp [Finset.mul_sum]
    · intro i _ hi
      simp [hi.symm]
    · simp
  simp only [mulVec, dotProduct, blockInverse, sub_mul, Finset.sum_sub_distrib]
  rw [hfirst]
  simp only [ite_mul, zero_mul]
  simp [div_eq_mul_inv, mul_comm]

private theorem inverse_mul_one (hn : ∀ i, 0 < n i) :
    blockInverse n *ᵥ (fun _ => 1) = z n := by
  funext u
  rw [inverse_action]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, z]
  have hu := d_ne_zero n hn u.1
  dsimp [d] at *
  field_simp
  <;> ring

private theorem inverse_mul_base (hn : ∀ i, 0 < n i) :
    blockInverse n * blockBase n = 1 := by
  ext u v
  change (blockInverse n *ᵥ (fun x => blockBase n x v)) u = _
  rw [inverse_action]
  rcases u with ⟨i, j⟩
  rcases v with ⟨k,l⟩
  by_cases hik : i = k
  · subst k
    simp [blockBase, Matrix.one_apply, Finset.sum_sub_distrib, eq_comm]
    have hi := d_ne_zero n hn i
    dsimp [d] at *
    split_ifs <;> field_simp <;> ring
  · have huv : (⟨i, j⟩ : Vertex n) ≠ ⟨k,l⟩ := by
      intro h
      exact hik (congrArg Sigma.fst h)
    simp [blockBase, hik, huv]

private theorem delta_decomposition :
    delta n = blockBase n +
      replicateCol Unit (fun _ => (1 : ℝ)) * replicateRow Unit (fun _ => (1 : ℝ)) := by
  ext u v
  by_cases huv : u = v
  · subst v
    norm_num [delta, blockBase, mul_apply]
  · by_cases hij : u.1 = v.1 <;> norm_num [delta, blockBase, mul_apply, huv, hij]

private theorem singular_ratio (hn : ∀ i, 0 < n i) (hs : (delta n).det = 0) :
    ratio n = -1 := by
  have hm : blockInverse n * delta n = 1 +
      replicateCol Unit (z n) * replicateRow Unit (fun _ => (1 : ℝ)) := by
    rw [delta_decomposition, Matrix.mul_add, inverse_mul_base n hn,
      ← Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, inverse_mul_one n hn]
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
  change -(blockInverse n v u) = -(blockInverse n u v)
  by_cases huv : u = v
  · subst v
    rfl
  · by_cases h : u.1 = v.1
    · simp [blockInverse, h, huv, Ne.symm huv]
    · simp [blockInverse, h, Ne.symm h, huv, Ne.symm huv]

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

private theorem a_action (f : Vertex n → ℝ) (u : Vertex n) :
    (A n *ᵥ f) u = f u / 4 -
      3 / (4 * d n u.1) * ∑ j : Fin (n u.1), f ⟨u.1, j⟩ := by
  rw [A, neg_mulVec, Pi.neg_apply, inverse_action]
  ring

private theorem zero_a (hn : ∀ i, 0 < n i) :
    D5.S3.QuadraticForms.StructuredRankOneInertia.zeroIndex (a_hermitian n) = 0 := by
  have hdet : (A n).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse (B := -blockBase n)
    rw [A, neg_mul_neg, inverse_mul_base n hn]
  have hall : ∀ i, (a_hermitian n).eigenvalues i ≠ 0 := by
    rw [(a_hermitian n).det_eq_prod_eigenvalues] at hdet
    simpa using Finset.prod_ne_zero_iff.mp hdet
  simp [D5.S3.QuadraticForms.StructuredRankOneInertia.zeroIndex, hall]

private theorem deviation_action (hn : ∀ i, 0 < n i) (hr : ratio n = -1)
    (w : Vertex n → ℝ) (hw : ∀ i, ∑ j : Fin (n i), w ⟨i, j⟩ = 0) :
    sourceL n *ᵥ w = (1 / 4 : ℝ) • w := by
  have hz : z n ⬝ᵥ w = 0 := by
    simp [dotProduct, z, Fintype.sum_sigma, ← Finset.mul_sum, hw]
  have ha : A n *ᵥ w = (1 / 4 : ℝ) • w := by
    funext u
    rw [a_action, hw]
    simp [div_eq_mul_inv, mul_comm]
  rw [source_entries n hn hr, sub_mulVec, ha, vecMulVec_mulVec, hz]
  simp

private theorem singleton_action (hn : ∀ i, 0 < n i) (hr : ratio n = -1)
    (w : Vertex n → ℝ) (hw : ∀ i, n i ≠ 1 → ∀ j, w ⟨i, j⟩ = 0)
    (hsum : ∑ u, w u = 0) : sourceL n *ᵥ w = w := by
  have hz : z n ⬝ᵥ w = 0 := by
    have hterm : ∀ u : Vertex n, z n u * w u = -w u := by
      intro u
      by_cases hi : n u.1 = 1
      · norm_num [z, d, hi]
      · have h := hw u.1 hi u.2
        simp only [Sigma.eta] at h
        simp [h]
    simp only [dotProduct, hterm, Finset.sum_neg_distrib, hsum, neg_zero]
  have ha : A n *ᵥ w = w := by
    funext u
    rw [a_action]
    by_cases hi : n u.1 = 1
    · have hs : (∑ j : Fin (n u.1), w ⟨u.1, j⟩) = w u := by
        calc
          (∑ j : Fin (n u.1), w ⟨u.1, j⟩) = ∑ _j : Fin (n u.1), w u := by
            apply Finset.sum_congr rfl
            intro j _
            have hj : j = u.2 := by
              apply Fin.ext
              have hjb := j.isLt
              have hub := u.2.isLt
              omega
            subst j
            rfl
          _ = w u := by simp [hi]
      rw [hs]
      norm_num [d, hi]
      ring
    · have hu := hw u.1 hi u.2
      simp only [Sigma.eta] at hu
      simp [hw _ hi]
  rw [source_entries n hn hr, sub_mulVec, ha, vecMulVec_mulVec, hz]
  simp

private def partSum : (Vertex n → ℝ) →ₗ[ℝ] (Fin t → ℝ) where
  toFun w i := ∑ j : Fin (n i), w ⟨i, j⟩
  map_add' w v := by ext i; simp [Finset.sum_add_distrib]
  map_smul' c w := by ext i; simp [Finset.mul_sum]

/-- The actual subspace of vectors with zero sum in every part. -/
def deviationSpace : Submodule ℝ (Vertex n → ℝ) := LinearMap.ker (partSum n)

private theorem deviation_dimension (hn : ∀ i, 0 < n i) :
    Module.finrank ℝ (deviationSpace n) = (∑ i, n i) - t := by
  have hsurj : Function.Surjective (partSum n) := by
    intro f
    refine ⟨fun u => f u.1 / (n u.1 : ℝ), ?_⟩
    funext i
    change (∑ _j : Fin (n i), f i / (n i : ℝ)) = f i
    have hi : (n i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hn i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h := (partSum n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
  have hd : Fintype.card (Vertex n) = ∑ i, n i := by
    simp only [Vertex, Fintype.card_sigma, Fintype.card_fin]
  simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fin] at h
  rw [hd] at h
  change t + Module.finrank ℝ (deviationSpace n) = ∑ i, n i at h
  omega

/-- Source-level inertia transfer and the two exact positive-eigenvector families. -/
theorem singular_source_reduction (hn : ∀ i, 0 < n i) (hs : (delta n).det = 0) :
    ∃ hA : (A n).IsHermitian, ∃ hL : (sourceL n).IsHermitian,
      RHLinalg.posIndex hA = RHLinalg.posIndex hL + 1 ∧
      RHLinalg.negIndex hL = RHLinalg.negIndex hA ∧
      D5.S3.QuadraticForms.StructuredRankOneInertia.zeroIndex hL = 1 ∧
      (∀ w : Vertex n → ℝ, (∀ i, ∑ j : Fin (n i), w ⟨i, j⟩ = 0) →
        sourceL n *ᵥ w = (1 / 4 : ℝ) • w) ∧
      (∀ w : Vertex n → ℝ, (∀ i, n i ≠ 1 → ∀ j, w ⟨i, j⟩ = 0) →
        (∑ u, w u = 0) → sourceL n *ᵥ w = w) ∧
      Module.finrank ℝ (deviationSpace n) = (∑ i, n i) - t := by
  obtain ⟨_, hp, hsource⟩ := singular_source_downdate n hn hs
  obtain ⟨hM, hi, _⟩ :=
    D5.S3.QuadraticForms.StructuredRankOneInertia.inertia_downdate
      (A n) (a_hermitian n) (fun _ => 1) (by rw [hp]; norm_num)
  have hpos : 0 < D5.S3.QuadraticForms.StructuredRankOneInertia.pivot
      (A n) (fun _ => 1) := by rw [hp]; norm_num
  obtain ⟨hplus,hminus,hzero⟩ := hi hpos
  have hL : (sourceL n).IsHermitian := by rw [hsource]; exact hM
  refine ⟨a_hermitian n, hL, ?_, ?_, ?_, ?_, ?_, deviation_dimension n hn⟩
  · simpa only [hsource] using hplus
  · simpa only [hsource] using hminus
  · rw [zero_a n hn] at hzero
    simpa only [hsource] using hzero
  · exact fun w hw => deviation_action n hn (singular_ratio n hn hs) w hw
  · exact fun w hw hsum => singleton_action n hn (singular_ratio n hn hs) w hw hsum

/-- The complete unchanged two-clause target, with algebraic positive multiplicities. -/
def completeConjecture : Prop :=
  ∀ (t : ℕ) (n : Fin t → ℕ), 2 ≤ t → (∀ i, 0 < n i) →
    cofactorSum n ≠ 0 → (delta n).det = 0 →
    ∃ hL : (sourceL n).IsHermitian,
      ((sourceL n).charpoly.roots.filter (fun x => 0 < x) =
        Multiset.replicate ((∑ i, n i) - t) (1 / 4 : ℝ) +
        Multiset.replicate ((Finset.univ.filter (fun i => n i = 1)).card - 1) 1) ∧
      RHLinalg.posIndex hL =
        (∑ i, n i) - (Finset.univ.filter (fun i => 2 ≤ n i)).card - 1 ∧
      D5.S3.QuadraticForms.StructuredRankOneInertia.zeroIndex hL = 1 ∧
      RHLinalg.negIndex hL = (Finset.univ.filter (fun i => 2 ≤ n i)).card

#print axioms singular_source_downdate
#print axioms singular_source_reduction

end D5.S3.Combinatorics.SpectralGraph.DasMohantySingularSquaredDistance
