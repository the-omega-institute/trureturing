/- GID: D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal multipartite squared-distance matrices and the singular source Laplacian rank-one bridge. -/

import D5.S3.QuadraticForms.StructuredRankOneInertia
import Mathlib.LinearAlgebra.Eigenspace.Zero

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

private def first (hn : ∀ i, 0 < n i) (i : Fin t) : Vertex n := ⟨i, ⟨0, hn i⟩⟩

private def changeBasis : Matrix (Vertex n) (Vertex n) ℝ := fun u v =>
  (if u = v then 1 else 0) +
  (if u.1 = v.1 then if v.2.val = 0 then 1 else 0 else 0) -
  (if u.1 = v.1 then if u.2.val = 0 then 1 else 0 else 0)

private def diagonalValues (u : Vertex n) : ℝ :=
  if u.2.val = 0 then -1 / d n u.1 else 1 / 4

private theorem changeBasis_sum (hn : ∀ i, 0 < n i) (v : Vertex n) (i : Fin t) :
    (∑ j : Fin (n i), changeBasis n ⟨i,j⟩ v) =
      if i = v.1 then (if v.2.val = 0 then (n i : ℝ) else 0) else 0 := by
  rcases v with ⟨k,l⟩
  by_cases hi : i = k
  · subst k
    simp only [changeBasis, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ite_true, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    have hz : ∀ j : Fin (n i), (j.val = 0) ↔ j = ⟨0, hn i⟩ := by
      intro j; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp only [hz]
    simp
  · have he : ∀ j : Fin (n i), (⟨i,j⟩ : Vertex n) ≠ ⟨k,l⟩ := by
      intro j h; exact hi (congrArg Sigma.fst h)
    simp [changeBasis, hi, he]

private theorem changeBasis_action (hn : ∀ i, 0 < n i) (f : Vertex n → ℝ)
    (u : Vertex n) :
    (changeBasis n *ᵥ f) u = f u + f (first n hn u.1) -
      (if u.2.val = 0 then ∑ j : Fin (n u.1), f ⟨u.1,j⟩ else 0) := by
  simp only [mulVec, dotProduct, changeBasis, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  have hfirst : (∑ v : Vertex n,
      if u.1 = v.1 then if v.2.val = 0 then f v else 0 else 0) =
      f (first n hn u.1) := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_eq_single u.1 (by intro i _ hi; simp [hi.symm]) (by simp)]
    have hz : ∀ j : Fin (n u.1), (j.val = 0) ↔ j = ⟨0, hn u.1⟩ := by
      intro j; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp [hz, first]
  have hlast : (∑ v : Vertex n,
      if u.1 = v.1 then if u.2.val = 0 then f v else 0 else 0) =
      if u.2.val = 0 then ∑ j : Fin (n u.1), f ⟨u.1,j⟩ else 0 := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_eq_single u.1 (by intro i _ hi; simp [hi.symm]) (by simp)]
    simp
  rw [hfirst, hlast]
  simp

private theorem changeBasis_unit (hn : ∀ i, 0 < n i) : IsUnit (changeBasis n) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  apply (changeBasis n).mulVecLin.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro f hf
  change changeBasis n *ᵥ f = 0 at hf
  have hs (i : Fin t) : (n i : ℝ) * f (first n hn i) = 0 := by
    have h := congrArg (fun g : Vertex n → ℝ => ∑ j : Fin (n i), g ⟨i,j⟩) hf
    simp only [mulVec, dotProduct, Pi.zero_apply, Finset.sum_const_zero] at h
    rw [Finset.sum_comm] at h
    simp_rw [← Finset.sum_mul, changeBasis_sum n hn] at h
    rw [Fintype.sum_sigma] at h
    have hz : ∀ j : Fin (n i), (j.val = 0) ↔ j = ⟨0, hn i⟩ := by
      intro j; exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp only [ite_mul, zero_mul] at h
    simpa [hz, first] using h
  have hz (i : Fin t) : f (first n hn i) = 0 :=
    (mul_eq_zero.mp (hs i)).resolve_left (by exact_mod_cast (hn i).ne')
  have hsum (i : Fin t) : (∑ j : Fin (n i), f ⟨i,j⟩) = 0 := by
    have h := congrFun hf (first n hn i)
    rw [changeBasis_action n hn] at h
    change f (first n hn i) + f (first n hn i) -
      (if (0 : ℕ) = 0 then ∑ j : Fin (n i), f ⟨i,j⟩ else 0) = 0 at h
    simpa only [hz, zero_add, ite_true, zero_sub, neg_eq_zero] using h
  change f = 0
  funext u
  have h := congrFun hf u
  rw [changeBasis_action n hn, hz, hsum] at h
  simpa using h

private theorem a_diagonalization (hn : ∀ i, 0 < n i) :
    A n * changeBasis n = changeBasis n * diagonal (diagonalValues n) := by
  ext u v
  change (A n *ᵥ fun x => changeBasis n x v) u = _
  rw [a_action, changeBasis_sum n hn, Matrix.mul_diagonal]
  have hd := d_ne_zero n hn v.1
  by_cases hi : u.1 = v.1
  · by_cases hv : v.2.val = 0
    · have he : (u = v) ↔ u.2.val = 0 := by
        rcases u with ⟨i,j⟩; rcases v with ⟨k,l⟩
        dsimp at hi hv ⊢; subst k
        simp [Fin.ext_iff, hv]
      simp only [changeBasis, hi, ite_true, hv, he, diagonalValues]
      split_ifs <;> (dsimp [d] at *; field_simp; ring)
    · simp [changeBasis, hi, hv, diagonalValues, div_eq_mul_inv]
  · have huv : u ≠ v := fun h => hi (congrArg Sigma.fst h)
    simp [changeBasis, hi, huv]

private theorem a_roots (hn : ∀ i, 0 < n i) :
    (A n).charpoly.roots = Finset.univ.val.map (diagonalValues n) := by
  have hunit : IsUnit (changeBasis n).det := (changeBasis_unit n hn).map Matrix.detMonoidHom
  have hsim : A n = changeBasis n * diagonal (diagonalValues n) * (changeBasis n)⁻¹ := by
    rw [← a_diagonalization n hn, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  rw [hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul,
    Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private theorem diagonal_negative (hn : ∀ i, 0 < n i) (u : Vertex n) :
    diagonalValues n u < 0 ↔ u.2.val = 0 ∧ 2 ≤ n u.1 := by
  by_cases hu : u.2.val = 0
  · simp only [diagonalValues, hu, ite_true, true_and]
    by_cases hi : n u.1 = 1
    · norm_num [d, hi]
    · have htwo : 2 ≤ n u.1 := by have := hn u.1; omega
      have hd : 0 < d n u.1 := by
        have hr : (2 : ℝ) ≤ n u.1 := by exact_mod_cast htwo
        dsimp [d]; linarith
      exact iff_of_true (div_neg_of_neg_of_pos (by norm_num) hd) htwo
  · norm_num [diagonalValues, hu]

private theorem a_negative_count (hn : ∀ i, 0 < n i) :
    RHLinalg.negIndex (a_hermitian n) =
      (Finset.univ.filter fun i => 2 ≤ n i).card := by
  have hr : (A n).charpoly.roots.countP (fun x => x < 0) =
      RHLinalg.negIndex (a_hermitian n) := by
    rw [(a_hermitian n).roots_charpoly_eq_eigenvalues, Multiset.countP_map]
    rfl
  rw [← hr, a_roots n hn, Multiset.countP_map]
  change (Finset.univ.filter fun u : Vertex n => diagonalValues n u < 0).card = _
  apply Finset.card_bij (fun u _ => u.1)
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((diagonal_negative n hn u).mp (Finset.mem_filter.mp hu).2).2⟩
  · intro u hu v hv h
    have hu0 := ((diagonal_negative n hn u).mp (Finset.mem_filter.mp hu).2).1
    have hv0 := ((diagonal_negative n hn v).mp (Finset.mem_filter.mp hv).2).1
    rcases u with ⟨i,j⟩; rcases v with ⟨k,l⟩
    dsimp at h hu0 hv0; subst k
    congr 1
    exact Fin.ext (hu0.trans hv0.symm)
  · intro i hi
    refine ⟨first n hn i, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (diagonal_negative n hn _).mpr ⟨rfl, (Finset.mem_filter.mp hi).2⟩⟩

private theorem a_positive_count (hn : ∀ i, 0 < n i) :
    RHLinalg.posIndex (a_hermitian n) =
      (∑ i, n i) - (Finset.univ.filter fun i => 2 ≤ n i).card := by
  have hpart := D5.S3.SpectralTopology.PointGapExactInertia.posIndex_add_negIndex_eq_rank
    (a_hermitian n)
  have hdet : (A n).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse (B := -blockBase n)
    rw [A, neg_mul_neg, inverse_mul_base n hn]
  have hfull : (A n).rank = Fintype.card (Vertex n) :=
    Matrix.rank_of_det_ne_zero hdet
  rw [hfull, a_negative_count n hn] at hpart
  have hc : Fintype.card (Vertex n) = ∑ i, n i := by simp [Vertex]
  rw [hc] at hpart
  omega

private abbrev SingletonPart := {i : Fin t // n i = 1}

private def singletonLift : (SingletonPart n → ℝ) →ₗ[ℝ] (Vertex n → ℝ) where
  toFun f u := if h : n u.1 = 1 then f ⟨u.1,h⟩ else 0
  map_add' f g := by ext u; dsimp; split_ifs <;> simp
  map_smul' c f := by ext u; dsimp; split_ifs <;> simp

private def singletonSum : (SingletonPart n → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ i, f i
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

private theorem singletonLift_injective (hn : ∀ i, 0 < n i) :
    Function.Injective (singletonLift n) := by
  intro f g h
  funext i
  have he := congrFun h (first n hn i.1)
  simpa [singletonLift, first, i.2] using he

private theorem singletonLift_sum (f : SingletonPart n → ℝ) :
    (∑ u : Vertex n, singletonLift n f u) = ∑ i, f i := by
  rw [Fintype.sum_sigma]
  simp only [singletonLift, LinearMap.coe_mk, AddHom.coe_mk]
  have he (i : Fin t) : (∑ j : Fin (n i),
      if h : n i = 1 then f ⟨i,h⟩ else 0) = if h : n i = 1 then f ⟨i,h⟩ else 0 := by
    by_cases h : n i = 1 <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  let e : {i : Fin t // i ∈ Finset.univ.filter (fun i => n i = 1)} ≃ SingletonPart n :=
    Equiv.subtypeEquivRight (by intro i; simp)
  exact e.sum_comp f

private theorem quarter_count_lower (hn : ∀ i, 0 < n i) (hs : (delta n).det = 0) :
    (∑ i, n i) - t ≤ (sourceL n).charpoly.roots.count (1 / 4 : ℝ) := by
  have he : deviationSpace n ≤ Module.End.eigenspace (sourceL n).mulVecLin (1 / 4 : ℝ) := by
    intro w hw
    rw [Module.End.mem_eigenspace_iff]
    have hw' : partSum n w = 0 := hw
    exact deviation_action n hn (singular_ratio n hn hs) w (fun i => congrFun hw' i)
  have hdim := (Submodule.finrank_mono he).trans
    (LinearMap.finrank_eigenspace_le (sourceL n).mulVecLin (1 / 4 : ℝ))
  rw [deviation_dimension n hn, Matrix.charpoly_mulVecLin, ← Polynomial.count_roots] at hdim
  exact hdim

private theorem one_count_lower (hn : ∀ i, 0 < n i) (hs : (delta n).det = 0) :
    (Finset.univ.filter (fun i => n i = 1)).card - 1 ≤
      (sourceL n).charpoly.roots.count 1 := by
  let K := LinearMap.ker (singletonSum n)
  let F : K →ₗ[ℝ] Module.End.eigenspace (sourceL n).mulVecLin 1 :=
    { toFun := fun f => ⟨singletonLift n f, by
        rw [Module.End.mem_eigenspace_iff]
        simp only [one_smul]
        apply singleton_action n hn (singular_ratio n hn hs)
        · intro i hi j; simp [singletonLift, hi]
        · rw [singletonLift_sum]
          exact f.2⟩
      map_add' := fun f g => by apply Subtype.ext; exact (singletonLift n).map_add f g
      map_smul' := fun c f => by apply Subtype.ext; exact (singletonLift n).map_smul c f }
  have hinj : Function.Injective F := by
    intro f g h
    apply Subtype.ext
    exact singletonLift_injective n hn (congrArg Subtype.val h)
  have hdim := (LinearMap.finrank_le_finrank_of_injective hinj).trans
    (LinearMap.finrank_eigenspace_le (sourceL n).mulVecLin 1)
  rw [Matrix.charpoly_mulVecLin, ← Polynomial.count_roots] at hdim
  have hrank := (singletonSum n).finrank_range_add_finrank_ker
  have hle : Module.finrank ℝ (LinearMap.range (singletonSum n)) ≤ 1 := by
    simpa using (Submodule.finrank_le (LinearMap.range (singletonSum n)))
  have hc : Module.finrank ℝ (SingletonPart n → ℝ) =
      (Finset.univ.filter fun i => n i = 1).card := by
    simp [SingletonPart, Fintype.card_subtype]
  rw [hc] at hrank
  dsimp only [K] at hdim
  omega

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

/-- Both complete singular spectral clauses on the original source domain. -/
theorem result : completeConjecture := by
  intro t n ht hn hcof hs
  obtain ⟨hA,hL,hplus,hminus,hzero,hquarter,hone,hdim⟩ :=
    singular_source_reduction n hn hs
  have hneg : RHLinalg.negIndex hL = (Finset.univ.filter fun i => 2 ≤ n i).card := by
    rw [hminus]
    exact a_negative_count n hn
  have hpos : RHLinalg.posIndex hL =
      (∑ i, n i) - (Finset.univ.filter fun i => 2 ≤ n i).card - 1 := by
    have hp := a_positive_count n hn
    have he : RHLinalg.posIndex hA = RHLinalg.posIndex (a_hermitian n) := rfl
    rw [he, hp] at hplus
    omega
  have hsize : t ≤ ∑ i, n i := by
    have h := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin t => 1)
      (g := n) (fun i _ => hn i)
    simpa using h
  have hparts : (Finset.univ.filter (fun i => n i = 1)).card +
      (Finset.univ.filter (fun i => 2 ≤ n i)).card = t := by
    have he : Finset.univ.filter (fun i => ¬ n i = 1) =
        Finset.univ.filter (fun i => 2 ≤ n i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hn i
      omega
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i => n i = 1)
    rw [he] at hc
    simpa using hc
  have hex : ∃ i, n i = 1 := by
    by_contra! hall
    have hr : 0 ≤ ratio n := by
      apply Finset.sum_nonneg
      intro i _
      have htwo : 2 ≤ n i := by have := hn i; have := hall i; omega
      have hd : 0 < d n i := by
        have hh : (2 : ℝ) ≤ n i := by exact_mod_cast htwo
        dsimp [d]; linarith
      exact div_nonneg (Nat.cast_nonneg _) hd.le
    rw [singular_ratio n hn hs] at hr
    norm_num at hr
  have hh : 0 < (Finset.univ.filter (fun i => n i = 1)).card := by
    obtain ⟨i,hi⟩ := hex
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  let roots := (sourceL n).charpoly.roots.filter (fun x => 0 < x)
  let target := Multiset.replicate ((∑ i, n i) - t) (1 / 4 : ℝ) +
    Multiset.replicate ((Finset.univ.filter (fun i => n i = 1)).card - 1) (1 : ℝ)
  have hle : target ≤ roots := by
    apply Multiset.le_iff_count.mpr
    intro x
    by_cases hx : x = (1 / 4 : ℝ)
    · subst x
      simpa only [target, roots, Multiset.count_add, Multiset.count_replicate,
        Multiset.count_filter, show (0 : ℝ) < 1 / 4 by norm_num,
        show ¬(1 : ℝ) = 1 / 4 by norm_num, ite_true, ite_false, add_zero]
        using quarter_count_lower n hn hs
    · by_cases hx1 : x = (1 : ℝ)
      · subst x
        simpa only [target, roots, Multiset.count_add, Multiset.count_replicate,
          Multiset.count_filter, show (0 : ℝ) < 1 by norm_num,
          show ¬(1 / 4 : ℝ) = 1 by norm_num, ite_true, ite_false, zero_add]
          using one_count_lower n hn hs
      · simp only [target, Multiset.count_add, Multiset.count_replicate,
          if_neg (Ne.symm hx), if_neg (Ne.symm hx1), zero_add]
        exact Nat.zero_le _
  have hcard : roots.card = RHLinalg.posIndex hL := by
    dsimp [roots]
    rw [hL.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
    rfl
  have hcardtarget : target.card = RHLinalg.posIndex hL := by
    simp only [target, Multiset.card_add, Multiset.card_replicate]
    rw [hpos]
    omega
  refine ⟨hL, ?_, hpos, hzero, hneg⟩
  exact (Multiset.eq_of_le_of_card_le hle (by omega)).symm

#print axioms result

#print axioms singular_source_downdate
#print axioms singular_source_reduction

end D5.S3.Combinatorics.SpectralGraph.DasMohantySingularSquaredDistance
