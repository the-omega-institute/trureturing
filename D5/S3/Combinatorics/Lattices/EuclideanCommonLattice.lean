/- GID: D5/S3/Combinatorics/Lattices/EuclideanCommonLattice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/EuclideanCommonLattice
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral Euclidean HN flags yield the common-lattice frame slope bound. -/
import D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism
import D5.S3.Combinatorics.Lattices.HarderNarasimhanTruncation
/-! Integral HN flags, frame rank coverage and spectral slope deficits. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace D5.S3.Combinatorics.Lattices.EuclideanCommonLattice
open Module Finset EuclideanSublattices EuclideanHarderNarasimhan HarderNarasimhan
open HarderNarasimhanTruncation EuclideanSlopeMorphism
open scoped InnerProductSpace
open LinearMap MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
private lemma hs2_eq_sum {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    hs2 A = ∑ j, ‖A (b j)‖ ^ 2 := by
  rw [hs2, LinearMap.trace_eq_sum_inner _ b]
  congr 1
  funext j
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
private lemma hs2_nonneg (A : E →ₗ[ℝ] F) : 0 ≤ hs2 A := by
  rw [hs2_eq_sum A (stdOrthonormalBasis ℝ E)]; exact sum_nonneg fun j _ => sq_nonneg _
private lemma hs2_adjoint (A : E →ₗ[ℝ] F) : hs2 A.adjoint = hs2 A := by
  simp only [hs2, LinearMap.adjoint_adjoint]
  rw [LinearMap.trace_comp_comm']
private lemma orthonormal_sum_le {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℝ] F) {v : ι → E} (hv : Orthonormal ℝ v) :
    ∑ j, ‖A (v j)‖ ^ 2 ≤ hs2 A := by
  classical
  let b := stdOrthonormalBasis ℝ F
  calc
    ∑ j, ‖A (v j)‖ ^ 2 = ∑ j, ∑ k, ‖⟪b k, A (v j)⟫_ℝ‖ ^ 2 := by
      simp_rw [b.sum_sq_norm_inner_right]
    _ = ∑ k, ∑ j, ‖⟪v j, A.adjoint (b k)⟫_ℝ‖ ^ 2 := by
      rw [sum_comm]
      apply sum_congr rfl; intro k _
      apply sum_congr rfl; intro j _
      rw [← LinearMap.adjoint_inner_left, norm_inner_symm]
    _ ≤ ∑ k, ‖A.adjoint (b k)‖ ^ 2 := by
      apply sum_le_sum; intro k _
      simpa using hv.sum_inner_products_le (A.adjoint (b k)) (s := univ)
    _ = hs2 A.adjoint := (hs2_eq_sum _ b).symm
    _ = hs2 A := hs2_adjoint A
private lemma abs_partial_trace_le {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℝ] E) {v : ι → E} (hv : Orthonormal ℝ v) :
    |∑ j, (⟪v j, A (v j)⟫_ℝ)| ≤
      Real.sqrt (Fintype.card ι) * Real.sqrt (hs2 A) := by
  classical
  calc
    |∑ j, (⟪v j, A (v j)⟫_ℝ)| ≤ ∑ j, |(⟪v j, A (v j)⟫_ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖A (v j)‖ := by
      apply sum_le_sum; intro j _
      calc
        |⟪v j, A (v j)⟫_ℝ| ≤ ‖v j‖ * ‖A (v j)‖ := abs_real_inner_le_norm _ _
        _ = ‖A (v j)‖ := by rw [hv.norm_eq_one j, one_mul]
    _ ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ j, ‖A (v j)‖ ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ : ι => (1 : ℝ))
        (fun j => ‖A (v j)‖)
    _ ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (hs2 A) := by
      gcongr
      exact orthonormal_sum_le A hv
/-- Weighted source Gram operator. -/
def gram (c : ℝ) (A : E →ₗ[ℝ] F) : E →ₗ[ℝ] E :=
  (c : ℝ) • (A.adjoint ∘ₗ A)
private lemma gram_partial_trace {ι : Type*} [Fintype ι]
    (c : ℝ) (A : E →ₗ[ℝ] F) {v : ι → E} (hv : Orthonormal ℝ v) :
    |c * ∑ j, ‖A (v j)‖ ^ 2 - Fintype.card ι| ≤
      Real.sqrt (Fintype.card ι) * Real.sqrt (hs2 (gram c A - LinearMap.id)) := by
  have h := abs_partial_trace_le (gram c A - LinearMap.id) hv
  have hself (j : ι) : ⟪v j, v j⟫_ℝ = 1 := by
    simp [real_inner_self_eq_norm_sq, hv.norm_eq_one j]
  have hterm (j : ι) :
      (⟪v j, (gram c A - LinearMap.id : E →ₗ[ℝ] E) (v j)⟫_ℝ) =
        c * ‖A (v j)‖ ^ 2 - 1 := by
    simp only [gram, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply, inner_sub_right, inner_smul_right, hself,
      LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
      mul_one]
  simpa only [hterm, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
    nsmul_eq_mul, mul_one] using h
private lemma orthogonal_image_energy {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℝ] F) (N : Submodule ℝ E) {v : ι → F} (hv : Orthonormal ℝ v)
    (hzero : ∀ j x, x ∈ N → ⟪A x, v j⟫_ℝ = 0) :
    ∑ j, ‖A.adjoint (v j)‖ ^ 2 ≤
      ∑ k, ‖A ((stdOrthonormalBasis ℝ Nᗮ k : Nᗮ) : E)‖ ^ 2 := by
  classical
  let b := stdOrthonormalBasis ℝ Nᗮ
  have hmem (j : ι) : A.adjoint (v j) ∈ Nᗮ := by
    apply (N.mem_orthogonal _).mpr
    intro x hx
    rw [LinearMap.adjoint_inner_right]; exact hzero j x hx
  have hparseval (j : ι) :
      ‖A.adjoint (v j)‖ ^ 2 =
        ∑ k, ‖⟪((b k : Nᗮ) : E), A.adjoint (v j)⟫_ℝ‖ ^ 2 := by
    exact (b.sum_sq_norm_inner_right ⟨A.adjoint (v j), hmem j⟩).symm
  calc
    ∑ j, ‖A.adjoint (v j)‖ ^ 2 =
        ∑ j, ∑ k, ‖⟪((b k : Nᗮ) : E), A.adjoint (v j)⟫_ℝ‖ ^ 2 := by
      simp_rw [hparseval]
    _ = ∑ k, ∑ j, ‖⟪v j, A ((b k : Nᗮ) : E)⟫_ℝ‖ ^ 2 := by
      rw [sum_comm]
      apply sum_congr rfl; intro k _
      apply sum_congr rfl; intro j _
      rw [LinearMap.adjoint_inner_right, norm_inner_symm]
    _ ≤ ∑ k, ‖A ((b k : Nᗮ) : E)‖ ^ 2 := by
      apply sum_le_sum; intro k _
      simpa using hv.sum_inner_products_le (A ((b k : Nᗮ) : E)) (s := univ)
section Family
variable {I : Type*} [Fintype I] {V : I → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
  [∀ i, FiniteDimensional ℝ (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]
/-- The weighted frame operator on the common target. -/
def frame (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H) : H →ₗ[ℝ] H :=
  ∑ i, (c i : ℝ) • (A i ∘ₗ (A i).adjoint)
private lemma frame_inner (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H) (x : H) :
    (⟪x, frame c A x⟫_ℝ) = ∑ i, c i * ‖(A i).adjoint x‖ ^ 2 := by
  simp only [frame, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum, inner_smul_right]
  apply sum_congr rfl; intro i _
  rw [← LinearMap.adjoint_inner_left (A i) ((A i).adjoint x) x,
    real_inner_self_eq_norm_sq]
private lemma frame_symmetric (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H) :
    (frame c A).IsSymmetric := by
  unfold frame
  exact LinearMap.isSymmetric_sum univ fun i _ =>
    (LinearMap.isSymmetric_self_comp_adjoint (A i)).smul (by simp)
private lemma frame_trace (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H) :
    (LinearMap.trace ℝ H (frame c A)) =
      ∑ i, c i * ∑ k, ‖A i (stdOrthonormalBasis ℝ (V i) k)‖ ^ 2 := by
  classical
  simp only [frame, map_sum, map_smul]
  apply sum_congr rfl; intro i _
  simp only [smul_eq_mul]
  have h : (LinearMap.trace ℝ H (A i ∘ₗ (A i).adjoint)) = hs2 (A i) := by
    rw [hs2, LinearMap.trace_comp_comm']
  rw [h, hs2_eq_sum (A i) (stdOrthonormalBasis ℝ (V i))]
private lemma frame_trace_lower (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H)
    (e : ℝ) (hR : 0 < ∑ i, (finrank ℝ (V i) : ℝ)) (he : 0 ≤ e)
    (hK : ∑ i, hs2 (gram (c i) (A i) - LinearMap.id) ≤
      e * ∑ i, (finrank ℝ (V i) : ℝ)) :
    (∑ i, (finrank ℝ (V i) : ℝ)) * (1 - Real.sqrt e) ≤
      LinearMap.trace ℝ H (frame c A) := by
  classical
  let R := ∑ i, (finrank ℝ (V i) : ℝ)
  let E : I → ℝ := fun i => hs2 (gram (c i) (A i) - LinearMap.id)
  have hfull (i : I) : (finrank ℝ (V i) : ℝ) -
      Real.sqrt (finrank ℝ (V i)) * Real.sqrt (E i) ≤
        c i * ∑ k, ‖A i (stdOrthonormalBasis ℝ (V i) k)‖ ^ 2 := by
    have h := gram_partial_trace (c i) (A i) (stdOrthonormalBasis ℝ (V i)).orthonormal
    simp only [Fintype.card_fin] at h
    linarith [(abs_le.mp h).1]
  have hcs : ∑ i, Real.sqrt (finrank ℝ (V i)) * Real.sqrt (E i) ≤
      R * Real.sqrt e := calc
    _ ≤ Real.sqrt R * Real.sqrt (∑ i, E i) :=
      Real.sum_sqrt_mul_sqrt_le univ (fun _ => Nat.cast_nonneg _) (fun _ => hs2_nonneg _)
    _ ≤ Real.sqrt R * Real.sqrt (e * R) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _)
    _ = R * Real.sqrt e := by
      rw [Real.sqrt_mul he]
      calc
        _ = (Real.sqrt R * Real.sqrt R) * Real.sqrt e := by ring
        _ = _ := by rw [Real.mul_self_sqrt hR.le]
  rw [frame_trace]
  have hf := sum_le_sum fun i (_ : i ∈ univ) => hfull i
  rw [sum_sub_distrib] at hf
  dsimp [R] at hcs; linarith
private lemma abstract_rank_estimate (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H)
    (N : ∀ i, Submodule ℝ (V i)) (e η ρ : ℝ)
    (hR : 0 < ∑ i, (finrank ℝ (V i) : ℝ)) (he : 0 ≤ e) (he1 : e < 1)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hK : ∑ i, hs2 (gram (c i) (A i) - LinearMap.id) ≤
      e * ∑ i, (finrank ℝ (V i) : ℝ))
    (hQ : (LinearMap.trace ℝ H (frame c A ∘ₗ frame c A)) ≤
      (1 + η) * (LinearMap.trace ℝ H (frame c A)) ^ 2 / finrank ℝ H)
    (hN : ∑ i, (finrank ℝ (N i)ᗮ : ℝ) ≤ ρ * ∑ i, (finrank ℝ (V i) : ℝ))
    (he4 : e ≤ 1 / 4) :
    (finrank ℝ (⨆ i, (N i).map (A i))ᗮ : ℝ) ≤
      (η + 4 * ρ + 4 * Real.sqrt e) * finrank ℝ H := by
  classical
  let S : Submodule ℝ H := (⨆ i, (N i).map (A i))ᗮ
  change (finrank ℝ S : ℝ) ≤ _
  by_cases hDzero : finrank ℝ H = 0
  · have hSz : finrank ℝ S = 0 := by
      have := S.finrank_le
      omega
    simp [hSz, hDzero]
  have hD : 0 < (finrank ℝ H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hDzero
  let R := ∑ i, (finrank ℝ (V i) : ℝ)
  let E : I → ℝ := fun i => hs2 (gram (c i) (A i) - LinearMap.id)
  have hEn (i : I) : 0 ≤ E i := hs2_nonneg _
  have hCS (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) {b : ℝ} (hb : 0 ≤ b)
      (hfB : ∑ i, f i ≤ b * R) :
      ∑ i, Real.sqrt (f i) * Real.sqrt (E i) ≤ R * Real.sqrt (b * e) := by
    calc
      _ ≤ Real.sqrt (∑ i, f i) * Real.sqrt (∑ i, E i) :=
        Real.sum_sqrt_mul_sqrt_le univ hf hEn
      _ ≤ Real.sqrt (b * R) * Real.sqrt (e * R) := by
        exact mul_le_mul (Real.sqrt_le_sqrt hfB) (Real.sqrt_le_sqrt hK)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = R * Real.sqrt (b * e) := by
        rw [← Real.sqrt_mul (mul_nonneg hb hR.le)]
        rw [show b * R * (e * R) = b * e * R ^ 2 by ring,
          Real.sqrt_mul (mul_nonneg hb he), Real.sqrt_sq hR.le]
        ring
  have ht : R * (1 - Real.sqrt e) ≤ LinearMap.trace ℝ H (frame c A) :=
    frame_trace_lower c A e hR he hK
  let b := stdOrthonormalBasis ℝ S
  let v : Fin (finrank ℝ S) → H := fun j => (b j : H)
  have hv : Orthonormal ℝ v := b.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  let z := ∑ j, (⟪v j, frame c A (v j)⟫_ℝ)
  have hz : z = ∑ i, c i * ∑ j, ‖(A i).adjoint (v j)‖ ^ 2 := by
    dsimp [z]
    simp_rw [frame_inner, Finset.mul_sum]
    exact sum_comm
  have hi (i : I) : c i * ∑ j, ‖(A i).adjoint (v j)‖ ^ 2 ≤
      (finrank ℝ (N i)ᗮ : ℝ) +
        Real.sqrt (finrank ℝ (N i)ᗮ) * Real.sqrt (E i) := by
    by_cases hci : 0 ≤ c i
    swap
    · have hz0 : c i * ∑ j, ‖(A i).adjoint (v j)‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hci)
          (sum_nonneg fun _ _ => sq_nonneg _)
      exact hz0.trans (by positivity)
    have hn : ∀ j x, x ∈ N i → ⟪A i x, v j⟫_ℝ = 0 := by
      intro j x hx; exact (Submodule.mem_orthogonal _ _).mp (b j).property _
        (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hx))
    have henergy := mul_le_mul_of_nonneg_left (orthogonal_image_energy (A i) (N i) hv hn)
      hci
    have hon := (stdOrthonormalBasis ℝ (N i)ᗮ).orthonormal.comp_linearIsometry
      (N i)ᗮ.subtypeₗᵢ
    have htrace := gram_partial_trace (c i) (A i) hon
    simp only [Fintype.card_fin] at htrace
    have hupper := (abs_le.mp htrace).2
    change c i * ∑ k, ‖A i ((stdOrthonormalBasis ℝ (N i)ᗮ k : (N i)ᗮ) : V i)‖ ^ 2 -
      (finrank ℝ (N i)ᗮ : ℝ) ≤ Real.sqrt (finrank ℝ (N i)ᗮ) * Real.sqrt (E i) at hupper
    linarith
  have hup : z ≤ R * (ρ + Real.sqrt (ρ * e)) := by
    rw [hz]
    have hsum := sum_le_sum fun i (_ : i ∈ univ) => hi i
    rw [sum_add_distrib] at hsum
    have hcs := hCS (fun i => (finrank ℝ (N i)ᗮ : ℝ))
      (fun _ => Nat.cast_nonneg _) hρ hN
    dsimp [R] at *; linarith
  let t := (LinearMap.trace ℝ H (frame c A))
  let a : H →ₗ[ℝ] H := frame c A - ((t / (finrank ℝ H : ℝ) : ℝ) : ℝ) • LinearMap.id
  have hlow : t / finrank ℝ H * finrank ℝ S -
      Real.sqrt (finrank ℝ S) * Real.sqrt (hs2 a) ≤ z := by
    have h := abs_partial_trace_le a hv
    have hself (j : Fin (finrank ℝ S)) : ⟪v j, v j⟫_ℝ = 1 := by
      simp [real_inner_self_eq_norm_sq, hv.norm_eq_one j]
    have hsum : ∑ j, (⟪v j, a (v j)⟫_ℝ) = z - t / finrank ℝ H * finrank ℝ S := by
      simp only [a, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        inner_sub_right, inner_smul_right, hself, mul_one, sum_sub_distrib, sum_const,
        card_univ, Fintype.card_fin,
        nsmul_eq_mul, z]
      ring
    rw [hsum] at h; simp only [Fintype.card_fin] at h; linarith [(abs_le.mp h).1]
  have hvar : hs2 a ≤ η * t ^ 2 / finrank ℝ H := by
    change hs2 (frame c A - ((t / (finrank ℝ H : ℝ) : ℝ) : ℝ) • LinearMap.id) ≤ _
    rw [variance_eq (frame c A) (frame_symmetric c A)]
    dsimp [t]; ring_nf at hQ ⊢; linarith
  exact scalar_rank_estimate _ R _ e η ρ t (hs2 a) z hD hR
    (by exact_mod_cast S.finrank_le) hρ ht (hs2_nonneg _) hvar hlow hup he4
end Family
/-- Rank coverage after deleting source subspaces with bounded total codimension. -/
private theorem rank_coverage {I : Type*} [Fintype I] {V : I → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H) (N : ∀ i, Submodule ℝ (V i))
    (e η ρ : ℝ) (hR : 0 < ∑ i, (finrank ℝ (V i) : ℝ))
    (he : 0 ≤ e) (he1 : e < 1) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hK : ∑ i, hs2 (gram (c i) (A i) - LinearMap.id) ≤
      e * ∑ i, (finrank ℝ (V i) : ℝ))
    (hQ : LinearMap.trace ℝ H (frame c A ∘ₗ frame c A) ≤
      (1 + η) * (LinearMap.trace ℝ H (frame c A)) ^ 2 / finrank ℝ H)
    (hN : ∑ i, (finrank ℝ (N i)ᗮ : ℝ) ≤
      ρ * ∑ i, (finrank ℝ (V i) : ℝ)) :
    (finrank ℝ (⨆ i, (N i).map (A i))ᗮ : ℝ) ≤
      (η + 4 * ρ + 4 * Real.sqrt e) * finrank ℝ H := by
  by_cases he4 : e ≤ 1 / 4
  · exact abstract_rank_estimate c A N e η ρ hR he he1 hη hρ hK hQ hN he4
  have hcodim : (finrank ℝ (⨆ i, (N i).map (A i))ᗮ : ℝ) ≤ finrank ℝ H := by
    exact_mod_cast (Submodule.finrank_le (⨆ i, (N i).map (A i))ᗮ)
  have hse : 1 / 2 ≤ Real.sqrt e := Real.le_sqrt_of_sq_le (by linarith)
  have hlarge : 1 ≤ η + 4 * ρ + 4 * Real.sqrt e := by linarith
  exact hcodim.trans (by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg (finrank ℝ H)))
private lemma finite_bad_rank {J : Type*} [Fintype J] (x : J → ℝ)
    (s u t : ℝ) (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hav : (Fintype.card J : ℝ) * s ≤ ∑ j, x j) (hmax : ∀ j, x j ≤ s + u) :
    ((univ.filter fun j => x j < s - t).card : ℝ) ≤
      u / (u + t) * Fintype.card J := by
  classical
  let bad := univ.filter fun j => x j < s - t
  have hsum : ∑ j, (s + u - x j) ≤ u * Fintype.card J := by
    simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    nlinarith
  have hnonneg (j : J) : 0 ≤ s + u - x j := sub_nonneg.mpr (hmax j)
  have hb : (bad.card : ℝ) * (u + t) ≤ u * Fintype.card J := calc
    (bad.card : ℝ) * (u + t) = ∑ _j ∈ bad, (u + t) := by simp; ring
    _ ≤ ∑ j ∈ bad, (s + u - x j) := sum_le_sum fun j hj => by
      have := (mem_filter.mp hj).2
      linarith
    _ ≤ ∑ j, (s + u - x j) := sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) (fun j _ _ => hnonneg j)
    _ ≤ u * Fintype.card J := hsum
  by_cases hp : 0 < u + t
  · calc
      (bad.card : ℝ) ≤ (u * Fintype.card J) / (u + t) := (le_div_iff₀ hp).mpr hb
      _ = u / (u + t) * Fintype.card J := by ring
  · have hu0 : u = 0 := by linarith
    have ht0 : t = 0 := by linarith
    have hall (j : J) : x j = s := by
      have htot : ∑ j, x j = ∑ _j : J, s := by
        have hupper : ∑ j, x j ≤ ∑ _j : J, s :=
          sum_le_sum fun k _ => by simpa [hu0] using hmax k
        exact le_antisymm hupper (by
          simpa only [sum_const, card_univ, nsmul_eq_mul] using hav)
      exact ((sum_eq_sum_iff_of_le (fun k _ => by simpa [hu0] using hmax k)).mp
        htot) j (mem_univ j)
    simp [hall, hu0, ht0]
/-- Spectral flags with the exact source and target multiplicities and image placement.
For a padded target, the target flag is the inverse image under the coordinate projection. -/
structure SpectralFlags {I : Type*} [Fintype I] (V : I → Type*)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (A : ∀ i, V i →ₗ[ℝ] H)
    (J : I → Type*) [∀ i, Fintype (J i)] (K : Type*) [Fintype K]
    (x : ∀ i, J i → ℝ) (y : K → ℝ) (s Hmax : ℝ) where
  source : ℝ → ∀ i, Submodule ℝ (V i)
  target : ℝ → Submodule ℝ H
  source_dim : ∀ i, Fintype.card (J i) = finrank ℝ (V i)
  source_codim : ∀ t ∈ Set.Icc (0 : ℝ) Hmax, ∀ i,
    finrank ℝ (source t i)ᗮ = (univ.filter fun j => x i j < s - t).card
  target_codim : ∀ t ∈ Set.Icc (0 : ℝ) Hmax,
    finrank ℝ (target t)ᗮ = (univ.filter fun j => y j < s - t).card
  placement : ∀ t ∈ Set.Icc (0 : ℝ) Hmax, ∀ i, (source t i).map (A i) ≤ target t
/-- The frame slope estimate for finite spectra and compatible spectral flags.
The arithmetic construction of these flags is a separate hypothesis here. -/
theorem spectral_frame_slope {I : Type*} [Fintype I] {V : I → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {J : I → Type*} [∀ i, Fintype (J i)]
    {K : Type*} [Fintype K] (c : I → ℝ) (A : ∀ i, V i →ₗ[ℝ] H)
    (x : ∀ i, J i → ℝ) (y : K → ℝ) (s u Hmax e η : ℝ)
    (flags : SpectralFlags V H A J K x y s Hmax)
    (hR : 0 < ∑ i, (finrank ℝ (V i) : ℝ))
    (hH : 0 ≤ Hmax) (he1 : e < 1)
    (hK : 0 < Fintype.card K)
    (hav : (∑ i, (Fintype.card (J i) : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hmax : ∀ i j, x i j ≤ s + u) (hlow : ∀ j, s - Hmax ≤ y j)
    (hgram : ∑ i, hs2 (gram (c i) (A i) - LinearMap.id) ≤
      e * ∑ i, (finrank ℝ (V i) : ℝ))
    (hframe : LinearMap.trace ℝ H (frame c A ∘ₗ frame c A) ≤
      (1 + η) * (LinearMap.trace ℝ H (frame c A)) ^ 2 / finrank ℝ H) :
    (∑ j, max (s - y j) 0) ≤ finrank ℝ H *
      (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax) ∧
    s - (∑ j, y j) / Fintype.card K ≤ (finrank ℝ H : ℝ) / Fintype.card K *
      (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax) := by
  classical
  have hRs : 0 < ∑ i, (Fintype.card (J i) : ℝ) := by
    simpa only [flags.source_dim] using hR
  have hmaxsum : ∑ i, ∑ j, x i j ≤
      (∑ i, (Fintype.card (J i) : ℝ)) * (s + u) := by
    calc
      _ ≤ ∑ i, ∑ _j : J i, (s + u) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hmax i j
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, sum_mul]
  have hu : 0 ≤ u := nonneg_of_mul_nonneg_left (by nlinarith [hmaxsum]) hRs
  have he : 0 ≤ e := nonneg_of_mul_nonneg_left
    ((sum_nonneg fun i _ => hs2_nonneg (gram (c i) (A i) - LinearMap.id)).trans hgram) hR
  let T := LinearMap.trace ℝ H (frame c A)
  have hse : Real.sqrt e < 1 :=
    (Real.sqrt_lt he (by norm_num)).mpr (by simpa using he1)
  have hT : 0 < T := lt_of_lt_of_le
    (mul_pos hR (by linarith : 0 < 1 - Real.sqrt e))
    (frame_trace_lower c A e hR he hgram)
  have hD : 0 < finrank ℝ H := by
    by_contra hn
    have hz : finrank ℝ H = 0 := by omega
    letI : Subsingleton H := (Module.finrank_zero_iff (R := ℝ) (M := H)).mp hz
    have hzero : frame c A = 0 := Subsingleton.elim _ _
    have hTzero : T = 0 := by simp [T, hzero]
    linarith
  have hDr : (0 : ℝ) < finrank ℝ H := by exact_mod_cast hD
  have hvar : T ^ 2 / finrank ℝ H ≤
      LinearMap.trace ℝ H (frame c A ∘ₗ frame c A) := by
    have hv := hs2_nonneg (frame c A - (T / (finrank ℝ H : ℝ)) • LinearMap.id)
    rw [variance_eq (frame c A) (frame_symmetric c A)] at hv
    dsimp [T] at *; linarith
  have hη : 0 ≤ η := by
    have hv := (div_le_iff₀ hDr).mp hvar
    have hq := (le_div_iff₀ hDr).mp hframe
    have hp : 0 ≤ η * T ^ 2 := by dsimp [T] at *; nlinarith
    exact nonneg_of_mul_nonneg_left hp (sq_pos_of_pos hT)
  have hcount (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) Hmax) :
      ((univ.filter fun j => y j < s - t).card : ℝ) ≤
        (η + 4 * (u / (u + t)) + 4 * Real.sqrt e) * finrank ℝ H := by
    have hshare := finite_bad_rank (fun z : Sigma J => x z.1 z.2) s u t hu ht.1
      (by simpa only [Fintype.card_sigma, Nat.cast_sum, Fintype.sum_sigma] using hav)
      (fun z => hmax z.1 z.2)
    have hbad : ∑ i, (finrank ℝ (flags.source t i)ᗮ : ℝ) ≤
        u / (u + t) * ∑ i, (finrank ℝ (V i) : ℝ) := by
      simp_rw [flags.source_codim t ht]
      have hcard : ((univ.filter fun z : Sigma J => x z.1 z.2 < s - t).card : ℝ) =
          ∑ i, ((univ.filter fun j => x i j < s - t).card : ℝ) := by
        rw [← Finset.univ_sigma_univ, Finset.filter_sigma, Finset.card_sigma, Nat.cast_sum]
      rw [hcard, Fintype.card_sigma, Nat.cast_sum] at hshare
      simpa only [flags.source_dim] using hshare
    have hcover := rank_coverage c A (flags.source t) e η (u / (u + t)) hR
      he he1 hη (div_nonneg hu (add_nonneg hu ht.1)) hgram hframe hbad
    have hplace : (⨆ i, (flags.source t i).map (A i)) ≤ flags.target t :=
      iSup_le fun i => flags.placement t ht i
    have hmono := Submodule.finrank_mono (Submodule.orthogonal_le hplace)
    have hcount' : ((univ.filter fun j => y j < s - t).card : ℝ) ≤
        (η + 4 * (u / (u + t)) + 4 * Real.sqrt e) * finrank ℝ H := by
      rw [← flags.target_codim t ht]
      have hm : (finrank ℝ (flags.target t)ᗮ : ℝ) ≤
          finrank ℝ (⨆ i, (flags.source t i).map (A i))ᗮ := by exact_mod_cast hmono
      exact hm.trans hcover
    exact hcount'
  exact finite_spectral_deficit y s u Hmax e η (finrank ℝ H) hu hH hK hlow hcount
/-- The slope normalized by integral rank, with the zero-rank convention. -/
def latticeSlope (L : Submodule ℤ E) [DiscreteTopology L] : ℝ :=
  -Real.log (covolume L) / finrank ℤ L
private def span (L : Submodule ℤ E) (a : Sublattice L) : Submodule ℝ E :=
  Submodule.span ℝ (integral L a : Set E)
private theorem bot_carrier (L : Submodule ℤ E) : integral L ⊥ = ⊥ := by
  change
    (((Submodule.span ℝ (((⊥ : Submodule ℤ L).map L.subtype) : Set E)).restrictScalars
      ℤ).comap L.subtype).map L.subtype = ⊥
  simp
private theorem rank_le_ambient (L : Submodule ℤ E) [DiscreteTopology L] :
    finrank ℤ L ≤ finrank ℝ E := by
  rw [EuclideanHarderNarasimhan.integral_rank_eq]; exact Submodule.finrank_le _
private theorem full_rank (L : Submodule ℤ E) [DiscreteTopology L]
    (hL : Submodule.span ℝ (L : Set E) = ⊤) : finrank ℤ L = finrank ℝ E := by
  have hr := EuclideanHarderNarasimhan.integral_rank_eq L
  change finrank ℤ L = finrank ℝ (Submodule.span ℝ (L : Set E)) at hr
  exact hr.trans ((LinearEquiv.ofEq _ _ hL).finrank_eq.trans (by simp))
private theorem sum_get (l : List ℝ) : (∑ j : Fin l.length, l[j.1]) = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Fin.sum_univ_succ, ih]
private theorem filter_get (l : List ℝ) (p : ℝ → Prop) [DecidablePred p] :
    (univ.filter fun j : Fin l.length => p (l.get j)).card =
      (l.filter fun x => decide (p x)).length := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    change (∑ j : Fin (l.length + 1), if p ((a :: l).get j) then 1 else 0) = _
    rw [Fin.sum_univ_succ]
    change (if p a then 1 else 0) +
      (∑ j : Fin l.length, if p (l.get j) then 1 else 0) = _
    rw [ih]
    by_cases ha : p a <;> simp [ha, List.filter_cons, Nat.add_comm]
private structure Data (L : Submodule ℤ E) [DiscreteTopology L] where
  values : List ℝ
  length_eq : values.length = finrank ℤ L
  sum_eq : values.sum = -Real.log (covolume L)
  bounds : ∀ j : Fin values.length,
    (slopeData L).muMin ⊥ ⊤ ≤ values.get j ∧
      values.get j ≤ (slopeData L).muMax ⊥ ⊤
  cut : ∀ t : ℝ, ∃ a : Sublattice L,
    (⊥ < a → t ≤ (slopeData L).muMin ⊥ a) ∧
    (a < ⊤ → (slopeData L).muMax a ⊤ < t) ∧
    finrank ℝ (span L a)ᗮ = finrank ℝ E - finrank ℤ L +
      (univ.filter fun j : Fin values.length => values.get j < t).card
private def data (L : Submodule ℤ E) [DiscreteTopology L] : Data L := by
  classical
  let hex := (exists_unique_filtration (slopeData L) ⊥ ⊤).mpr bot_le
  let l := Classical.choose hex
  have hf : (slopeData L).Filtration ⊥ ⊤ l := (Classical.choose_spec hex).1
  have hd := hn_spectrum (slopeData L) (l := l) hf
  have hspanB : span L ⊥ = ⊥ := by
    change Submodule.span ℝ (integral L ⊥ : Set E) = ⊥
    rw [bot_carrier]
    simp
  have ht : ((slopeData L).rank ⊤ : ℝ) = finrank ℤ L := by
    change (finrank ℤ (⊤ : Submodule ℤ L) : ℝ) = _
    simp
  have hb : ((slopeData L).rank ⊥ : ℝ) = 0 := by
    rw [show ((slopeData L).rank ⊥ : ℝ) = finrank ℝ (span L ⊥) by
      change (finrank ℤ (⊥ : Sublattice L).val : ℝ) = _
      exact_mod_cast EuclideanSublattices.integral_rank_eq L (⊥ : Sublattice L).val]
    have he := (LinearEquiv.ofEq _ _ hspanB).finrank_eq
    exact_mod_cast he.trans (by simp)
  have hvol : covolume (⊥ : Submodule ℤ E) = 1 := by
    rw [covolume_eq_gram _ (Module.Basis.empty _ : Basis Empty ℤ (⊥ : Submodule ℤ E))]
    simp
  refine ⟨slopeList (slopeData L) ⊥ l, ?_, ?_, ?_, ?_⟩
  · have h := hd.1
    rw [ht, hb, sub_zero] at h
    exact_mod_cast h
  · have h := hd.2.1
    simpa only [slopeData, degree, integral_top, bot_carrier,
      hvol, Real.log_one, neg_zero, sub_zero] using h
  · intro j
    exact hd.2.2.1 _ (List.get_mem _ _)
  · intro t
    obtain ⟨a, p, q, hba, hat, hp, hq, hl, hmin, hmax, hcount⟩ := hd.2.2.2 t
    refine ⟨a, hmin, hmax, ?_⟩
    have ho := Submodule.finrank_add_finrank_orthogonal (span L a)
    have hoR : (finrank ℝ (span L a) : ℝ) + finrank ℝ (span L a)ᗮ = finrank ℝ E := by
      exact_mod_cast ho
    rw [ht, show ((slopeData L).rank a : ℝ) = finrank ℝ (span L a) by
      change (finrank ℤ a.val : ℝ) = _
      exact_mod_cast EuclideanSublattices.integral_rank_eq L a.val] at hcount
    calc
      finrank ℝ (span L a)ᗮ = finrank ℝ E - finrank ℤ L +
          ((slopeList (slopeData L) ⊥ l).filter (fun x => decide (x < t))).length := by
        have hk : ((finrank ℝ E - finrank ℤ L : ℕ) : ℝ) =
            (finrank ℝ E : ℝ) - finrank ℤ L :=
          Nat.cast_sub (rank_le_ambient L)
        exact_mod_cast (by nlinarith : (finrank ℝ (span L a)ᗮ : ℝ) =
          ((finrank ℝ E - finrank ℤ L : ℕ) : ℝ) +
          (((slopeList (slopeData L) ⊥ l).filter (fun x => decide (x < t))).length : ℝ))
      _ = _ := congrArg (fun n => finrank ℝ E - finrank ℤ L + n)
        (filter_get (slopeList (slopeData L) ⊥ l) (fun x => x < t)).symm
private theorem weighted_slope (L : Submodule ℤ E) [DiscreteTopology L] (d : Data L) :
    (finrank ℤ L : ℝ) * latticeSlope L = d.values.sum := by
  rw [d.sum_eq, latticeSlope]
  by_cases hn : finrank ℤ L = 0
  · have hl : d.values = [] := List.length_eq_zero_iff.mp (d.length_eq.trans hn)
    have hzero : -Real.log (covolume L) = 0 := by rw [← d.sum_eq, hl]; rfl
    simp [hn, hzero]
  · field_simp [Nat.cast_ne_zero.mpr hn]
private theorem mean_ge_min (L : Submodule ℤ E) [DiscreteTopology L] (d : Data L) :
    (slopeData L).muMin ⊥ ⊤ ≤ latticeSlope L := by
  classical
  by_cases hn : finrank ℤ L = 0
  · have hrank (a : Sublattice L) :
        (slopeData L).rank a = (finrank ℤ (integral L a) : ℤ) := by
      change (finrank ℤ a.val : ℤ) = _
      exact_mod_cast (Submodule.finrank_map_subtype_eq L a.val).symm
    have htN : finrank ℤ (integral L ⊤) = finrank ℤ L :=
      (LinearEquiv.ofEq _ _ (integral_top L)).finrank_eq
    have hbN : finrank ℤ (integral L ⊥) = 0 := by
      exact (LinearEquiv.ofEq _ _ (bot_carrier L)).finrank_eq.trans (by simp)
    have ht : (slopeData L).rank ⊤ = 0 := by
      rw [hrank]
      exact_mod_cast htN.trans hn
    have hb : (slopeData L).rank ⊥ = 0 := by
      rw [hrank]
      exact_mod_cast hbN
    have htb : (⊤ : Sublattice L) = ⊥ := by
      by_contra hne
      have hlt := (slopeData L).rank_strictMono (bot_lt_iff_ne_bot.mpr hne)
      rw [hb, ht] at hlt; exact (lt_irrefl (0 : ℤ)) hlt
    have hmin : (slopeData L).muMin ⊥ ⊤ = 0 := by
      rw [htb]; simp [SlopeData.muMin, Real.sInf_empty]
    rw [hmin]; simp only [latticeSlope, hn, Nat.cast_zero, div_zero, le_refl]
  · have hpos : (0 : ℝ) < finrank ℤ L := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hs : (∑ j : Fin d.values.length, d.values.get j) = d.values.sum := by
      simpa only [List.get_eq_getElem] using sum_get d.values
    have hb : (∑ _j : Fin d.values.length, (slopeData L).muMin ⊥ ⊤) ≤
        ∑ j : Fin d.values.length, d.values.get j :=
      Finset.sum_le_sum fun j _ => (d.bounds j).1
    rw [hs] at hb
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
    rw [d.length_eq, d.sum_eq] at hb
    rw [latticeSlope]; exact (le_div_iff₀ hpos).mpr (by nlinarith)
private theorem count_sum {J K : Type*} [Fintype J] [Fintype K]
    (x : J → ℝ) (y : K → ℝ) (t : ℝ) :
    (univ.filter fun j : J ⊕ K => Sum.elim x y j < t).card =
      (univ.filter fun j => x j < t).card + (univ.filter fun j => y j < t).card := by
  classical
  have hs : (univ.filter fun j : J ⊕ K => Sum.elim x y j < t) =
      (univ.filter fun j => x j < t).disjSum (univ.filter fun j => y j < t) := by
    ext j
    cases j <;> simp
  rw [hs, Finset.card_disjSum]
private theorem count_padded {J : Type*} [Fintype J] (y : J → ℝ)
    (k : ℕ) (s H t : ℝ) :
    (univ.filter fun j : J ⊕ Fin k => Sum.elim y (fun _ => s - H) j < s - t).card =
      (univ.filter fun j => y j < s - t).card + (if t < H then k else 0) := by
  classical
  rw [count_sum]
  congr 1
  by_cases ht : t < H
  · have hlt : s - H < s - t := by linarith
    simp [ht, hlt]
  · have hlt : ¬ s - H < s - t := by linarith
    simp [ht, hlt]
private theorem sum_padded {J : Type*} [Fintype J] (y : J → ℝ)
    (k : ℕ) (a : ℝ) :
    (∑ j : J ⊕ Fin k, Sum.elim y (fun _ => a) j) = ∑ j, y j + k * a := by
  simpa only [Sum.elim_inl, Sum.elim_inr, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul] using
      (Fintype.sum_sum_type (Sum.elim y (fun _ : Fin k => a)))
private theorem comap_codim {W : Type*} {H : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (P : H →ₗ[ℝ] W) (hP : Function.Surjective P) (U : Submodule ℝ W) :
    finrank ℝ (U.comap P)ᗮ = finrank ℝ Uᗮ := by
  let g := U.mkQ ∘ₗ P
  have hg : Function.Surjective g := U.mkQ_surjective.comp hP
  have hk : LinearMap.ker g = U.comap P := by ext x; simp [g]
  have hd := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hk] at hd
  have hq := U.finrank_quotient_add_finrank
  have ho := Submodule.finrank_add_finrank_orthogonal (U.comap P)
  have hw := Submodule.finrank_add_finrank_orthogonal U
  omega
/-- The common integral lattice frame slope bound, in invariant real operator coordinates.
The target map permits padding by arbitrary extra orthogonal coordinates. -/
theorem common_lattice_slope {I : Type*} [Fintype I] (V : I → Type*)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    {W : Type*} {H : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (N : ∀ i, Submodule ℤ (V i)) (C : Submodule ℤ W)
    [∀ i, DiscreteTopology (N i)] [DiscreteTopology C]
    (hN : ∀ i, Submodule.span ℝ (N i : Set (V i)) = ⊤)
    (B : ∀ i, V i →L[ℝ] W) (A : ∀ i, V i →ₗ[ℝ] H)
    (P : H →ₗ[ℝ] W) (hP : Function.Surjective P)
    (hPA : ∀ i, P ∘ₗ A i = (B i).toLinearMap)
    (hBC : ∀ i x, x ∈ N i → B i x ∈ C)
    (h : I → ℝ) (hB : ∀ i, B i ≠ 0 → Real.log ‖B i‖ ≤ h i)
    (c : I → ℝ) (s u Hmax e η : ℝ)
    (hR : 0 < ∑ i, (finrank ℝ (V i) : ℝ))
    (hH : 0 ≤ Hmax) (he1 : e < 1) (hd : 0 < finrank ℝ W)
    (hav : (∑ i, (finrank ℤ (N i) : ℝ)) * s ≤
      ∑ i, (finrank ℤ (N i) : ℝ) * (latticeSlope (N i) - h i))
    (hmax : ∀ i, 0 < finrank ℤ (N i) → (slopeData (N i)).muMax ⊥ ⊤ - h i ≤ s + u)
    (hlow : s - (slopeData C).muMin ⊥ ⊤ ≤ Hmax)
    (hgram : ∑ i, hs2 (gram (c i) (A i) - LinearMap.id) ≤
      e * ∑ i, (finrank ℝ (V i) : ℝ))
    (hframe : LinearMap.trace ℝ H (frame c A ∘ₗ frame c A) ≤
      (1 + η) * (LinearMap.trace ℝ H (frame c A)) ^ 2 / finrank ℝ H) :
    s - latticeSlope C ≤ (finrank ℝ H : ℝ) / finrank ℝ W *
      (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax) ∧
    (finrank ℤ C : ℝ) * (s - latticeSlope C) +
      ((finrank ℝ W : ℝ) - finrank ℤ C) * Hmax ≤ finrank ℝ H *
        (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax) ∧
    ∀ δ : ℝ, δ < 1 → (1 - δ) * finrank ℝ H ≤ (finrank ℝ W : ℝ) →
      s - latticeSlope C ≤
        (4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax) / (1 - δ) := by
  classical
  let dn : ∀ i, Data (N i) := fun i => data (N i)
  let dc : Data C := data C
  let J : I → Type := fun i => Fin (dn i).values.length
  let k := finrank ℝ W - finrank ℤ C
  let K := Fin dc.values.length ⊕ Fin k
  let x : ∀ i, J i → ℝ := fun i j => (dn i).values.get j - h i
  let y : K → ℝ := Sum.elim (fun j => dc.values.get j) (fun _ => s - Hmax)
  have hKcard : Fintype.card K = finrank ℝ W := by
    simp only [K, Fintype.card_sum, Fintype.card_fin, dc.length_eq]
    exact Nat.add_sub_of_le (rank_le_ambient C)
  have hymin : ∀ j, s - Hmax ≤ y j := by
    intro j
    cases j with
    | inl j => exact (by linarith : s - Hmax ≤ (slopeData C).muMin ⊥ ⊤).trans (dc.bounds j).1
    | inr j => exact le_rfl
  choose a haMin haMax haCount using fun (t : ℝ) (i : I) =>
    (dn i).cut (s - t + h i)
  choose b hbMin hbMax hbCount using fun t : ℝ => dc.cut (s - t)
  let flags : SpectralFlags V H A J K x y s Hmax := {
    source := fun t i => span (N i) (a t i)
    target := fun t => if t = Hmax then ⊤ else (span C (b t)).comap P
    source_dim := fun i => by simp [J, (dn i).length_eq, full_rank (N i) (hN i)]
    source_codim := by
      intro t ht i
      rw [haCount, full_rank (N i) (hN i), Nat.sub_self, zero_add]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro j _
      dsimp [x]
      constructor <;> intro hh <;> linarith
    target_codim := by
      intro t ht
      by_cases hEnd : t = Hmax
      · have hz : (univ.filter fun j : K => y j < s - Hmax) = ∅ :=
          filter_eq_empty_iff.mpr (fun j _ => not_lt_of_ge (hymin j))
        rw [if_pos hEnd, Submodule.top_orthogonal_eq_bot, finrank_bot]
        simp only [hEnd, hz, card_empty]
      · rw [if_neg hEnd, comap_codim P hP, hbCount]
        have hlt : t < Hmax := lt_of_le_of_ne ht.2 hEnd
        change k + (univ.filter fun j => dc.values.get j < s - t).card =
          (univ.filter fun j : Fin dc.values.length ⊕ Fin k =>
            Sum.elim (fun j => dc.values.get j) (fun _ => s - Hmax) j < s - t).card
        rw [count_padded, if_pos hlt]; omega
    placement := by
      intro t ht i
      by_cases hEnd : t = Hmax
      · rw [if_pos hEnd]
        exact le_top
      · rw [if_neg hEnd]
        rw [Submodule.map_le_iff_le_comap]
        apply Submodule.span_le.mpr
        intro z hz
        change P (A i z) ∈ span C (b t)
        have hmap : P (A i z) = B i z := congrArg (fun f => f z) (hPA i)
        rw [hmap]
        by_contra hmod
        have has : (⊥ : Sublattice (N i)) < a t i := by
          apply bot_lt_iff_ne_bot.mpr
          intro ha
          rw [ha, bot_carrier] at hz
          have hz0 : z = 0 := hz
          simp [hz0] at hmod
        have hbt : b t < (⊤ : Sublattice C) := by
          apply lt_top_iff_ne_top.mpr
          intro hb
          apply hmod
          simp only [span, hb, integral_top]
          exact Submodule.subset_span (hBC i z (integral_le (N i) (a t i) hz))
        have hm := slope_morphism (N i) C (a t i) (b t) (B i) (h i)
          (fun z hz => hBC i z (integral_le (N i) (a t i) hz))
          ⟨z, hz, hmod⟩ (fun v _ =>
            ((span C (b t))ᗮ.norm_starProjection_apply_le (B i v)).trans
              (((B i).le_opNorm v).trans (mul_le_mul_of_nonneg_right
                (Real.le_exp_of_log_le (hB i (by
                  intro hbzero; apply hmod; simp [hbzero]))) (norm_nonneg v))))
        have hn := haMin t i has
        have hc := hbMax t hbt
        linarith
  }
  have hsumN (i : I) : (∑ j, x i j) =
      (finrank ℤ (N i) : ℝ) * (latticeSlope (N i) - h i) := by
    dsimp [x, J]
    rw [sum_sub_distrib, sum_get, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, (dn i).length_eq, ← weighted_slope (N i) (dn i)]
    ring
  have hcard (i : I) : Fintype.card (J i) = finrank ℤ (N i) := by
    simp only [J, Fintype.card_fin, (dn i).length_eq, full_rank (N i) (hN i)]
  have hmean : (∑ i, (Fintype.card (J i) : ℝ)) * s ≤ ∑ i, ∑ j, x i j := by
    simpa only [hcard, hsumN] using hav
  have hxmax : ∀ i j, x i j ≤ s + u := by
    intro i j; exact (sub_le_sub_right ((dn i).bounds j).2 _).trans
      (hmax i (by have hj := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
                  have heq := (dn i).length_eq; omega))
  have hK : 0 < Fintype.card K := by simpa only [hKcard] using hd
  have result := spectral_frame_slope c A x y s u Hmax e η flags hR
    hH he1 hK hmean hxmax hymin hgram hframe
  have hfloor : s - Hmax ≤ latticeSlope C :=
    (by linarith : s - Hmax ≤ (slopeData C).muMin ⊥ ⊤).trans (mean_ge_min C dc)
  have hsumY : (∑ j, y j) =
      (finrank ℤ C : ℝ) * latticeSlope C + (k : ℝ) * (s - Hmax) := by
    dsimp [y, K]
    rw [sum_padded]; simp only [List.get_eq_getElem, sum_get, ← weighted_slope C dc]
  have hcountK : Fintype.card K = finrank ℤ C + k := by
    simp only [K, Fintype.card_sum, Fintype.card_fin, dc.length_eq]
  have hdim : (0 : ℝ) < Fintype.card K := by exact_mod_cast hK
  have hcast : (Fintype.card K : ℝ) = (finrank ℤ C : ℝ) + k := by
    exact_mod_cast hcountK
  have hmeanY : (∑ j, y j) / Fintype.card K ≤ latticeSlope C := by
    apply (div_le_iff₀ hdim).mpr
    rw [hsumY, hcast]
    nlinarith [mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg k)]
  have hexact := (sub_le_sub_left hmeanY s).trans result.2
  rw [hKcard] at hexact
  have hsum : (Fintype.card K : ℝ) * s - ∑ j, y j ≤
      ∑ j, max (s - y j) 0 := by
    simpa only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] using
      (sum_le_sum fun j (_ : j ∈ univ) => le_max_left (s - y j) 0)
  have hk : (k : ℝ) = (finrank ℝ W : ℝ) - finrank ℤ C :=
    Nat.cast_sub (rank_le_ambient C)
  have hw := hsum.trans result.1
  rw [hsumY, hcast, hk] at hw
  refine ⟨hexact, by nlinarith only [hw], ?_⟩
  intro δ hδ hratio
  let G := 4 * u * Real.log (1 + Hmax / u) + (η + 4 * Real.sqrt e) * Hmax
  have hDr : (0 : ℝ) < finrank ℝ H := by
    exact_mod_cast hd.trans_le (LinearMap.finrank_le_finrank_of_surjective hP)
  have hG : 0 ≤ G := nonneg_of_mul_nonneg_right
    ((sum_nonneg fun j _ => le_max_right (s - y j) 0).trans result.1) hDr
  have hdp : (0 : ℝ) < finrank ℝ W := by exact_mod_cast hd
  have hδp : 0 < 1 - δ := by linarith
  have hratio' : (finrank ℝ H : ℝ) / finrank ℝ W ≤ 1 / (1 - δ) := by
    apply (div_le_div_iff₀ hdp hδp).mpr
    nlinarith only [hratio]
  exact hexact.trans (by simpa only [G, one_div, div_eq_inv_mul, one_mul, mul_one] using
    mul_le_mul_of_nonneg_right hratio' hG)
end D5.S3.Combinatorics.Lattices.EuclideanCommonLattice
