/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Right dimension bounds for a width-four Clifford coefficient kernel. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeThreeRectangularBound

/-! The paired Clifford relations constrain the rank of the right column factors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree

open NativeFourKernel (compression compression_star)
open NativeRectangularBound
open D5.S3.Quantum.Algebra.NativeCoefficientWhitening (mix mix_apply flat flat_gram flat_injective)
open D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation (concatK)

private theorem full_rank_of_injective {c d : ℕ} (Y : Matrix (Fin d) (Fin c) ℂ)
    (hY : Function.Injective Y.mulVecLin) : Y.rank = c := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hY, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

private theorem orthogonal_rank {c d : ℕ} {A B : Matrix (Fin d) (Fin c) ℂ}
    {S : Submodule ℂ (Fin d → ℂ)}
    (hA : LinearMap.range A.mulVecLin ≤ S) (hB : LinearMap.range B.mulVecLin ≤ S)
    (h : Aᴴ * B = 0) : A.rank + B.rank ≤ finrank ℂ S := by
  have hdis : Disjoint (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
    change B *ᵥ v = A *ᵥ u at hv
    apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero A u).mp
    rw [← Matrix.mulVec_mulVec, ← hv, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  rw [hdis.eq_bot, finrank_bot, add_zero] at hdim
  rw [Matrix.rank, Matrix.rank, ← hdim]
  exact Submodule.finrank_mono (sup_le hA hB)

private theorem rank_sum {m n : ℕ} (P Q : Matrix (Fin m) (Fin n) ℂ) :
    (P + Q).rank ≤ P.rank + Q.rank := by
  rw [Matrix.rank, Matrix.mulVecLin_add]
  have hr : LinearMap.range (P.mulVecLin + Q.mulVecLin) ≤
      LinearMap.range P.mulVecLin ⊔ LinearMap.range Q.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hr).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem concat_range {c d k : ℕ}
    (W : Fin k → Matrix (Fin d) (Fin c) ℂ) (i : Fin k) :
    LinearMap.range (W i).mulVecLin ≤ LinearMap.range (concatK W).mulVecLin := by
  classical
  rintro _ ⟨v, rfl⟩
  refine ⟨fun p => if p.1 = i then v p.2 else 0, ?_⟩
  ext j
  change (concatK W *ᵥ (fun p => if p.1 = i then v p.2 else 0)) j = (W i *ᵥ v) j
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, concatK]
  rw [Finset.sum_eq_single i]
  · simp
  · intro r _ hr
    simp [hr]
  · simp

private theorem scalar_offset_zero {c : ℕ} {A B : Matrix (Fin c) (Fin c) ℂ}
    {z : ℂ} {x : Fin c → ℂ} (hx : x ≠ 0)
    (hA : Aᴴ *ᵥ x = 0) (hB : Bᴴ *ᵥ x = 0) (h : A + Bᴴ = z • 1) : z = 0 := by
  have hrow : star x ᵥ* A = 0 := by
    simpa [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose] using congrArg star hA
  have hdot := congrArg (fun M : Matrix (Fin c) (Fin c) ℂ =>
    star x ⬝ᵥ (M *ᵥ x)) h
  simp only [Matrix.add_mulVec, dotProduct_add, hB, dotProduct_zero, add_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul] at hdot
  rw [Matrix.dotProduct_mulVec, hrow, zero_dotProduct, eq_comm, smul_eq_mul] at hdot
  exact (mul_eq_zero.mp hdot).resolve_right (fun hzero =>
    hx (dotProduct_star_self_eq_zero.mp hzero))

private theorem equal_pairs {c d : ℕ} (A B C D : Matrix (Fin d) (Fin c) ℂ)
    (S : Submodule ℂ (Fin d → ℂ))
    (hAS : LinearMap.range A.mulVecLin ≤ S) (hBS : LinearMap.range B.mulVecLin ≤ S)
    (hCS : LinearMap.range C.mulVecLin ≤ S) (hDS : LinearMap.range D.mulVecLin ≤ S)
    {P Q : Matrix (Fin c) (Fin c) ℂ} {h : ℝ} (hh : 0 < h)
    (hA : Aᴴ * A = P) (hB : Bᴴ * B = P) (hC : Cᴴ * C = Q) (hD : Dᴴ * D = Q)
    (hAB : Aᴴ * B = 0) (hCD : Cᴴ * D = 0)
    (hPQ : P + Q = h • 1)
    (hz : ∃ z : ℂ, Aᴴ * C - (Bᴴ * D)ᴴ = z • 1)
    (hw : ∃ w : ℂ, Aᴴ * D + (Bᴴ * C)ᴴ = w • 1) :
    2 * c ≤ finrank ℂ S := by
  classical
  let K := LinearMap.ker P.mulVecLin
  by_cases hK : K = ⊥
  · have hP := full_rank_of_injective P (LinearMap.ker_eq_bot.mp hK)
    have h := orthogonal_rank hAS hBS hAB
    rw [← Matrix.rank_conjTranspose_mul_self A, ← Matrix.rank_conjTranspose_mul_self B,
      hA, hB, hP] at h
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have leftA (y : Fin c → ℂ) (hy : y ∈ K) : A *ᵥ y = 0 := by
    apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero A y).mp
    rw [hA]
    exact hy
  have leftB (y : Fin c → ℂ) (hy : y ∈ K) : B *ᵥ y = 0 := by
    apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero B y).mp
    rw [hB]
    exact hy
  have killA (Y : Matrix (Fin d) (Fin c) ℂ) (y : Fin c → ℂ) (hy : y ∈ K) :
      (Aᴴ * Y)ᴴ *ᵥ y = 0 := by
    simp [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, leftA y hy]
  have killB (Y : Matrix (Fin d) (Fin c) ℂ) (y : Fin c → ℂ) (hy : y ∈ K) :
      (Bᴴ * Y)ᴴ *ᵥ y = 0 := by
    simp [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, leftB y hy]
  obtain ⟨z, hz⟩ := hz
  obtain ⟨w, hw⟩ := hw
  have hz0 : z = 0 := scalar_offset_zero (A := Aᴴ * C) (B := -(Bᴴ * D))
    hx0 (killA C x hx) (by rw [Matrix.conjTranspose_neg, Matrix.neg_mulVec, killB D x hx, neg_zero])
    (by simpa [sub_eq_add_neg] using hz)
  have hw0 : w = 0 := scalar_offset_zero hx0 (killA D x hx) (killB C x hx) hw
  have hAC : Aᴴ * C = (Bᴴ * D)ᴴ :=
    sub_eq_zero.mp (by simpa only [hz0, zero_smul] using hz)
  have hAD : Aᴴ * D = -(Bᴴ * C)ᴴ :=
    eq_neg_of_add_eq_zero_left (by simpa [hw0] using hw)
  have hBD : Bᴴ * D = (Aᴴ * C)ᴴ := by
    simpa using (congrArg Matrix.conjTranspose hAC).symm
  have hBC : Bᴴ * C = -(Aᴴ * D)ᴴ := by
    simpa using congrArg (fun M : Matrix (Fin c) (Fin c) ℂ => -Mᴴ) hAD |>.symm
  obtain ⟨L, hKL⟩ := K.exists_isCompl
  let V : Matrix (Fin c) (Fin c) ℂ := LinearMap.toMatrix' (K.projection L hKL)
  have hV (y : Fin c → ℂ) : V *ᵥ y ∈ K := by
    change (LinearMap.toMatrix' (K.projection L hKL)) *ᵥ y ∈ K
    rw [LinearMap.toMatrix'_mulVec]
    exact (K.projectionOnto L hKL y).property
  have hVy (y : Fin c → ℂ) (hy : y ∈ K) : V *ᵥ y = y := by
    change (LinearMap.toMatrix' (K.projection L hKL)) *ᵥ y = y
    rw [LinearMap.toMatrix'_mulVec, Submodule.projection_apply_of_mem_left hKL hy]
  have vanishes (M : Matrix (Fin c) (Fin c) ℂ)
      (hm : ∀ y ∈ K, M *ᵥ y = 0) : M * V = 0 := by
    ext i j
    have h := congrFun (hm (V *ᵥ Pi.single j 1) (hV _)) i
    change (M *ᵥ V.col j) i = 0
    simpa only [Matrix.mulVec_single_one, Pi.zero_apply] using h
  have vAC : Aᴴ * C * V = 0 := vanishes _ (fun y hy => by rw [hAC, killB D y hy])
  have vAD : Aᴴ * D * V = 0 := vanishes _ (fun y hy => by rw [hAD, Matrix.neg_mulVec, killB C y hy, neg_zero])
  have vBC : Bᴴ * C * V = 0 := vanishes _ (fun y hy => by rw [hBC, Matrix.neg_mulVec, killA D y hy, neg_zero])
  have vBD : Bᴴ * D * V = 0 := vanishes _ (fun y hy => by rw [hBD, killA C y hy])
  let U := A + C * V
  let W := B + D * V
  have hUW : Uᴴ * W = 0 := by
    have h := congrArg Matrix.conjTranspose vBC
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h
    have h' : Vᴴ * Cᴴ * B = 0 := by simpa only [Matrix.mul_assoc] using h
    have h'' : Vᴴ * Cᴴ * D * V = 0 := by
      rw [Matrix.mul_assoc Vᴴ Cᴴ D, hCD, Matrix.mul_zero, Matrix.zero_mul]
    simp only [U, W, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc,
      hAB, vAD, h', h'', add_zero, zero_add]
  have extend_injective (Y Z : Matrix (Fin d) (Fin c) ℂ)
      (hy : Yᴴ * Y = P) (hz : Zᴴ * Z = Q) (hyz : Yᴴ * Z * V = 0)
      (hyK : ∀ y ∈ K, Y *ᵥ y = 0) : Function.Injective (Y + Z * V).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro y hY
    change (Y + Z * V) *ᵥ y = 0 at hY
    have hp : P *ᵥ y = 0 := by
      have ht := congrArg (fun v => Yᴴ *ᵥ v) hY
      simpa [Matrix.mulVec_mulVec, Matrix.mul_add, ← Matrix.mul_assoc, hy, hyz] using ht
    have hk : y ∈ K := hp
    have hzy : Z *ᵥ y = 0 := by
      simpa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hVy y hk, hyK y hk] using hY
    have hq : Q *ᵥ y = 0 := by rw [← hz, ← Matrix.mulVec_mulVec, hzy, Matrix.mulVec_zero]
    have hs := congrArg (fun M : Matrix (Fin c) (Fin c) ℂ => M *ᵥ y) hPQ
    have hs' : h • y = 0 := by simpa [Matrix.add_mulVec, hp, hq, Matrix.smul_mulVec] using hs.symm
    exact (smul_eq_zero.mp hs').resolve_left hh.ne'
  have hu := full_rank_of_injective U (extend_injective A C hA hC vAC leftA)
  have hw := full_rank_of_injective W (extend_injective B D hB hD vBD leftB)
  have extend_range (Y Z : Matrix (Fin d) (Fin c) ℂ)
      (hy : LinearMap.range Y.mulVecLin ≤ S)
      (hz : LinearMap.range Z.mulVecLin ≤ S) :
      LinearMap.range (Y + Z * V).mulVecLin ≤ S := by
    rintro _ ⟨y, rfl⟩
    change (Y + Z * V) *ᵥ y ∈ S
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    exact S.add_mem (hy ⟨y, rfl⟩) (hz ⟨V *ᵥ y, rfl⟩)
  have h : U.rank + W.rank ≤ finrank ℂ S :=
    orthogonal_rank (extend_range A C hAS hCS) (extend_range B D hBS hDS) hUW
  omega

private theorem paired_gram_bound {c d : ℕ} (A B C D : Matrix (Fin d) (Fin c) ℂ)
    (S : Submodule ℂ (Fin d → ℂ))
    (hAS : LinearMap.range A.mulVecLin ≤ S) (hBS : LinearMap.range B.mulVecLin ≤ S)
    (hCS : LinearMap.range C.mulVecLin ≤ S) (hDS : LinearMap.range D.mulVecLin ≤ S)
    (p₁ p₂ q₁ q₂ : ℝ) (hp : 0 < p₁) (hp' : 0 < p₂) (hq : 0 < q₁) (hq' : 0 < q₂)
    (T : Matrix (Fin c) (Fin c) ℂ)
    (hA : Aᴴ * A = p₁ • 1 + T) (hB : Bᴴ * B = p₂ • 1 + T)
    (hC : Cᴴ * C = q₁ • 1 - T) (hD : Dᴴ * D = q₂ • 1 - T)
    (hAB : Aᴴ * B = 0) (hCD : Cᴴ * D = 0)
    (hz : ∃ z : ℂ, Aᴴ * C - (Bᴴ * D)ᴴ = z • 1)
    (hw : ∃ w : ℂ, Aᴴ * D + (Bᴴ * C)ᴴ = w • 1) :
    4 * c ≤ 3 * finrank ℂ S := by
  classical
  let P := min p₁ p₂ • (1 : Matrix (Fin c) (Fin c) ℂ) + T
  let Q := min q₁ q₂ • (1 : Matrix (Fin c) (Fin c) ℂ) - T
  have hPQ : P + Q =
      (min p₁ p₂ + min q₁ q₂) • (1 : Matrix (Fin c) (Fin c) ℂ) := by
    dsimp [P, Q]
    rw [add_smul]
    abel
  have hpos : 0 < min p₁ p₂ + min q₁ q₂ :=
    add_pos (lt_min hp hp') (lt_min hq hq')
  have hs := rank_sum P Q
  have hfull : (P + Q).rank = c := by
    apply full_rank_of_injective
    rw [hPQ]
    exact (Matrix.PosDef.one.smul hpos).mulVec_injective
  rw [hfull] at hs
  have pair (Y Z : Matrix (Fin d) (Fin c) ℂ) (s t : ℝ)
      (hy : LinearMap.range Y.mulVecLin ≤ S)
      (hz : LinearMap.range Z.mulVecLin ≤ S)
      (R : Matrix (Fin c) (Fin c) ℂ) (hY : Yᴴ * Y = s • 1 + R)
      (hZ : Zᴴ * Z = t • 1 + R) (hyz : Yᴴ * Z = 0) :
      let r := (min s t • (1 : Matrix (Fin c) (Fin c) ℂ) + R).rank
      (if s = t then 2 * r else c + r) ≤ finrank ℂ S := by
    dsimp only
    have h := orthogonal_rank hy hz hyz
    rw [← Matrix.rank_conjTranspose_mul_self Y, ← Matrix.rank_conjTranspose_mul_self Z] at h
    rcases lt_trichotomy s t with hst | rfl | hst
    · rw [if_neg hst.ne, min_eq_left hst.le, ← hY]
      have he : Zᴴ * Z = (t - s) • 1 + Yᴴ * Y := by
        rw [hZ, hY, sub_smul]
        abel
      have hr : (Zᴴ * Z).rank = c := by
        apply full_rank_of_injective
        rw [he]
        exact ((Matrix.PosDef.one.smul (sub_pos.mpr hst)).add_posSemidef
          (Matrix.posSemidef_conjTranspose_mul_self Y)).mulVec_injective
      omega
    · rw [if_pos rfl, min_self, ← hY]
      rw [hZ, ← hY] at h
      omega
    · rw [if_neg hst.ne', min_eq_right hst.le, ← hZ]
      have he : Yᴴ * Y = (s - t) • 1 + Zᴴ * Z := by
        rw [hY, hZ, sub_smul]
        abel
      have hr : (Yᴴ * Y).rank = c := by
        apply full_rank_of_injective
        rw [he]
        exact ((Matrix.PosDef.one.smul (sub_pos.mpr hst)).add_posSemidef
          (Matrix.posSemidef_conjTranspose_mul_self Z)).mulVec_injective
      omega
  have hleft : (if p₁ = p₂ then 2 * P.rank else c + P.rank) ≤ finrank ℂ S :=
    pair A B p₁ p₂ hAS hBS T hA hB hAB
  have hright : (if q₁ = q₂ then 2 * Q.rank else c + Q.rank) ≤ finrank ℂ S := by
    simpa only [sub_eq_add_neg, Q] using
      pair C D q₁ q₂ hCS hDS (-T) (by simpa only [sub_eq_add_neg] using hC)
        (by simpa only [sub_eq_add_neg] using hD) hCD
  by_cases he : p₁ = p₂ <;> by_cases hf : q₁ = q₂
  · have hh := equal_pairs A B C D S hAS hBS hCS hDS hpos
      (by simpa only [P, he, min_self] using hA)
      (by simpa only [P, he, min_self] using hB)
      (by simpa only [Q, hf, min_self] using hC)
      (by simpa only [Q, hf, min_self] using hD) hAB hCD hPQ hz hw
    omega
  all_goals simp [he, hf] at hleft hright
  all_goals omega

private abbrev Coeff := Matrix (Fin 4) (Fin 4) ℂ

/-- The five Pauli Clifford matrices in the tensor product coordinate basis. -/
def pauliClifford : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, 0, -Complex.I, 0; 0, 0, 0, -Complex.I;
       Complex.I, 0, 0, 0; 0, Complex.I, 0, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0],
    !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0;
       0, 0, 0, Complex.I; 0, 0, -Complex.I, 0],
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]]

private def pairOrder : Fin 4 ≃ Fin 4 := Equiv.swap 1 3

private def paired (v : Fin 5 → ℂ) : Coeff :=
  !![v 0, 0, v 1, v 2;
     0, v 0, -v 3, v 4;
     v 4, -v 2, -v 0, 0;
     v 3, v 1, 0, -v 0]

private def pairedLin : (Fin 5 → ℂ) →ₗ[ℂ] Coeff where
  toFun := paired
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [paired, add_comm]
  map_smul' z v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [paired, Pi.smul_apply]

private def pairedSpace : Submodule ℂ Coeff :=
  LinearMap.range pairedLin

private theorem clifford_reindex (T : Coeff)
    (h : T ∈ Submodule.span ℝ (Set.range pauliClifford)) :
    T.submatrix pairOrder pairOrder ∈ pairedSpace := by
  induction h using Submodule.span_induction with
  | mem T h =>
    obtain ⟨i, rfl⟩ := h
    apply LinearMap.mem_range.mpr
    fin_cases i
    · refine ⟨![0, 1, 0, 0, 1], ?_⟩
      ext r s; fin_cases r <;> fin_cases s <;>
        simp [pairedLin, paired, pauliClifford, Matrix.submatrix_apply, pairOrder, Equiv.swap_apply_def]
    · refine ⟨![0, -Complex.I, 0, 0, Complex.I], ?_⟩
      ext r s; fin_cases r <;> fin_cases s <;>
        simp [pairedLin, paired, pauliClifford, Matrix.submatrix_apply, pairOrder, Equiv.swap_apply_def]
    · refine ⟨![0, 0, 1, 1, 0], ?_⟩
      ext r s; fin_cases r <;> fin_cases s <;>
        simp [pairedLin, paired, pauliClifford, Matrix.submatrix_apply, pairOrder, Equiv.swap_apply_def]
    · refine ⟨![0, 0, -Complex.I, Complex.I, 0], ?_⟩
      ext r s; fin_cases r <;> fin_cases s <;>
        simp [pairedLin, paired, pauliClifford, Matrix.submatrix_apply, pairOrder, Equiv.swap_apply_def]
    · refine ⟨![1, 0, 0, 0, 0], ?_⟩
      ext r s; fin_cases r <;> fin_cases s <;>
        simp [pairedLin, paired, pauliClifford, Matrix.submatrix_apply, pairOrder, Equiv.swap_apply_def]
  | zero => exact pairedSpace.zero_mem
  | add A B _ _ hA hB => exact pairedSpace.add_mem hA hB
  | smul r A _ hA => exact pairedSpace.smul_mem (r : ℂ) hA

private def pairMatrix (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u, v; -star v, star u]

private def pairChange (u v w x : ℂ) : Coeff :=
  !![u, v, 0, 0; -star v, star u, 0, 0;
     0, 0, w, x; 0, 0, -star x, star w]

private theorem diagonalize_pair (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.PosDef) :
    ∃ (u v : ℂ) (s t : ℝ), 0 < s ∧ 0 < t ∧
      star u * u + star v * v = 1 ∧
      (pairMatrix u v)ᴴ * H * pairMatrix u v = diagonal ![(s : ℂ), (t : ℂ)] := by
  classical
  let U : Matrix (Fin 2) (Fin 2) ℂ := hH.isHermitian.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hd : star U.det * U.det = 1 := by
    simpa [Matrix.det_mul, Matrix.det_conjTranspose] using congrArg Matrix.det hU
  have hd' : U.det * (starRingEnd ℂ) U.det = 1 := by
    change U.det * star U.det = 1
    rw [mul_comm, hd]
  let E : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, star U.det]
  let S := U * E
  have hE : Eᴴ * E = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Matrix.one_apply, hd']
  have hS : Sᴴ * S = 1 := by
    change (U * E)ᴴ * (U * E) = 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U E,
      hU, Matrix.one_mul, hE]
  have hdet : S.det = 1 := by
    simp only [S, E, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    rwa [mul_comm]
  have ha : S.adjugate = Sᴴ := by
    calc
      S.adjugate = Sᴴ * (S * S.adjugate) := by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
      _ = Sᴴ := by rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]
  have h00 : S 1 1 = star (S 0 0) := by
    simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using
      congrFun (congrFun ha 0) 0
  have h10 : S 1 0 = -star (S 0 1) := by
    have h : -S 1 0 = star (S 0 1) := by
      simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply] using
        congrFun (congrFun ha 1) 0
    rw [← h, neg_neg]
  let u := S 0 0
  let v := S 0 1
  have hSform : S = pairMatrix u v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMatrix, u, v, h00, h10]
  have hdS : star u * u + star v * v = 1 := by
    rw [hSform] at hS
    have h := congrFun (congrFun hS 0) 0
    simpa [pairMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      mul_comm] using h
  let e := hH.isHermitian.eigenvalues
  refine ⟨u, v, e 0, e 1, hH.eigenvalues_pos _, hH.eigenvalues_pos _, hdS, ?_⟩
  have hdiag : Uᴴ * H * U = diagonal (fun i => (e i : ℂ)) := by
    have h := hH.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at h
    with_unfolding_all exact h
  calc
    (pairMatrix u v)ᴴ * H * pairMatrix u v = Eᴴ * (Uᴴ * H * U) * E := by
      rw [← hSform]
      change (U * E)ᴴ * H * (U * E) = _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = diagonal ![(e 0 : ℂ), (e 1 : ℂ)] := ?_
  rw [hdiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, ← mul_assoc]
  calc
    U.det * (e 1 : ℂ) * (starRingEnd ℂ) U.det =
        (e 1 : ℂ) * (U.det * (starRingEnd ℂ) U.det) := by ring
    _ = (e 1 : ℂ) := by rw [hd', mul_one]

private theorem paired_change_mem (u v w x : ℂ)
    (hu : star u * u + star v * v = 1) (hw : star w * w + star x * x = 1)
    {T : Coeff} (hT : T ∈ pairedSpace) :
    (pairChange u v w x)ᴴ * T * pairChange u v w x ∈ pairedSpace := by
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp (show T ∈ LinearMap.range pairedLin from hT)
  change paired a = T at ha
  rw [← ha]
  apply LinearMap.mem_range.mpr
  let B := (pairChange u v w x)ᴴ * paired a * pairChange u v w x
  refine ⟨![a 0, B 0 2, B 0 3, B 3 0, B 2 0], ?_⟩
  have h₁ : (a 0) * (star u * u + star v * v) = a 0 := by rw [hu, mul_one]
  have h₂ : (a 0) * (star w * w + star x * x) = a 0 := by rw [hw, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, pairedLin, paired, pairChange, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four, starRingEnd_apply] <;>
    first | (ring; done) | (linear_combination -h₁; done) | linear_combination h₂


private def topPair (i : Fin 2) : Fin 4 := Fin.castAdd 2 i
private def bottomPair (i : Fin 2) : Fin 4 := Fin.natAdd 2 i

private theorem topPair_compression (H : Coeff) (u v w x : ℂ) :
    ((pairChange u v w x)ᴴ * H * pairChange u v w x).submatrix topPair topPair =
      (pairMatrix u v)ᴴ * H.submatrix topPair topPair * pairMatrix u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topPair, pairChange, pairMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_four, Fin.sum_univ_two]

private theorem bottomPair_compression (H : Coeff) (u v w x : ℂ) :
    ((pairChange u v w x)ᴴ * H * pairChange u v w x).submatrix bottomPair bottomPair =
      (pairMatrix w x)ᴴ * H.submatrix bottomPair bottomPair * pairMatrix w x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bottomPair, pairChange, pairMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_four, Fin.sum_univ_two]

private def rightMoment {c d : ℕ} (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (l m : Fin c) : Coeff :=
  fun i j => ((Y i)ᴴ * Y j) l m

private theorem moment_mix {c d : ℕ} (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (P : Coeff) (l m : Fin c) :
    rightMoment (mix Pᵀ Y) l m = Pᴴ * rightMoment Y l m * P := by
  let column (U : Fin 4 → Matrix (Fin d) (Fin c) ℂ) (i : Fin c) :
      Matrix (Fin d) (Fin 4) ℂ := fun a r => U r a i
  have hcolumn (i : Fin c) : column (mix Pᵀ Y) i = column Y i * P := by
    ext a r
    simp [column, mix_apply, Matrix.mul_apply, mul_comm]
  change (column (mix Pᵀ Y) l)ᴴ * column (mix Pᵀ Y) m =
    Pᴴ * ((column Y l)ᴴ * column Y m) * P
  rw [hcolumn l, hcolumn m, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private def compressionLin {a b : ℕ} (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) :
    Coeff →ₗ[ℂ] Matrix (Fin b) (Fin b) ℂ where
  toFun := compression X
  map_add' T U := by
    simp only [compression, Matrix.kronecker, Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]
  map_smul' z T := by
    simp only [compression, RingHom.id_apply, Matrix.kronecker, Matrix.smul_kronecker,
      Matrix.mul_smul, Matrix.smul_mul]

private theorem rightMoment_compression {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (lam : ℝ) (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
      (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))
    (l m : Fin c) :
    compressionLin X (rightMoment Y l m) = (1 : Matrix (Fin c) (Fin c) ℂ) l m •
        ((lam : ℂ) • (1 : Matrix (Fin b) (Fin b) ℂ)) := by
  change compression X _ = _
  rw [compression, stackK_compression]
  have hExp : (∑ r, kronecker (X r) (Y r))ᴴ * (∑ r, kronecker (X r) (Y r)) =
      ∑ r, ∑ s, kronecker ((X r)ᴴ * X s) ((Y r)ᴴ * Y s) := by
    simp only [Matrix.kronecker, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    exact Finset.sum_comm
  rw [hExp] at hF
  ext u v
  have h := congrArg (fun M : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ =>
    M (u, l) (v, m)) hF
  by_cases huv : u = v <;> by_cases hlm : l = m <;>
    simpa [rightMoment, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, huv, hlm, mul_comm] using h

private def coefficientTransport (P : Coeff) : Coeff →ₗ[ℂ] Coeff where
  toFun T := (Pᴴ * T * P).submatrix pairOrder pairOrder
  map_add' T U := by
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.submatrix_apply, Matrix.add_apply]
  map_smul' z T := by
    ext i j
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_apply,
      Matrix.smul_apply]

private theorem complex_kernel_transport {a b : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (P : Coeff)
    (hP : ∀ T : Coeff, T.IsHermitian → compression X T = 0 →
      Pᴴ * T * P ∈ Submodule.span ℝ (Set.range pauliClifford))
    (T : Coeff) (hT : compressionLin X T = 0) :
    coefficientTransport P T ∈ pairedSpace := by
  have hstar : compressionLin X Tᴴ = 0 := by
    change compression X Tᴴ = 0
    rw [compression_star, show compression X T = 0 from hT, Matrix.conjTranspose_zero]
  let A := T + Tᴴ
  let B := Complex.I • (T - Tᴴ)
  have hA : coefficientTransport P A ∈ pairedSpace := by
    apply clifford_reindex _ (hP A ?_ ?_)
    · change Aᴴ = A
      simp [A, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
    · change compressionLin X (T + Tᴴ) = 0
      rw [map_add, hT, hstar, zero_add]
  have hB : coefficientTransport P B ∈ pairedSpace := by
    apply clifford_reindex _ (hP B ?_ ?_)
    · change Bᴴ = B
      simp [B, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, Complex.conj_I, neg_smul, smul_sub, sub_eq_add_neg, add_comm]
    · change compressionLin X (Complex.I • (T - Tᴴ)) = 0
      rw [map_smul, map_sub, hT, hstar, sub_self, smul_zero]
  have he : A - Complex.I • B = (2 : ℂ) • T := by
    simp [A, B, smul_smul, Complex.I_mul_I, neg_one_smul]
    module
  have h := pairedSpace.sub_mem hA (pairedSpace.smul_mem Complex.I hB)
  rw [← map_smul, ← map_sub, he, map_smul] at h
  have hinv := pairedSpace.smul_mem (2 : ℂ)⁻¹ h
  simpa [smul_smul] using hinv

private theorem scalar_gram_swap {a b c d k : ℕ}
    (X : Fin k → Matrix (Fin a) (Fin b) ℂ) (Y : Fin k → Matrix (Fin d) (Fin c) ℂ) :
    (∑ i, kronecker (Y i) (X i)) =
      (∑ i, kronecker (X i) (Y i)).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, mul_comm]

/-- A Hermitian coefficient kernel congruent into the five Pauli directions
forces the opposite input-output ratio to be at most three quarters. -/
theorem clifford_kernel_four_bound {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (lam : ℝ) (hlam : 0 < lam) (hab : a < b)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) =
      (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ))
    (hK : ∃ P : Matrix (Fin 4) (Fin 4) ℂ, IsUnit P ∧
      ∀ T : Matrix (Fin 4) (Fin 4) ℂ, T.IsHermitian → compression X T = 0 →
        Pᴴ * T * P ∈ Submodule.span ℝ (Set.range pauliClifford)) :
    4 * c ≤ 3 * d := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  by_cases hY : LinearIndependent ℂ Y
  · obtain ⟨P, hP, hK⟩ := hK
    let H := (1 / (c : ℂ)) • ∑ l : Fin c, rightMoment Y l l
    have hHpos : H.PosDef := by
      have he : H = (1 / (c : ℝ)) • ((flat Y)ᴴ * flat Y) := by
        rw [← flat_gram]
        ext i j
        simp [H, rightMoment, Matrix.trace, Matrix.smul_apply, Matrix.sum_apply,
          Complex.real_smul]
      rw [he]
      exact (Matrix.PosDef.conjTranspose_mul_self (flat Y) (flat_injective Y hY)).smul
        (by positivity)
    have hHcomp : compressionLin X H = (lam : ℂ) • (1 : Matrix (Fin b) (Fin b) ℂ) := by
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      dsimp only [H]
      rw [map_smul, map_sum]
      simp only [rightMoment_compression X Y lam hF, Matrix.one_apply_eq, one_smul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, one_div, one_mul, ← mul_assoc, inv_mul_cancel₀ hc']
    let Hr := coefficientTransport P H
    have hHr : Hr.PosDef :=
      ((Matrix.IsUnit.posDef_star_left_conjugate_iff hP).mpr hHpos).submatrix pairOrder.injective
    obtain ⟨u, v, p₁, p₂, hp₁, hp₂, huv, htop⟩ :=
      diagonalize_pair (Hr.submatrix topPair topPair)
        (hHr.submatrix (fun i j hij => Fin.ext (by simpa [topPair] using congrArg Fin.val hij)))
    obtain ⟨w, x, q₁, q₂, hq₁, hq₂, hwx, hbottom⟩ :=
      diagonalize_pair (Hr.submatrix bottomPair bottomPair)
        (hHr.submatrix (fun i j hij => Fin.ext (by
          have h := congrArg Fin.val hij
          simp [bottomPair] at h
          omega)))
    let U := pairChange u v w x
    let S := Uᴴ * Hr * U
    have htop' : S.submatrix topPair topPair = diagonal ![(p₁ : ℂ), (p₂ : ℂ)] :=
      (topPair_compression Hr u v w x).trans htop
    have hbottom' : S.submatrix bottomPair bottomPair = diagonal ![(q₁ : ℂ), (q₂ : ℂ)] :=
      (bottomPair_compression Hr u v w x).trans hbottom
    let Yr := fun i => mix Pᵀ Y (pairOrder i)
    let W := mix Uᵀ Yr
    have hcentered (l m : Fin c) :
        rightMoment W l m - (1 : Matrix (Fin c) (Fin c) ℂ) l m • S ∈ pairedSpace := by
      let z := (1 : Matrix (Fin c) (Fin c) ℂ) l m
      let T := rightMoment Y l m - z • H
      have hT : compressionLin X T = 0 := by
        simp [T, z, rightMoment_compression X Y lam hF, hHcomp]
      have h := paired_change_mem u v w x huv hwx (complex_kernel_transport X P hK T hT)
      have hm : rightMoment Yr l m = coefficientTransport P (rightMoment Y l m) := by
        have hh := congrArg (fun M : Coeff => M.submatrix pairOrder pairOrder)
          (moment_mix Y P l m)
        exact hh
      change rightMoment (mix Uᵀ Yr) l m - z • S ∈ pairedSpace
      rw [moment_mix, hm]
      have hT' : coefficientTransport P T =
          coefficientTransport P (rightMoment Y l m) - z • Hr := by
        simp [T, Hr]
      rw [hT'] at h
      simpa [S, U, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using h
    have hm (l m : Fin c) : ∃ v : Fin 5 → ℂ,
        paired v = rightMoment W l m - (1 : Matrix (Fin c) (Fin c) ℂ) l m • S :=
      LinearMap.mem_range.mp (hcentered l m)
    choose f hf using hm
    let D : Matrix (Fin c) (Fin c) ℂ := fun l m => f l m 0
    have ent (i j : Fin 4) (l m : Fin c) :
        ((W i)ᴴ * W j) l m =
          S i j * (1 : Matrix (Fin c) (Fin c) ℂ) l m + paired (f l m) i j := by
      have h := congrFun (congrFun (hf l m) i) j
      change paired (f l m) i j = rightMoment W l m i j -
        (1 : Matrix (Fin c) (Fin c) ℂ) l m * S i j at h
      calc
        ((W i)ᴴ * W j) l m = paired (f l m) i j + (1 : Matrix (Fin c) (Fin c) ℂ) l m * S i j :=
          sub_eq_iff_eq_add.mp h.symm
        _ = _ := by ring
    have h00 : S 0 0 = (p₁ : ℂ) := by simpa [topPair] using congrFun (congrFun htop' 0) 0
    have h11 : S 1 1 = (p₂ : ℂ) := by simpa [topPair] using congrFun (congrFun htop' 1) 1
    have h22 : S 2 2 = (q₁ : ℂ) := by simpa [bottomPair] using congrFun (congrFun hbottom' 0) 0
    have h33 : S 3 3 = (q₂ : ℂ) := by simpa [bottomPair] using congrFun (congrFun hbottom' 1) 1
    have h01 : S 0 1 = 0 := by simpa [topPair] using congrFun (congrFun htop' 0) 1
    have h23 : S 2 3 = 0 := by simpa [bottomPair] using congrFun (congrFun hbottom' 0) 1
    let C := concatK W
    let G := Cᴴ * C
    have hGrank : G.rank = finrank ℂ (LinearMap.range C.mulVecLin) :=
      Matrix.rank_conjTranspose_mul_self C
    have hG : 4 * c ≤ 3 * G.rank := by
      rw [hGrank]
      apply paired_gram_bound (W 0) (W 1) (W 2) (W 3) (LinearMap.range C.mulVecLin)
        (concat_range W 0) (concat_range W 1) (concat_range W 2) (concat_range W 3)
        p₁ p₂ q₁ q₂ hp₁ hp₂ hq₁ hq₂ D
      · ext l m; simpa [h00, D, paired, Complex.real_smul] using ent 0 0 l m
      · ext l m; simpa [h11, D, paired, Complex.real_smul] using ent 1 1 l m
      · ext l m; simpa [h22, D, paired, Complex.real_smul, sub_eq_add_neg] using ent 2 2 l m
      · ext l m; simpa [h33, D, paired, Complex.real_smul, sub_eq_add_neg] using ent 3 3 l m
      · ext l m; simpa [h01, paired] using ent 0 1 l m
      · ext l m; simpa [h23, paired] using ent 2 3 l m
      · refine ⟨S 0 2 - S 3 1, ?_⟩
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        ext l m
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ent 0 2, ent 3 1]
        simp [paired]
        ring
      · refine ⟨S 0 3 + S 2 1, ?_⟩
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        ext l m
        rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ent 0 3, ent 2 1]
        simp [paired]
        ring
    have hGd : G.rank ≤ d :=
      (Matrix.rank_conjTranspose_mul_self C).le.trans (by simpa using C.rank_le_card_height)
    omega
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hY
    obtain ⟨N, M, h⟩ := reduce_left (n := 3) Y X g i hi hg
    have hf : (∑ i, kronecker (M i) (N i)) = ∑ i, kronecker (X i) (Y i) := by
      rw [scalar_gram_swap N M, h, ← scalar_gram_swap]
    have h3 := NativeThreeRectangularBound.native_three_rectangular_bound M N lam hlam hab
      (by simpa only [hf] using hF)
    omega

open private compression_mix from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourKernel
open private tensor_mix mixed_energy from D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound

private theorem normalize_rank_three {a b c d : ℕ}
    (X : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
    (hc : 0 < c) (hY : LinearIndependent ℂ Y)
    (hF : (∑ i, kronecker (X i) (Y i))ᴴ * (∑ i, kronecker (X i) (Y i)) = 1)
    (T : Matrix (Fin 4) (Fin 4) ℂ) (hT : T.IsHermitian)
    (hcomp : NativeFourKernel.compression X T = 0) (hrank : T.rank = 3) :
    ∃ (A : Fin 4 → Matrix (Fin a) (Fin b) ℂ) (B : Fin 4 → Matrix (Fin d) (Fin c) ℂ)
      (e : Fin 4 → ℝ),
      (∑ i, kronecker (A i) (B i))ᴴ * (∑ i, kronecker (A i) (B i)) = 1 ∧
      (∑ i, (A i)ᴴ * A i) = 1 ∧
      NativeFourKernel.compression A (diagonal (fun i => (e i : ℂ))) = 0 ∧
      (diagonal (fun i => (e i : ℂ))).rank = 3 := by
  classical
  obtain ⟨P, hP, _, hFmix, hGram, _⟩ := NativeRectangularBound.exact_whitening X Y hY hc hF
  let L := mix P X
  let R := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix P.transpose⁻¹ Y
  let Q := (P⁻¹)ᴴ * T * P⁻¹
  have hPi : IsUnit P⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have hQ : Q.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul _ hT
  have hQr : Q.rank = 3 := by
    change ((P⁻¹)ᴴ * T * P⁻¹).rank = 3
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hPi),
      Matrix.rank_mul_eq_right_of_isUnit_det (P⁻¹)ᴴ T
        ((Matrix.isUnit_iff_isUnit_det _).mp hPi.star), hrank]
  let U : Matrix (Fin 4) (Fin 4) ℂ := hQ.eigenvectorUnitary
  let e := hQ.eigenvalues
  let D := diagonal (fun i => (e i : ℂ))
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hd : Uᴴ * Q * U = D := by
    have h := hQ.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at h
    with_unfolding_all exact h
  have hUd : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det _).mp Unitary.isUnit_coe
  have hUD : U * D * Uᴴ = Q := by
    rw [← hd]
    calc
      U * (Uᴴ * Q * U) * Uᴴ = (U * Uᴴ) * Q * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Q := by rw [hU', Matrix.one_mul, Matrix.mul_one]
  have hDr : D.rank = 3 := by
    rw [← hd, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUd,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by simpa [Matrix.det_conjTranspose] using hUd.star),
      hQr]
  let A := mix Uᴴ L
  let B := D5.S3.Quantum.Algebra.NativeCoefficientWhitening.mix Uᵀ R
  have hpres : (∑ i, kronecker (A i) (B i)) = ∑ i, kronecker (L i) (R i) := by
    apply tensor_mix
    rw [← Matrix.transpose_mul, hU', Matrix.transpose_one]
  have hAnorm : ∑ i, (A i)ᴴ * A i = 1 := by
    change ∑ i, (mix Uᴴ L i)ᴴ * mix Uᴴ L i = 1
    rw [mixed_energy, Matrix.conjTranspose_conjTranspose, hU']
    simpa [Matrix.one_apply, ite_smul] using hGram
  have hPC : Pᴴ * Q * P = T := by
    have hI : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)
    have hI' : Pᴴ * (P⁻¹)ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose hI
    calc
      Pᴴ * Q * P = (Pᴴ * (P⁻¹)ᴴ) * T * (P⁻¹ * P) := by simp only [Q, Matrix.mul_assoc]
      _ = T := by rw [hI', hI, Matrix.one_mul, Matrix.mul_one]
  refine ⟨A, B, e, ?_, hAnorm, ?_, hDr⟩
  · rw [hpres, show (∑ i, kronecker (L i) (R i)) = _ from hFmix, hF]
  · change NativeFourKernel.compression (mix Uᴴ (mix P X)) D = 0
    rw [compression_mix, Matrix.conjTranspose_conjTranspose, hUD, compression_mix, hPC]
    exact hcomp
end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeFourCliffordRankThree
