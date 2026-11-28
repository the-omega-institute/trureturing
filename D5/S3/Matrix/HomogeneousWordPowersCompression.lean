/- GID: D5/S3/Matrix/HomogeneousWordPowersCompression
   generality: G
   mirror-B: none(waiver:covered-by-shitov-size-three-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Word estimates in coordinates adapted to a size-three plane-to-line compression. -/

import D5.S3.Matrix.HomogeneousWordPowersAlternating
import D5.S3.Matrix.HomogeneousWordPowersSingular
import Mathlib.LinearAlgebra.Basis.Fin

/-! Omega original.

Word estimates in coordinates adapted to a size-three plane-to-line compression. -/

compile_only_with_mathlib

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace OmegaMath.HomogeneousWordPowers

variable {K : Type*} [Field K]

local notation "Mat" => Matrix (Fin 3) (Fin 3) K

private def compressionMatrix (a : K) (i : Fin 2) : Mat :=
  !![a, if i = 0 then 1 else 0, if i = 1 then 1 else 0;
     if i = 0 then 1 else 0, 0, 0;
     if i = 1 then 1 else 0, 0, 0]

private def pairingMatrix (T : Matrix (Fin 2) (Fin 2) K) : Mat :=
  !![1, 0, 0; 0, T 0 0, T 0 1; 0, T 1 0, T 1 1]

private theorem pairingMatrix_det (T : Matrix (Fin 2) (Fin 2) K) :
    (pairingMatrix T).det = T.det := by
  simp [pairingMatrix, Matrix.det_fin_three, Matrix.det_fin_two]

private theorem compressionPair_det (T : Matrix (Fin 2) (Fin 2) K)
    (a : Fin 2 → K) (x y z w : K) :
    (x • (compressionMatrix (a 0) 0 * pairingMatrix T * compressionMatrix (a 0) 0) +
      y • (compressionMatrix (a 0) 0 * pairingMatrix T * compressionMatrix (a 1) 1) +
      z • (compressionMatrix (a 1) 1 * pairingMatrix T * compressionMatrix (a 0) 0) +
      w • (compressionMatrix (a 1) 1 * pairingMatrix T * compressionMatrix (a 1) 1)).det =
      (x * T 0 0 + y * T 0 1 + z * T 1 0 + w * T 1 1) * (x * w - y * z) := by
  simp [compressionMatrix, pairingMatrix, Matrix.det_fin_three]
  ring

/-- Two compressed generators with independent rows and columns in the plane
give a unit in the square. The first entry of each generator is arbitrary. -/
private theorem exists_unit_mem_square_of_compression_generators [NeZero (2 : K)]
    (L : Submodule K Mat) (T : Matrix (Fin 2) (Fin 2) K) (hT : T.det ≠ 0)
    (a : Fin 2 → K) (h : ∀ i, compressionMatrix (a i) i * pairingMatrix T ∈ L) :
    ∃ U : Matˣ, (U : Mat) ∈ L ^ 2 := by
  have hG : (pairingMatrix T).det ≠ 0 := by rwa [pairingMatrix_det]
  let P (i j : Fin 2) : Mat :=
    (compressionMatrix (a i) i * pairingMatrix T) *
      (compressionMatrix (a j) j * pairingMatrix T)
  have hP (i j : Fin 2) : P i j ∈ L ^ 2 := by
    simpa [P, pow_two] using Submodule.mul_mem_mul (h i) (h j)
  let W (x y z w : K) := x • P 0 0 + y • P 0 1 + z • P 1 0 + w • P 1 1
  have hw (x y z w : K) : W x y z w ∈ L ^ 2 :=
    (L ^ 2).add_mem ((L ^ 2).add_mem ((L ^ 2).add_mem
      ((L ^ 2).smul_mem x (hP 0 0)) ((L ^ 2).smul_mem y (hP 0 1)))
      ((L ^ 2).smul_mem z (hP 1 0))) ((L ^ 2).smul_mem w (hP 1 1))
  have hdet (x y z w : K) : (W x y z w).det =
      (x * T 0 0 + y * T 0 1 + z * T 1 0 + w * T 1 1) *
        (x * w - y * z) * (pairingMatrix T).det := by
    dsimp only [W, P]
    simp only [← mul_assoc, ← smul_mul_assoc, ← add_mul, Matrix.det_mul]
    simp only [smul_mul_assoc, compressionPair_det]
  have hex (x y z w : K) (hl : x * T 0 0 + y * T 0 1 + z * T 1 0 + w * T 1 1 ≠ 0)
      (hn : x * w - y * z ≠ 0) : ∃ U : Matˣ, (U : Mat) ∈ L ^ 2 := by
    have hd : (W x y z w).det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero (mul_ne_zero hl hn) hG
    obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd.isUnit
    exact ⟨U, hU ▸ hw x y z w⟩
  by_cases hd : T 0 0 + T 1 1 = 0
  · by_cases h01 : T 0 1 = 0
    · by_cases h10 : T 1 0 = 0
      · have h00 : T 0 0 ≠ 0 := by
          intro hz
          exact hT (by simp [Matrix.det_fin_two, hz, h01])
        apply hex 2 0 0 1
        · have he : 2 * T 0 0 + T 1 1 = T 0 0 := by linear_combination hd
          simpa [he] using h00
        · simpa using (two_ne_zero : (2 : K) ≠ 0)
      · apply hex 1 0 1 1 _ (by simp)
        have he : T 0 0 + T 1 0 + T 1 1 = T 1 0 := by linear_combination hd
        simpa [he] using h10
    · apply hex 1 1 0 1 _ (by simp)
      have he : T 0 0 + T 0 1 + T 1 1 = T 0 1 := by linear_combination hd
      simpa [he] using h01
  · exact hex 1 0 0 1 (by simpa using hd) (by simp)

private def compressionTriple (T : Matrix (Fin 2) (Fin 2) K)
    (a : Fin 2 → K) (i j k : Fin 2) : Mat :=
  compressionMatrix (a i) i * pairingMatrix T * compressionMatrix (a j) j *
    pairingMatrix T * compressionMatrix (a k) k

private theorem compressionTriple_plane (T : Matrix (Fin 2) (Fin 2) K)
    (a : Fin 2 → K) (i j k r c : Fin 2) :
    compressionTriple T a i j k r.succ c.succ =
      if i = r ∧ k = c then a j else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r <;> fin_cases c <;>
    simp [compressionTriple, compressionMatrix, pairingMatrix]

private theorem compressionTriple_row (T : Matrix (Fin 2) (Fin 2) K)
    (a : Fin 2 → K) (i k c : Fin 2) (ha : a 1 = 0) :
    compressionTriple T a i 1 k 0 c.succ = if k = c then T i 1 else 0 := by
  fin_cases i <;> fin_cases k <;> fin_cases c <;>
    simp [compressionTriple, compressionMatrix, pairingMatrix, ha]

private theorem compressionTriple_col (T : Matrix (Fin 2) (Fin 2) K)
    (a : Fin 2 → K) (i k r : Fin 2) (ha : a 1 = 0) :
    compressionTriple T a i 1 k r.succ 0 = if i = r then T 1 k else 0 := by
  fin_cases i <;> fin_cases k <;> fin_cases r <;>
    simp [compressionTriple, compressionMatrix, pairingMatrix, ha]

private theorem compressionTriples_linearIndependent (T : Matrix (Fin 2) (Fin 2) K)
    (a : Fin 2 → K) (ha₀ : a 0 = 1) (ha₁ : a 1 = 0)
    {i₀ i₁ k₀ k₁ : Fin 2} (hi : i₁ ≠ i₀) (hk : k₁ ≠ k₀)
    (hicol : T i₀ 1 ≠ 0) (hkrow : T 1 k₀ ≠ 0) :
    LinearIndependent K (![compressionTriple T a 0 0 0, compressionTriple T a 0 0 1,
      compressionTriple T a 1 0 0, compressionTriple T a 1 0 1,
      compressionTriple T a i₀ 1 k₀, compressionTriple T a i₁ 1 k₀,
      compressionTriple T a i₀ 1 k₁] : Fin 7 → Mat) := by
  apply Fintype.linearIndependent_iff.2
  intro g hg
  have he (r c : Fin 3) := congr_fun (congr_fun hg r) c
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ] at he
  have hplane (r c : Fin 2) := he r.succ c.succ
  simp only [compressionTriple_plane, ha₀, ha₁, ite_self, mul_zero, add_zero]
    at hplane
  have h0 : g 0 = 0 := by simpa using hplane 0 0
  have h1 : g 1 = 0 := by simpa using hplane 0 1
  have h2 : g 2 = 0 := by simpa using hplane 1 0
  have h3 : g 3 = 0 := by simpa using hplane 1 1
  have h6 : g 6 = 0 := by
    have h := he 0 k₁.succ
    simp [h0, h1, h2, h3, compressionTriple_row, ha₁, hk.symm] at h
    exact h.resolve_right hicol
  have h5 : g 5 = 0 := by
    have h := he i₁.succ 0
    simp [h0, h1, h2, h3, h6, compressionTriple_col, ha₁, hi.symm] at h
    exact h.resolve_right hkrow
  have h4 : g 4 = 0 := by
    have h := he 0 k₀.succ
    simp [h0, h1, h2, h3, h5, h6, compressionTriple_row, ha₁] at h
    exact h.resolve_right hicol
  intro n
  fin_cases n
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- Seven independent cubic words from two compressed generators whose first
entries are one and zero and whose planar pairing is nonsingular. -/
private theorem seven_le_finrank_cube_of_compression_generators
    (L : Submodule K Mat) (T : Matrix (Fin 2) (Fin 2) K) (hT : T.det ≠ 0)
    (a : Fin 2 → K) (ha₀ : a 0 = 1) (ha₁ : a 1 = 0)
    (h : ∀ i, compressionMatrix (a i) i * pairingMatrix T ∈ L) :
    7 ≤ Module.finrank K ↥(L ^ 3) := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin 2, T i 1 ≠ 0 := by
    by_contra! hz
    exact hT (by simp [Matrix.det_fin_two, hz])
  obtain ⟨k₀, hk₀⟩ : ∃ k : Fin 2, T 1 k ≠ 0 := by
    by_contra! hz
    exact hT (by simp [Matrix.det_fin_two, hz])
  let i₁ := i₀ + 1
  let k₁ := k₀ + 1
  have hi : i₁ ≠ i₀ := by fin_cases i₀ <;> decide
  have hk : k₁ ≠ k₀ := by fin_cases k₀ <;> decide
  have hG : (pairingMatrix T).det ≠ 0 := by rwa [pairingMatrix_det]
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hG.isUnit
  let q : Fin 7 → Mat := ![compressionTriple T a 0 0 0, compressionTriple T a 0 0 1,
    compressionTriple T a 1 0 0, compressionTriple T a 1 0 1,
    compressionTriple T a i₀ 1 k₀, compressionTriple T a i₁ 1 k₀,
    compressionTriple T a i₀ 1 k₁]
  have hq : LinearIndependent K q :=
    compressionTriples_linearIndependent T a ha₀ ha₁ hi hk hi₀ hk₀
  let e := G.mulRightLinearEquiv K
  have hind : LinearIndependent K (e ∘ q) := hq.map' e.toLinearMap (by simp)
  have hw (i j k : Fin 2) : e (compressionTriple T a i j k) ∈ L ^ 3 := by
    change compressionTriple T a i j k * (G : Mat) ∈ L ^ 3
    rw [hG]
    simpa only [compressionTriple, mul_assoc, show (3 : ℕ) = 2 + 1 from rfl,
      pow_add, pow_two, pow_one] using
      Submodule.mul_mem_mul (Submodule.mul_mem_mul (h i) (h j)) (h k)
  have hle : Submodule.span K (Set.range (e ∘ q)) ≤ L ^ 3 := by
    apply Submodule.span_le.2
    rintro _ ⟨n, rfl⟩
    fin_cases n <;> exact hw _ _ _
  simpa [finrank_span_eq_card hind] using Submodule.finrank_mono hle

private theorem compression_plane_entries (L : Submodule K Mat)
    (hzero : ∀ B ∈ L, ∀ i j : Fin 2, B i.succ j.succ = 0)
    {B : Mat} (hB : B ∈ L) :
    B 1 1 = 0 ∧ B 1 2 = 0 ∧ B 2 1 = 0 ∧ B 2 2 = 0 :=
  ⟨hzero B hB 0 0, hzero B hB 0 1, hzero B hB 1 0, hzero B hB 1 1⟩

private theorem exists_nonzero_corner [NeZero (2 : K)] (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hzero : ∀ B ∈ L, ∀ i j : Fin 2, B i.succ j.succ = 0) :
    ∃ B ∈ L, B 0 0 ≠ 0 := by
  by_contra! h
  let J : Mat := Matrix.diagonal ![(1 : K), -1, -1]
  have hanti (B : Mat) (hB : B ∈ L) : J * B = -(B * J) := by
    apply Matrix.ext
    intro i j
    obtain ⟨h11, h12, h21, h22⟩ := compression_plane_entries L hzero hB
    have h00 := h B hB
    fin_cases i <;> fin_cases j <;>
      simp [J, Matrix.diagonal_mul, Matrix.mul_diagonal, h00, h11, h12, h21, h22]
  have hp (m : ℕ) (B : Mat) (hB : B ∈ L ^ m) :
      J * B = ((-1 : K) ^ m) • (B * J) := by
    induction m generalizing B with
    | zero =>
      rw [pow_zero] at hB ⊢
      obtain ⟨x, rfl⟩ := Submodule.mem_one.mp hB
      rw [Algebra.algebraMap_eq_smul_one]
      simp
    | succ m ih =>
      rw [pow_succ] at hB
      refine Submodule.mul_induction_on hB ?_ ?_
      · intro X hX Y hY
        calc
          J * (X * Y) = (J * X) * Y := by rw [mul_assoc]
          _ = ((-1 : K) ^ m) • (X * (J * Y)) := by
            rw [ih X hX, smul_mul_assoc, mul_assoc]
          _ = ((-1 : K) ^ (m + 1)) • (X * Y * J) := by
            rw [hanti Y hY, mul_neg, ← mul_assoc, pow_succ, mul_smul, neg_one_smul]
      · intro X Y hX hY
        simp [mul_add, add_mul, smul_add, hX, hY]
  obtain ⟨m, _, hm⟩ := hfull
  have ht (B : Mat) : J * B = ((-1 : K) ^ m) • (B * J) :=
    hp m B (hm.symm ▸ Submodule.mem_top)
  have hsign : (-1 : K) ^ m = 1 := by
    have he := congr_fun (congr_fun (ht 1) (0 : Fin 3)) (0 : Fin 3)
    simpa [J] using he.symm
  have he := congr_fun (congr_fun (ht (Matrix.single 0 1 1)) (0 : Fin 3)) (1 : Fin 3)
  have hneg : (1 : K) = -1 := by simpa [hsign, J, Matrix.mul_diagonal] using he
  exact (two_ne_zero : (2 : K) ≠ 0) (by linear_combination hneg)

private theorem compression_generators_of_zero_plane_block [Infinite K] [NeZero (2 : K)]
    (L : Submodule K Mat) (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hzero : ∀ B ∈ L, ∀ i j : Fin 2, B i.succ j.succ = 0) :
    ∃ X ∈ L, ∃ Y ∈ L, X 0 0 = 1 ∧ Y 0 0 = 0 ∧
      (X 1 0 * Y 2 0 - X 2 0 * Y 1 0 ≠ 0) ∧
      (X 0 1 * Y 0 2 - X 0 2 * Y 0 1 ≠ 0) := by
  let a := Matrix.entryLinearMap K K (0 : Fin 3) (0 : Fin 3)
  let c₁ := Matrix.entryLinearMap K K (1 : Fin 3) (0 : Fin 3)
  let c₂ := Matrix.entryLinearMap K K (2 : Fin 3) (0 : Fin 3)
  let r₁ := Matrix.entryLinearMap K K (0 : Fin 3) (1 : Fin 3)
  let r₂ := Matrix.entryLinearMap K K (0 : Fin 3) (2 : Fin 3)
  obtain ⟨hk, hl⟩ := eventually_full_reduced L hfull
  have hcol (s t : K) (h : ∀ B ∈ L, s * B 1 0 + t * B 2 0 = 0) :
      s = 0 ∧ t = 0 := by
    have hv := hl ![0, s, t] (by
      intro B hB
      obtain ⟨h11, h12, h21, h22⟩ := compression_plane_entries L hzero hB
      ext i
      fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three,
        h B hB, h11, h12, h21, h22])
    exact ⟨congr_fun hv 1, congr_fun hv 2⟩
  have hrow (s t : K) (h : ∀ B ∈ L, s * B 0 1 + t * B 0 2 = 0) :
      s = 0 ∧ t = 0 := by
    have hv := hk ![0, s, t] (by
      intro B hB
      obtain ⟨h11, h12, h21, h22⟩ := compression_plane_entries L hzero hB
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm,
          h B hB, h11, h12, h21, h22])
    exact ⟨congr_fun hv 1, congr_fun hv 2⟩
  let forms : Fin 3 → Module.Dual K Mat := ![a, c₁, r₁]
  have hforms : ∀ i, ∃ B ∈ L, forms i B ≠ 0 := by
    intro i
    fin_cases i
    · exact exists_nonzero_corner L hfull hzero
    · by_contra! hn
      exact one_ne_zero (hcol 1 0 (by simpa [forms, c₁] using hn)).1
    · by_contra! hn
      exact one_ne_zero (hrow 1 0 (by simpa [forms, r₁] using hn)).1
  obtain ⟨B, hB, hBn⟩ :=
    Module.Dual.exists_forall_mem_ne_zero_of_forall_exists L forms hforms
  have hBa : B 0 0 ≠ 0 := hBn 0
  have hBc : B 1 0 ≠ 0 := hBn 1
  have hBr : B 0 1 ≠ 0 := hBn 2
  let X := (B 0 0)⁻¹ • B
  have hX : X ∈ L := L.smul_mem _ hB
  have ha : X 0 0 = 1 := by simp [X, hBa]
  have hc : X 1 0 ≠ 0 := by simp [X, hBa, hBc]
  have hr : X 0 1 ≠ 0 := by simp [X, hBa, hBr]
  let f : Module.Dual K Mat := X 1 0 • c₂ - X 2 0 • c₁
  let g : Module.Dual K Mat := X 0 1 • r₂ - X 0 2 • r₁
  have hf (Z : Mat) : f Z = X 1 0 * Z 2 0 - X 2 0 * Z 1 0 := by simp [f, c₁, c₂]
  have hg (Z : Mat) : g Z = X 0 1 * Z 0 2 - X 0 2 * Z 0 1 := by simp [g, r₁, r₂]
  have hlin : ∀ i : Fin 2, ∃ Z ∈ L, (![f, g] : Fin 2 → Module.Dual K Mat) i Z ≠ 0 := by
    intro i
    fin_cases i
    · by_contra! hn
      apply hc
      apply (hcol (-X 2 0) (X 1 0) ?_).2
      intro Z hZ
      have h := hn Z hZ
      change f Z = 0 at h
      rw [hf] at h
      linear_combination h
    · by_contra! hn
      apply hr
      apply (hrow (-X 0 2) (X 0 1) ?_).2
      intro Z hZ
      have h := hn Z hZ
      change g Z = 0 at h
      rw [hg] at h
      linear_combination h
  obtain ⟨Z, hZ, hZn⟩ :=
    Module.Dual.exists_forall_mem_ne_zero_of_forall_exists L ![f, g] hlin
  let Y := Z - Z 0 0 • X
  refine ⟨X, hX, Y, L.sub_mem hZ (L.smul_mem _ hX), ha, by simp [Y, ha], ?_, ?_⟩
  · have hfx : f X = 0 := by rw [hf, mul_comm (X 1 0), sub_self]
    rw [← hf]
    simpa [Y, hfx] using (show f Z ≠ 0 from hZn 0)
  · have hgx : g X = 0 := by rw [hg, mul_comm (X 0 1), sub_self]
    rw [← hg]
    simpa [Y, hgx] using (show g Z ≠ 0 from hZn 1)

private theorem transport_compression_estimates (e : Mat ≃ₐ[K] Mat)
    (L : Submodule K Mat)
    (h : ∃ U : Matˣ, (U : Mat) ∈ (L.map e.toLinearMap) ^ 2 ∧
      7 ≤ Module.finrank K ↥((L.map e.toLinearMap) ^ 3)) :
    ∃ U : Matˣ, (U : Mat) ∈ L ^ 2 ∧ 7 ≤ Module.finrank K ↥(L ^ 3) := by
  obtain ⟨U, hU, hdim⟩ := h
  have hpow (n : ℕ) : (L ^ n).map e.toLinearMap = (L.map e.toLinearMap) ^ n :=
    Submodule.map_pow L e.toAlgHom n
  refine ⟨Units.map e.symm.toMonoidHom U, ?_, ?_⟩
  · rw [← hpow] at hU
    obtain ⟨X, hX, he⟩ := Submodule.mem_map.mp hU
    change e.symm (U : Mat) ∈ L ^ 2
    change e X = _ at he
    simpa [← he] using hX
  · rwa [← hpow, e.toLinearEquiv.finrank_map_eq] at hdim

private def compressionBasisChange (S : Matˣ) : Mat ≃ₐ[K] Mat where
  __ := (S⁻¹.mulLeftLinearEquiv K Mat).trans (S.mulRightLinearEquiv K)
  map_mul' X Y := by
    change (↑S⁻¹ : Mat) * (X * Y) * (S : Mat) =
      ((↑S⁻¹ : Mat) * X * (S : Mat)) * ((↑S⁻¹ : Mat) * Y * (S : Mat))
    calc
      _ = (↑S⁻¹ : Mat) * (X * (((S : Mat) * (↑S⁻¹ : Mat)) * Y)) * (S : Mat) := by
        rw [Units.mul_inv, one_mul]
      _ = _ := by simp only [mul_assoc]
  commutes' c := by
    change (↑S⁻¹ : Mat) * algebraMap K Mat c * (S : Mat) = _
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Units.inv_mul]

private theorem compression_estimates_of_zero_plane_block [Infinite K] [NeZero (2 : K)]
    (L : Submodule K Mat) (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hzero : ∀ B ∈ L, ∀ i j : Fin 2, B i.succ j.succ = 0) :
    ∃ U : Matˣ, (U : Mat) ∈ L ^ 2 ∧ 7 ≤ Module.finrank K ↥(L ^ 3) := by
  obtain ⟨X, hX, Y, hY, hx, hy, hcol, hrow⟩ :=
    compression_generators_of_zero_plane_block L hfull hzero
  let C : Matrix (Fin 2) (Fin 2) K := !![X 1 0, Y 1 0; X 2 0, Y 2 0]
  let R : Matrix (Fin 2) (Fin 2) K := !![X 0 1, X 0 2; Y 0 1, Y 0 2]
  let T := R * C
  have hT : T.det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (by simpa [R, Matrix.det_fin_two] using hrow)
      (by simpa [C, Matrix.det_fin_two, mul_comm] using hcol)
  have hc : (pairingMatrix C).det ≠ 0 := by
    rw [pairingMatrix_det]
    simpa [C, Matrix.det_fin_two, mul_comm] using hcol
  obtain ⟨S, hS⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hc.isUnit
  let e := compressionBasisChange S
  let M := L.map e.toLinearMap
  let a : Fin 2 → K := ![1, 0]
  have he (B Z : Mat) (h : B * pairingMatrix C = pairingMatrix C * Z) :
      e B = Z := by
    change (↑S⁻¹ : Mat) * B * (S : Mat) = Z
    rw [mul_assoc, hS, h, ← hS, ← mul_assoc, Units.inv_mul, one_mul]
  have hx' : e X = compressionMatrix (a 0) 0 * pairingMatrix T := by
    apply he
    obtain ⟨h11, h12, h21, h22⟩ := compression_plane_entries L hzero hX
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a, compressionMatrix, pairingMatrix, T, R, C, hx, h11, h12, h21, h22,
        Matrix.mul_apply, Fin.sum_univ_three]
  have hy' : e Y = compressionMatrix (a 1) 1 * pairingMatrix T := by
    apply he
    obtain ⟨h11, h12, h21, h22⟩ := compression_plane_entries L hzero hY
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a, compressionMatrix, pairingMatrix, T, R, C, hy, h11, h12, h21, h22,
        Matrix.mul_apply, Fin.sum_univ_three]
  have hm (i : Fin 2) : compressionMatrix (a i) i * pairingMatrix T ∈ M := by
    fin_cases i
    · exact Submodule.mem_map.mpr ⟨X, hX, hx'⟩
    · exact Submodule.mem_map.mpr ⟨Y, hY, hy'⟩
  obtain ⟨U, hU⟩ := exists_unit_mem_square_of_compression_generators M T hT a hm
  exact transport_compression_estimates e L ⟨U, hU,
    seven_le_finrank_cube_of_compression_generators M T hT a rfl rfl hm⟩

private theorem compression_line_not_le_plane (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (H D : Submodule K (Fin 3 → K))
    (hD : Module.finrank K D = 1)
    (hmap : ∀ B ∈ L, ∀ v ∈ H, B *ᵥ v ∈ D) : ¬ D ≤ H := by
  intro hle
  have hne : D ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hD
    omega
  obtain ⟨d, hd, hdne⟩ := D.ne_bot_iff.mp hne
  obtain ⟨m, _, hm⟩ := hfull
  have hall (B : Mat) : ∀ v ∈ D, B *ᵥ v ∈ D := by
    have hB : B ∈ L ^ m := hm.symm ▸ Submodule.mem_top
    refine Submodule.pow_induction_on_left L
      (C := fun B => ∀ v ∈ D, B *ᵥ v ∈ D) ?_ ?_ ?_ hB
    · intro r v hv
      simpa [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec] using D.smul_mem r hv
    · intro X Y hX hY v hv
      rw [Matrix.add_mulVec]
      exact D.add_mem (hX v hv) (hY v hv)
    · intro X hX Y hY v hv
      rw [← Matrix.mulVec_mulVec]
      exact hmap X hX _ (hle (hY v hv))
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hdne
  have ht : D = ⊤ := by
    apply top_unique
    intro v _
    let B : Mat := Matrix.vecMulVec ((d j)⁻¹ • v) (Pi.single j 1)
    have hB : B *ᵥ d = v := by
      dsimp only [B]
      rw [Matrix.vecMulVec_mulVec, single_dotProduct, one_mul]
      ext i
      change (d j)⁻¹ * v i * d j = v i
      rw [mul_right_comm, inv_mul_cancel₀ hj, one_mul]
    exact hB ▸ hall B d hd
  rw [ht, finrank_top] at hD
  have hdim : Module.finrank K (Fin 3 → K) = 3 := by simp
  omega

/-- An eventually full size-three space mapping a plane into a line has a unit
in its square and a cube of dimension at least seven. -/
theorem compression_word_estimates [Infinite K] [NeZero (2 : K)]
    (L : Submodule K Mat) (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (H D : Submodule K (Fin 3 → K))
    (hH : Module.finrank K H = 2) (hD : Module.finrank K D = 1)
    (hmap : ∀ B ∈ L, ∀ v ∈ H, B *ᵥ v ∈ D) :
    ∃ U : Matˣ, (U : Mat) ∈ L ^ 2 ∧ 7 ≤ Module.finrank K ↥(L ^ 3) := by
  classical
  obtain ⟨d, hd, hdH⟩ : ∃ d ∈ D, d ∉ H := by
    by_contra! h
    exact compression_line_not_le_plane L hfull H D hD hmap h
  have hdne : d ≠ 0 := fun h => hdH (h ▸ H.zero_mem)
  have hspan : D = Submodule.span K ({d} : Set (Fin 3 → K)) := by
    symm
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hd)
    rw [finrank_span_singleton hdne, hD]
  have hsup : H ⊔ D = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hspan, Submodule.finrank_sup_span_singleton hdH, hH]
    simp
  have hli (c : K) (x : Fin 3 → K) (hx : x ∈ H) (he : c • d + x = 0) : c = 0 := by
    by_contra hn
    have hcd : c • d ∈ H := (eq_neg_of_add_eq_zero_left he) ▸ H.neg_mem hx
    exact hdH ((Submodule.smul_mem_iff H hn).mp hcd)
  have hsp (z : Fin 3 → K) : ∃ c : K, z + c • d ∈ H := by
    have hz : z ∈ H ⊔ D := hsup.symm ▸ Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [hspan, Submodule.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    exact ⟨-c, by simpa [neg_smul, add_assoc] using hx⟩
  let b := Module.Basis.mkFinCons d (Module.finBasisOfFinrankEq K H hH) hli hsp
  let e : Mat ≃ₐ[K] Mat := Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)
  have hb₀ : b 0 = d := by simp [b]
  have hb (j : Fin 2) : b j.succ ∈ H := by simp [b]
  let M := L.map e.toLinearMap
  have hfullM : ∃ m : ℕ, 0 < m ∧ M ^ m = ⊤ := by
    obtain ⟨m, hp, hm⟩ := hfull
    refine ⟨m, hp, ?_⟩
    change L.map e.toAlgHom.toLinearMap ^ m = ⊤
    rw [← Submodule.map_pow, hm, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  have hzero (B : Mat) (hB : B ∈ M) (i j : Fin 2) : B i.succ j.succ = 0 := by
    obtain ⟨A, hA, rfl⟩ := Submodule.mem_map.mp hB
    change LinearMap.toMatrixAlgEquiv b (Matrix.toLinAlgEquiv' A) i.succ j.succ = 0
    rw [LinearMap.toMatrixAlgEquiv_apply, Matrix.toLinAlgEquiv'_apply]
    have hv := hmap A hA (b j.succ) (hb j)
    rw [hspan, Submodule.mem_span_singleton] at hv
    obtain ⟨c, hc⟩ := hv
    rw [← hc, ← hb₀]
    simp
  exact transport_compression_estimates e L
    (compression_estimates_of_zero_plane_block M hfullM hzero)

/-- Linear estimates close either the alternating-square branch or the compression
    certificate branch of the size-three singular classification. -/
private theorem pow_seven_eq_top_of_singular_alternatives
    (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (halt : (L ^ 2 = ⊤) ∨
      (∃ U : Matˣ, (U : Mat) ∈ L ^ 2 ∧
        7 ≤ Module.finrank K ↥(L ^ 3))) :
    L ^ 7 = ⊤ := by
  rcases halt with hsq | ⟨U, hU, hdim⟩
  · exact pow_eq_top_of_le L (by decide) hsq (by decide)
  by_cases h3 : L ^ 3 = ⊤
  · exact pow_eq_top_of_le L (by decide) h3 (by decide)
  by_cases h5 : L ^ 5 = ⊤
  · exact pow_eq_top_of_le L (by decide) h5 (by decide)
  have hg3 := finrank_pow_lt_of_unit_mem L 3 2 U hfull (by decide) hU h3
  have hg5 := finrank_pow_lt_of_unit_mem L 5 2 U hfull (by decide) hU h5
  have hdim7 : 9 ≤ Module.finrank K ↥(L ^ 7) := by
    have h3le : 7 ≤ Module.finrank K ↥(L ^ 3) := hdim
    have h5le : Module.finrank K ↥(L ^ 5) ≥ Module.finrank K ↥(L ^ 3) + 1 := by
      have hg3' : Module.finrank K ↥(L ^ 3) < Module.finrank K ↥(L ^ 5) := by
        simpa using hg3
      omega
    have h7le : Module.finrank K ↥(L ^ 7) ≥ Module.finrank K ↥(L ^ 5) + 1 := by
      have hg5' : Module.finrank K ↥(L ^ 5) < Module.finrank K ↥(L ^ 7) := by
        simpa using hg5
      omega
    omega
  apply Submodule.eq_of_le_of_finrank_le le_top
  simpa [Module.finrank_matrix] using hdim7

/-- An all-singular size-three matrix space with a positive full exact power
already has a full seventh power. -/
theorem all_singular_pow_seven_eq_top [Infinite K] [NeZero (2 : K)]
    (L : Submodule K Mat) (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hsing : ∀ B ∈ L, B.det = 0) : L ^ 7 = ⊤ := by
  apply pow_seven_eq_top_of_singular_alternatives L hfull
  rcases singular_space_classification L hfull hsing with
    ⟨H, D, hH, hD, hmap⟩ | ⟨P, Q, hclass⟩
  · exact Or.inr (compression_word_estimates L hfull H D hH hD hmap)
  · exact Or.inl (alternating_left_right_square_eq_top L P Q hclass)

end OmegaMath.HomogeneousWordPowers
