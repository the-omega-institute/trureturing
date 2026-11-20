/- GID: D5/S3/Quantum/Algebra/Unitary/TensorSquareSinglet
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/Unitary/TensorSquareSinglet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two explicit SU(2) elements already fix the four invariant subspaces of C2 tensor C2. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped Matrix Kronecker

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Invariant subspaces of the tensor square of two qubits

For any set `S` of `2 × 2` complex matrices containing the two special unitary matrices
`phaseMatrix` and `rotationMatrix`, the subspaces of `ℂ² ⊗ ℂ²` invariant under every `g ⊗ g`,
`g ∈ S`, are exactly `0`, the singlet line `ℂ ω`, its orthogonal complement (the symmetric
tensors, of dimension three) and the whole space. Taking `S` to be the special unitary group
gives the classification under `SU(2)`; taking `S = {phaseMatrix, rotationMatrix}` shows that
two explicit elements suffice. Moreover `(g ⊗ g) ω = det g • ω` for every `2 × 2` matrix `g`.
-/

namespace D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet

local notation "V" => EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The unnormalized singlet `|01⟩ - |10⟩` of two qubits. -/
def singlet : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun ij => if ij = (0, 1) then 1 else if ij = (1, 0) then -1 else 0)

/-- The vector with coordinates `a, b, c, d` at `|00⟩, |01⟩, |10⟩, |11⟩`. -/
private def vec (a b c d : ℂ) : V := WithLp.toLp 2 (fun ij => ![![a, b], ![c, d]] ij.1 ij.2)

@[simp] private lemma vec_00 (a b c d : ℂ) : vec a b c d (0, 0) = a := rfl
@[simp] private lemma vec_01 (a b c d : ℂ) : vec a b c d (0, 1) = b := rfl
@[simp] private lemma vec_10 (a b c d : ℂ) : vec a b c d (1, 0) = c := rfl
@[simp] private lemma vec_11 (a b c d : ℂ) : vec a b c d (1, 1) = d := rfl

private lemma eta (x : V) : x = vec (x (0, 0)) (x (0, 1)) (x (1, 0)) (x (1, 1)) := by
  refine PiLp.ext fun ij => ?_
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> rfl

private lemma vec_eq_vec {a b c d a' b' c' d' : ℂ} :
    vec a b c d = vec a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro h
    exact ⟨congrArg (· (0, 0)) h, congrArg (· (0, 1)) h, congrArg (· (1, 0)) h,
      congrArg (· (1, 1)) h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

private lemma vec_add (a b c d a' b' c' d' : ℂ) :
    vec a b c d + vec a' b' c' d' = vec (a + a') (b + b') (c + c') (d + d') := by
  rw [eta (vec a b c d + vec a' b' c' d')]
  rfl

private lemma smul_vec (r a b c d : ℂ) : r • vec a b c d = vec (r * a) (r * b) (r * c) (r * d) := by
  rw [eta (r • vec a b c d)]
  rfl

private lemma singlet_eq : singlet = vec 0 1 (-1) 0 := by
  rw [eta singlet]
  rfl

private lemma tensor_vec (g : Matrix (Fin 2) (Fin 2) ℂ) (a b c d : ℂ) :
    (g ⊗ₖ g).toEuclideanLin (vec a b c d) =
      vec (g 0 0 * g 0 0 * a + g 0 0 * g 0 1 * b + g 0 1 * g 0 0 * c + g 0 1 * g 0 1 * d)
        (g 0 0 * g 1 0 * a + g 0 0 * g 1 1 * b + g 0 1 * g 1 0 * c + g 0 1 * g 1 1 * d)
        (g 1 0 * g 0 0 * a + g 1 0 * g 0 1 * b + g 1 1 * g 0 0 * c + g 1 1 * g 0 1 * d)
        (g 1 0 * g 1 0 * a + g 1 0 * g 1 1 * b + g 1 1 * g 1 0 * c + g 1 1 * g 1 1 * d) := by
  rw [eta ((g ⊗ₖ g).toEuclideanLin (vec a b c d)), vec_eq_vec]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, vec] <;> ring


/-- `(g ⊗ g) ω = det g • ω` for every `2 × 2` matrix `g`. -/
private lemma tensor_singlet (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (g ⊗ₖ g).toEuclideanLin singlet = g.det • singlet := by
  rw [singlet_eq, tensor_vec, smul_vec, Matrix.det_fin_two, vec_eq_vec]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- The orthogonal complement of the singlet is the space of symmetric tensors. -/
private lemma mem_orthogonal_iff (x : V) : x ∈ (ℂ ∙ singlet)ᗮ ↔ x (0, 1) = x (1, 0) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, eta x, singlet_eq]
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two, vec]
  constructor <;> intro h <;> linear_combination h

/-- Extraction of the weight components by a diagonal operator with eigenvalues
`α, 1, 1, β` on the standard basis. -/
private lemma extract (T : V →ₗ[ℂ] V) (α β : ℂ) (hα : α ≠ 1) (hβ : β ≠ 1) (hαβ : α ≠ β)
    (hT : ∀ p q r s : ℂ, T (vec p q r s) = vec (α * p) q r (β * s)) (W : Submodule ℂ V)
    (hW : ∀ x ∈ W, T x ∈ W) {p q r s : ℂ} (hx : vec p q r s ∈ W) :
    (p ≠ 0 → vec 1 0 0 0 ∈ W) ∧ (s ≠ 0 → vec 0 0 0 1 ∈ W) ∧ vec 0 q r 0 ∈ W := by
  have hTx := hW _ hx
  rw [hT] at hTx
  have hTTx := hW _ hTx
  rw [hT] at hTTx
  have hα' : α - 1 ≠ 0 := sub_ne_zero.mpr hα
  have hβ' : β - 1 ≠ 0 := sub_ne_zero.mpr hβ
  have hαβ' : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
  refine ⟨fun hp => ?_, fun hs => ?_, ?_⟩
  · have h := W.add_mem (W.add_mem hTTx (W.smul_mem (-(1 + β)) hTx)) (W.smul_mem β hx)
    have h' := W.smul_mem ((α - 1) * (α - β) * p)⁻¹ h
    convert h' using 1
    rw [smul_vec, smul_vec, vec_add, vec_add, smul_vec, vec_eq_vec]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring
  · have h := W.add_mem (W.add_mem hTTx (W.smul_mem (-(1 + α)) hTx)) (W.smul_mem α hx)
    have h' := W.smul_mem ((β - 1) * (β - α) * s)⁻¹ h
    convert h' using 1
    rw [smul_vec, smul_vec, vec_add, vec_add, smul_vec, vec_eq_vec]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring
  · have h := W.add_mem (W.add_mem hTTx (W.smul_mem (-(α + β)) hTx)) (W.smul_mem (α * β) hx)
    have h' := W.smul_mem ((α - 1) * (β - 1))⁻¹ h
    convert h' using 1
    rw [smul_vec, smul_vec, vec_add, vec_add, smul_vec, vec_eq_vec]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring


/-- The diagonal phase matrix with diagonal entries `(3 + 4i)/5` and `(3 - 4i)/5`. -/
def phaseMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(3 + 4 * Complex.I) / 5, 0; 0, (3 - 4 * Complex.I) / 5]

/-- The real rotation matrix with cosine `3/5` and sine `4/5`. -/
def rotationMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![3 / 5, -4 / 5; 4 / 5, 3 / 5]

/-- `phaseMatrix ⊗ phaseMatrix` is diagonal with eigenvalues `α, 1, 1, β`, `α ≠ β`, `α, β ≠ 1`. -/
private lemma tensor_phase (p q r s : ℂ) :
    (phaseMatrix ⊗ₖ phaseMatrix).toEuclideanLin (vec p q r s) =
      vec ((-7 + 24 * Complex.I) / 25 * p) q r ((-7 - 24 * Complex.I) / 25 * s) := by
  rw [tensor_vec, vec_eq_vec]
  simp only [phaseMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (16 / 25 * p) * Complex.I_sq
  · linear_combination (-16 / 25 * q) * Complex.I_sq
  · linear_combination (-16 / 25 * r) * Complex.I_sq
  · linear_combination (16 / 25 * s) * Complex.I_sq

private lemma tensor_rotation (p q r s : ℂ) :
    (rotationMatrix ⊗ₖ rotationMatrix).toEuclideanLin (vec p q r s) =
      vec ((9 * p - 12 * q - 12 * r + 16 * s) / 25) ((12 * p + 9 * q - 16 * r - 12 * s) / 25)
        ((12 * p - 16 * q + 9 * r - 12 * s) / 25) ((16 * p + 12 * q + 12 * r + 9 * s) / 25) := by
  rw [tensor_vec, vec_eq_vec]
  simp only [rotationMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

private lemma phase_mem : phaseMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff,
        Complex.conj_ofNat] <;>
      norm_num
  · rw [phaseMatrix, Matrix.det_fin_two_of]
    linear_combination (-16 / 25 : ℂ) * Complex.I_sq

private lemma rotation_mem : rotationMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_ofNat] <;> norm_num
  · rw [rotationMatrix, Matrix.det_fin_two_of]
    norm_num


/-- Every `g ⊗ g` preserves each of the four subspaces `⊥`, `ℂ ∙ ω`, `(ℂ ∙ ω)ᗮ`, `⊤`. -/
private lemma tensor_mem (g : Matrix (Fin 2) (Fin 2) ℂ) {W : Submodule ℂ V}
    (hW : W = ⊥ ∨ W = ℂ ∙ singlet ∨ W = (ℂ ∙ singlet)ᗮ ∨ W = ⊤) {x : V} (hx : x ∈ W) :
    (g ⊗ₖ g).toEuclideanLin x ∈ W := by
  rcases hW with rfl | rfl | rfl | rfl
  · rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, tensor_singlet, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self singlet)
  · rw [mem_orthogonal_iff] at hx ⊢
    rw [eta x, tensor_vec, vec_01, vec_10, hx]
    ring
  · exact Submodule.mem_top

private lemma alpha_ne_one : (-7 + 24 * Complex.I) / 25 ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

private lemma beta_ne_one : (-7 - 24 * Complex.I) / 25 ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

private lemma alpha_ne_beta : (-7 + 24 * Complex.I) / 25 ≠ (-7 - 24 * Complex.I) / 25 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-- A subspace invariant under `phaseMatrix ⊗ phaseMatrix` and
`rotationMatrix ⊗ rotationMatrix` containing `|00⟩` or `|11⟩`
contains every symmetric vector. -/
private lemma symmetric_le {W : Submodule ℂ V}
    (hd : ∀ x ∈ W, (phaseMatrix ⊗ₖ phaseMatrix).toEuclideanLin x ∈ W)
    (hR : ∀ x ∈ W, (rotationMatrix ⊗ₖ rotationMatrix).toEuclideanLin x ∈ W)
    (h : vec 1 0 0 0 ∈ W ∨ vec 0 0 0 1 ∈ W) (z : V) (hz : z (0, 1) = z (1, 0)) : z ∈ W := by
  have hE := fun {p q r s : ℂ} (hx : vec p q r s ∈ W) =>
    extract _ _ _ alpha_ne_one beta_ne_one alpha_ne_beta tensor_phase W hd hx
  have h00 : vec 1 0 0 0 ∈ W := by
    rcases h with h | h
    · exact h
    · have hy := hR _ h
      rw [tensor_rotation] at hy
      exact (hE hy).1 (by norm_num)
  have hy := hR _ h00
  rw [tensor_rotation] at hy
  have h11 := (hE hy).2.1 (by norm_num)
  have hmid := (hE hy).2.2
  have hz' : z = z (0, 0) • vec 1 0 0 0 +
      (25 / 12 * z (0, 1)) • vec 0 ((12 * 1 + 9 * 0 - 16 * 0 - 12 * 0) / 25)
        ((12 * 1 - 16 * 0 + 9 * 0 - 12 * 0) / 25) 0 + z (1, 1) • vec 0 0 0 1 := by
    rw [smul_vec, smul_vec, smul_vec, vec_add, vec_add, eta z, vec_eq_vec]
    simp only [vec_00, vec_01, vec_11]
    exact ⟨by ring, by ring, by linear_combination (-1 : ℂ) * hz, by ring⟩
  rw [hz']
  exact W.add_mem (W.add_mem (W.smul_mem _ h00) (W.smul_mem _ hmid)) (W.smul_mem _ h11)

/-- The four subspaces are the only ones invariant under `phaseMatrix ⊗ phaseMatrix` and
`rotationMatrix ⊗ rotationMatrix`. -/
private lemma classify {W : Submodule ℂ V}
    (hd : ∀ x ∈ W, (phaseMatrix ⊗ₖ phaseMatrix).toEuclideanLin x ∈ W)
    (hR : ∀ x ∈ W, (rotationMatrix ⊗ₖ rotationMatrix).toEuclideanLin x ∈ W) :
    W = ⊥ ∨ W = ℂ ∙ singlet ∨ W = (ℂ ∙ singlet)ᗮ ∨ W = ⊤ := by
  have hE := fun {p q r s : ℂ} (hx : vec p q r s ∈ W) =>
    extract _ _ _ alpha_ne_one beta_ne_one alpha_ne_beta tensor_phase W hd hx
  by_cases hle : W ≤ ℂ ∙ singlet
  · by_cases hb : W = ⊥
    · exact Or.inl hb
    refine Or.inr (Or.inl (le_antisymm hle ?_))
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp (hle hx)
    have ht : t ≠ 0 := by
      rintro rfl
      exact hx0 (zero_smul ℂ singlet)
    rw [Submodule.span_singleton_le_iff_mem]
    have := W.smul_mem t⁻¹ hx
    rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  right; right
  obtain ⟨x, hx, hxs⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hsym : ∀ z : V, z (0, 1) = z (1, 0) → z ∈ W := by
    apply symmetric_le hd hR
    rw [eta x] at hx hxs
    by_cases hp : x (0, 0) = 0
    · by_cases hs : x (1, 1) = 0
      · rw [hp, hs] at hx hxs
        have hmid := (hE hx).2.2
        have hqr : x (0, 1) + x (1, 0) ≠ 0 := by
          intro hqr
          apply hxs
          refine Submodule.mem_span_singleton.mpr ⟨x (0, 1), ?_⟩
          rw [singlet_eq, smul_vec, vec_eq_vec]
          exact ⟨by ring, by ring, by linear_combination (-1 : ℂ) * hqr, by ring⟩
        have hy := hR _ hmid
        rw [tensor_rotation] at hy
        refine Or.inl ((hE hy).1 ?_)
        intro h0
        apply hqr
        linear_combination (-25 / 12 : ℂ) * h0
      · exact Or.inr ((hE hx).2.1 hs)
    · exact Or.inl ((hE hx).1 hp)
  by_cases hW' : W ≤ (ℂ ∙ singlet)ᗮ
  · exact Or.inl (le_antisymm hW' fun z hz => hsym z ((mem_orthogonal_iff z).mp hz))
  right
  obtain ⟨y, hy, hyo⟩ := IsConcreteLE.not_le_iff_exists.mp hW'
  rw [mem_orthogonal_iff] at hyo
  have hc : (y (0, 1) - y (1, 0)) / 2 ≠ 0 := by
    intro h
    apply hyo
    linear_combination (2 : ℂ) * h
  have key : ∀ (z : V) (c : ℂ), c = (z (0, 1) - z (1, 0)) / 2 → z - c • singlet ∈ W := by
    intro z c hcz
    apply hsym
    rw [singlet_eq, eta z, smul_vec]
    simp only [PiLp.sub_apply, vec_01, vec_10]
    rw [hcz]
    ring
  have hs : singlet ∈ W := by
    have h1 := W.sub_mem hy (key y _ rfl)
    rw [sub_sub_cancel] at h1
    have := W.smul_mem ((y (0, 1) - y (1, 0)) / 2)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  refine eq_top_iff.mpr fun z _ => ?_
  have := W.add_mem (key z _ rfl) (W.smul_mem ((z (0, 1) - z (1, 0)) / 2) hs)
  rwa [sub_add_cancel] at this

/-- For every set `S` of `2 × 2` complex matrices containing `phaseMatrix` and
`rotationMatrix` (both special unitary), the subspaces of `ℂ² ⊗ ℂ²` invariant under `g ⊗ g` for
all `g ∈ S` are exactly `0`, the line of the singlet `ω = |01⟩ - |10⟩`, its orthogonal
complement and the whole space. Every `g ⊗ g` maps `ω` to `det g • ω`; the orthogonal
complement of `ω` consists of the vectors with equal `|01⟩` and `|10⟩` coordinates and has
dimension three. -/
theorem singlet_invariant_subspaces :
    phaseMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    rotationMatrix ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    (∀ S : Set (Matrix (Fin 2) (Fin 2) ℂ), phaseMatrix ∈ S → rotationMatrix ∈ S →
      ∀ W : Submodule ℂ (EuclideanSpace ℂ (Fin 2 × Fin 2)),
        (∀ g ∈ S, ∀ x ∈ W, (g ⊗ₖ g).toEuclideanLin x ∈ W) ↔
          W = ⊥ ∨ W = ℂ ∙ singlet ∨ W = (ℂ ∙ singlet)ᗮ ∨ W = ⊤) ∧
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, (g ⊗ₖ g).toEuclideanLin singlet = g.det • singlet) ∧
    (∀ x : EuclideanSpace ℂ (Fin 2 × Fin 2), x ∈ (ℂ ∙ singlet)ᗮ ↔ x (0, 1) = x (1, 0)) ∧
    Module.finrank ℂ (ℂ ∙ singlet)ᗮ = 3 := by
  refine ⟨phase_mem, rotation_mem, fun S hd hr W =>
    ⟨fun h => classify (h phaseMatrix hd) (h rotationMatrix hr),
      fun hW g _ x hx => tensor_mem g hW hx⟩, tensor_singlet, mem_orthogonal_iff, ?_⟩
  have : Fact (Module.finrank ℂ V = 3 + 1) := ⟨by simp⟩
  refine Submodule.finrank_orthogonal_span_singleton ?_
  intro h
  have := congrArg (· (0, 1)) h
  simp [singlet_eq] at this

end D5.S3.Quantum.Algebra.Unitary.TensorSquareSinglet
