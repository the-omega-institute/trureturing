/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonNeutral
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonNeutral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unique neutral size-two block of the actual Cartesian vortex derivative. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonDecomposition

/-! The full neutral generalized space and its actual Jordan chain. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
open InverseChordCirculant AlternatingPolygonModes AlternatingPolygonJordan
open AlternatingPolygonDecomposition

private theorem paired_square {Q : Type*} (α β : Q → ℂ) (v : Q → ℂ × ℂ) (q : Q) :
    ((pairedOperator α β) ^ 2) v q =
      (α q * β q * (v q).1, α q * β q * (v q).2) := by
  simp only [pow_two, Module.End.mul_apply, pairedOperator, LinearMap.coe_mk,
    AddHom.coe_mk]
  ext <;> ring

private theorem paired_kernel_cube {Q : Type*} (α β : Q → ℂ) (v : Q → ℂ × ℂ)
    (h : ((pairedOperator α β) ^ 2) (pairedOperator α β v) = 0) :
    ((pairedOperator α β) ^ 2) v = 0 := by
  funext q
  rw [paired_square]
  by_cases hγ : α q * β q = 0
  · simp [hγ]
  · have hα : α q ≠ 0 := fun h => hγ (by rw [h, zero_mul])
    have hβ : β q ≠ 0 := fun h => hγ (by rw [h, mul_zero])
    have h₁ := congrArg (fun w : Q → ℂ × ℂ => (w q).1) h
    have h₂ := congrArg (fun w : Q → ℂ × ℂ => (w q).2) h
    rw [paired_square] at h₁ h₂
    change α q * β q * (α q * (v q).2) = 0 at h₁
    change α q * β q * (β q * (v q).1) = 0 at h₂
    apply Prod.ext
    · exact (mul_eq_zero.mp (show β q * (α q * β q * (v q).1) = 0 by
        linear_combination h₂)).resolve_left hβ
    · exact (mul_eq_zero.mp (show α q * (α q * β q * (v q).2) = 0 by
        linear_combination h₁)).resolve_left hα

/-- All nilpotent restrictions of an off-diagonal paired operator have index at most two. -/
theorem paired_neutral_iff {Q : Type*} (α β : Q → ℂ) (v : Q → ℂ × ℂ) :
    v ∈ (pairedOperator α β).maxGenEigenspace 0 ↔
      ∀ q, α q * β q ≠ 0 → v q = 0 := by
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
    simp only [zero_smul, sub_zero] at hn
    have hp : ∀ n : ℕ, ∀ v : Q → ℂ × ℂ,
        ((pairedOperator α β) ^ n) v = 0 → ((pairedOperator α β) ^ 2) v = 0 := by
      intro n
      induction n with
      | zero =>
        intro v hv
        simpa only [pow_zero, Module.End.one_apply, map_zero] using congrArg
          (fun w => ((pairedOperator α β) ^ 2) w) hv
      | succ n ih =>
        intro v hv
        apply paired_kernel_cube α β v
        apply ih
        simpa only [pow_succ, Module.End.mul_apply] using hv
    intro q hq
    have h := congrArg (fun w : Q → ℂ × ℂ => w q) (hp n v hn)
    rw [paired_square] at h
    exact Prod.ext
      ((mul_eq_zero.mp (congrArg Prod.fst h)).resolve_left hq)
      ((mul_eq_zero.mp (congrArg Prod.snd h)).resolve_left hq)
  · intro hv
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    refine ⟨2, ?_⟩
    simp only [zero_smul, sub_zero]
    funext q
    rw [paired_square]
    by_cases hq : α q * β q = 0
    · simp [hq]
    · rw [hv q hq]
      simp

theorem gamma_zero_iff_label (m : ℕ) [NeZero (2 * m)] (q : ZMod (2 * m)) :
    gamma m q = 0 ↔ q = m := by
  have hm : 0 < m := by have := NeZero.ne (2 * m); omega
  have hv : (m : ZMod (2 * m)).val = m := ZMod.val_natCast_of_lt (by omega)
  rw [gamma_zero_iff, fold_eq_iff m q le_rfl]
  constructor
  · intro h
    apply ZMod.val_injective
    rw [hv]
    omega
  · intro h
    left
    rw [h, hv]

/-- Powers intertwine through the same complete Cartesian coordinate equivalence. -/
theorem actual_pow_coordinates (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    (n : ℕ) (v : Cartesian m) :
    cartesianCoordinates m (((actualOperator m) ^ n) v) =
      ((modeOperator m) ^ n) (cartesianCoordinates m v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [actual_normal_form m hm, ih]

/-- The entire neutral generalized space is exactly the single Fourier block q=m. -/
theorem actual_neutral_iff (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (v : Cartesian m) :
    v ∈ (actualOperator m).maxGenEigenspace 0 ↔
      ∀ q : ZMod (2 * m), q ≠ m → cartesianCoordinates m v q = 0 := by
  have ht : v ∈ (actualOperator m).maxGenEigenspace 0 ↔
      cartesianCoordinates m v ∈ (modeOperator m).maxGenEigenspace 0 := by
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← actual_pow_coordinates m hm, hn, map_zero]⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hw : cartesianCoordinates m (((actualOperator m) ^ n) v) = 0 := by
        rwa [actual_pow_coordinates m hm]
      exact (reconstruct m _).trans ((unique_coefficients m _).mpr hw)
  rw [ht, modeOperator, paired_neutral_iff]
  have hg (q : ZMod (2 * m)) :
      (ell m q : ℂ) * ((ell m (q + m) + 1 : ℝ) : ℂ) ≠ 0 ↔ q ≠ m := by
    rw [← Complex.ofReal_mul, ne_eq, Complex.ofReal_eq_zero, mode_product,
      gamma_zero_iff_label]
  simp only [hg]

/-- The actual Cartesian neutral eigenvector, in explicit Fourier coordinates. -/
def neutral0 (m : ℕ) [NeZero (2 * m)] : Cartesian m :=
  (cartesianCoordinates m).symm (Pi.single (m : ZMod (2 * m)) (0, 1))

/-- Its actual generalized vector; the nonzero denominator is proved for all m>=1. -/
def neutral1 (m : ℕ) [NeZero (2 * m)] : Cartesian m :=
  (cartesianCoordinates m).symm
    (Pi.single (m : ZMod (2 * m))
      (((ell m ((m : ZMod (2 * m)) + m) + 1 : ℝ) : ℂ)⁻¹, 0))

theorem neutral_chain (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
    actualOperator m (neutral0 m) = 0 ∧
      actualOperator m (neutral1 m) = neutral0 m := by
  have hm0 : 0 < m := by omega
  have hv : (m : ZMod (2 * m)).val = m := ZMod.val_natCast_of_lt (by omega)
  have hα : ell m (m : ZMod (2 * m)) = 0 := by simp [ell, hv]
  have hβ : ((ell m ((m : ZMod (2 * m)) + m) + 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ell_add_one_ne_zero m _)
  push_cast at hβ
  constructor <;> apply (cartesianCoordinates m).injective
  · rw [actual_normal_form m hm, neutral0, LinearEquiv.apply_symm_apply, map_zero]
    funext q
    by_cases hq : q = (m : ZMod (2 * m))
    · subst q
      simp [modeOperator, pairedOperator, hα]
    · simp [modeOperator, pairedOperator, Pi.single_eq_of_ne hq]
  · rw [actual_normal_form m hm, neutral1, LinearEquiv.apply_symm_apply,
      neutral0, LinearEquiv.apply_symm_apply]
    funext q
    by_cases hq : q = (m : ZMod (2 * m))
    · subst q
      simp [modeOperator, pairedOperator, hβ]
    · simp [modeOperator, pairedOperator, Pi.single_eq_of_ne hq]

/-- The entire neutral generalized space is this one two-dimensional invariant block. -/
theorem neutral_space (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
    (actualOperator m).maxGenEigenspace 0 = invariantSpace m m := by
  classical
  ext v
  rw [actual_neutral_iff m hm]
  constructor
  · intro hv
    refine ⟨cartesianCoordinates m v m, ?_⟩
    apply (cartesianCoordinates m).injective
    rw [coordinates_block]
    funext q
    by_cases hq : q = (m : ZMod (2 * m))
    · subst q; simp
    · rw [hv q hq, Pi.single_eq_of_ne hq]
  · rintro ⟨w, rfl⟩ q hq
    rw [coordinates_block, Pi.single_eq_of_ne hq]

theorem neutral_generalized_finrank (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
    Module.finrank ℂ ((actualOperator m).maxGenEigenspace 0) = 2 := by
  rw [neutral_space m hm, invariantSpace_finrank]

theorem neutral0_ne_zero (m : ℕ) [NeZero (2 * m)] : neutral0 m ≠ 0 := by
  intro h
  have h' := congrArg (fun v => (cartesianCoordinates m v m).2) h
  simp [neutral0] at h'

/-- The ordinary neutral eigenspace is exactly the line generated by the actual chain endpoint. -/
theorem neutral_eigenspace (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
    (actualOperator m).eigenspace 0 = Submodule.span ℂ {neutral0 m} := by
  classical
  ext v
  constructor
  · intro hv
    have hvG := Module.End.eigenspace_le_maxGenEigenspace hv
    rw [neutral_space m hm] at hvG
    obtain ⟨w, rfl⟩ := hvG
    rw [Module.End.mem_eigenspace_iff] at hv
    have hβ : ((ell m ((m : ZMod (2 * m)) + m) + 1 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ell_add_one_ne_zero m _)
    have hx := congrArg (fun v => (cartesianCoordinates m v m).2) hv
    rw [block_restriction m hm, coordinates_block] at hx
    simp only [Pi.single_eq_same, zero_smul, map_zero] at hx
    change ((ell m ((m : ZMod (2 * m)) + m) + 1 : ℝ) : ℂ) * w.1 = 0 at hx
    have hw : w.1 = 0 := (mul_eq_zero.mp hx).resolve_left hβ
    apply Submodule.mem_span_singleton.mpr
    refine ⟨w.2, ?_⟩
    apply (cartesianCoordinates m).injective
    rw [map_smul, neutral0, LinearEquiv.apply_symm_apply, coordinates_block]
    rw [← Pi.single_smul]
    congr 1
    ext <;> simp [hw]
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [Module.End.mem_eigenspace_iff, map_smul, (neutral_chain m hm).1]
    simp

/-- Exactly one neutral eigenline and a two-dimensional generalized space: one size-two block. -/
theorem neutral_geometric_finrank (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) :
    Module.finrank ℂ ((actualOperator m).eigenspace 0) = 1 := by
  rw [neutral_eigenspace m hm]
  exact finrank_span_singleton (neutral0_ne_zero m)

/-- The two members of the actual chain are linearly independent. -/
theorem neutral_chain_independent (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    (a b : ℂ) (h : a • neutral0 m + b • neutral1 m = 0) : a = 0 ∧ b = 0 := by
  have h' := congrArg (actualOperator m) h
  rw [map_add, map_smul, map_smul, (neutral_chain m hm).1,
    (neutral_chain m hm).2, smul_zero, zero_add, map_zero] at h'
  have hb : b = 0 := (smul_eq_zero.mp h').resolve_right (neutral0_ne_zero m)
  subst b
  simp only [zero_smul, add_zero] at h
  exact ⟨(smul_eq_zero.mp h).resolve_right (neutral0_ne_zero m), rfl⟩

/-- The generalized vector generates a nonconstant linear-drift solution of the linearized equation. -/
theorem neutral_drift (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (t : ℂ) :
    actualOperator m (neutral1 m + t • neutral0 m) = neutral0 m := by
  rw [map_add, map_smul, (neutral_chain m hm).1, (neutral_chain m hm).2,
    smul_zero, add_zero]

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
