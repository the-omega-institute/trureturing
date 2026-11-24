import D5.S3.Geometry.AdS3ModularBoundary
import D5.S3.Arith.ModularForms.RademacherVacuum

/-! The primitive bottom rows of the rectangular Rademacher vacuum sum index
the meridians of the modularly marked Euclidean AdS₃ solid tori. -/

set_option autoImplicit false

open scoped BigOperators Matrix MatrixGroups UpperHalfPlane

namespace D5.S3.Geometry.AdS3RademacherFilling

open AdS3LoxodromicQuotient.Loxodromic
open D5.S3.Arith.ModularForms.RademacherVacuum

/-- The sign normalization of a primitive meridian period (cτ+d). -/
@[ext] structure FillingIndex where
  c : ℤ
  d : ℤ
  primitive : Int.gcd c d = 1
  normalized : 0 < c ∨ (c = 0 ∧ d = 1)
  deriving DecidableEq

/-- The index of the identity filling. -/
def polarIndex : FillingIndex :=
  ⟨0, 1, by decide, Or.inr ⟨rfl, rfl⟩⟩

theorem eq_polarIndex_iff (p : FillingIndex) : p = polarIndex ↔ p.c = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro hc
    rcases p.normalized with h | ⟨_, hd⟩
    · exact (h.ne' hc).elim
    · exact FillingIndex.ext hc hd

/-- A determinant-one completion given by the extended gcd. -/
def FillingIndex.completion (p : FillingIndex) : SL(2, ℤ) :=
  ⟨!![Int.gcdB p.c p.d, -Int.gcdA p.c p.d; p.c, p.d], by
    have h : (1 : ℤ) = p.c * Int.gcdA p.c p.d + p.d * Int.gcdB p.c p.d := by
      simpa only [p.primitive, Nat.cast_one] using Int.gcd_eq_gcd_ab p.c p.d
    rw [Matrix.det_fin_two]
    change Int.gcdB p.c p.d * p.d - (-Int.gcdA p.c p.d) * p.c = 1
    linear_combination -h⟩

@[simp] theorem FillingIndex.completion_c (p : FillingIndex) : p.completion 1 0 = p.c := rfl

@[simp] theorem FillingIndex.completion_d (p : FillingIndex) : p.completion 1 1 = p.d := rfl

@[simp] theorem polarIndex_completion : polarIndex.completion = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FillingIndex.completion, polarIndex, Int.gcdA, Int.gcdB]

noncomputable section

/-- The meridian path on the reference boundary in its complex lift coordinates. -/
def markedMeridian (τ : ℍ) (p : FillingIndex) (t : ℝ) : (modularFilling τ).Boundary :=
  (modularFilling τ).boundaryLift ((t : ℂ) * ((p.c : ℂ) * (τ : ℂ) + (p.d : ℂ)))

/-- Every completion transports the boundary of the actual meridian disk to
the prescribed path. In particular, the transported path uses only the bottom row. -/
theorem markedMeridian_eq (τ : ℍ) (p : FillingIndex) (γ : SL(2, ℤ))
    (hc : γ 1 0 = p.c) (hd : γ 1 1 = p.d) (t : ℝ) :
    modularBoundaryHomeomorph γ τ
        ((modularFilling (γ • τ)).meridianCircle 0 (Circle.exp (2 * Real.pi * t))) =
      markedMeridian τ p t := by
  rw [modularBoundaryHomeomorph_meridianCircle]
  simp only [markedMeridian, modularFactor, hc, hd]

/-- Pulling the path back into the filling gives the rim of its meridian disk. -/
theorem markedMeridian_unmark_eq_disk (τ : ℍ) (p : FillingIndex) (γ : SL(2, ℤ))
    (hc : γ 1 0 = p.c) (hd : γ 1 1 = p.d) (t : ℝ) :
    ((modularBoundaryHomeomorph γ τ).symm (markedMeridian τ p t)).val =
      (modularFilling (γ • τ)).meridianDisk 0
        ⟨(Circle.exp (2 * Real.pi * t) : ℂ),
          mem_closedBall_zero_iff.mpr (Circle.norm_coe _).le⟩ := by
  rw [← markedMeridian_eq τ p γ hc hd t, Homeomorph.symm_apply_apply]
  rfl

private theorem eq_zero_of_real_mul_int {z : ℝ} (h : ∀ t : ℝ, ∃ n : ℤ, t * z = n) :
    z = 0 := by
  by_contra hz
  obtain ⟨n, hn⟩ := h (1 / (2 * z))
  have hn' : (2 : ℝ) * n = 1 := by
    rw [← hn]
    field_simp
  have hn'' : (2 : ℤ) * n = 1 := by exact_mod_cast hn'
  omega

/-- The parameterized geometric meridians distinguish normalized rows. -/
theorem markedMeridian_injective (τ : ℍ) : Function.Injective (markedMeridian τ) := by
  intro p q hpq
  have coords (t : ℝ) : ∃ m n : ℤ,
      t * ((p.c : ℝ) - q.c) = n ∧ t * ((p.d : ℝ) - q.d) = m := by
    have ht := congrFun hpq t
    unfold markedMeridian at ht
    obtain ⟨m, n, h⟩ := (boundaryLift_eq_iff τ τ.im_pos _ _).mp ht
    have h' : (t : ℂ) * (((p.c : ℂ) - q.c) * (τ : ℂ) + ((p.d : ℂ) - q.d)) =
        (m : ℂ) + (n : ℂ) * (τ : ℂ) := by
      linear_combination h
    have him := congrArg Complex.im h'
    have hre := congrArg Complex.re h'
    simp only [← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.mul_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      zero_mul, zero_add, add_zero, sub_zero] at him hre
    have hct : t * ((p.c : ℝ) - q.c) = n := by
      apply mul_right_cancel₀ τ.im_pos.ne'
      rw [mul_assoc]
      exact him
    refine ⟨m, n, hct, ?_⟩
    linear_combination hre - (τ : ℂ).re * hct
  apply FillingIndex.ext
  · have hc := eq_zero_of_real_mul_int (fun t => by
      obtain ⟨_, n, hn, _⟩ := coords t
      exact ⟨n, hn⟩)
    exact_mod_cast (sub_eq_zero.mp hc)
  · have hd := eq_zero_of_real_mul_int (fun t => by
      obtain ⟨m, _, _, hm⟩ := coords t
      exact ⟨m, hm⟩)
    exact_mod_cast (sub_eq_zero.mp hd)

/-- The embedded meridian circle, on the common marked boundary. -/
def markedMeridianCircle (τ : ℍ) (p : FillingIndex) (u : Circle) :
    (modularFilling τ).Boundary :=
  modularBoundaryHomeomorph p.completion τ
    ((modularFilling (p.completion • τ)).meridianCircle 0 u)

theorem markedMeridianCircle_isEmbedding (τ : ℍ) (p : FillingIndex) :
    Topology.IsEmbedding (markedMeridianCircle τ p) :=
  modularBoundaryHomeomorph_meridianCircle_isEmbedding p.completion τ

theorem markedMeridianCircle_eq (τ : ℍ) (p : FillingIndex) (γ : SL(2, ℤ))
    (hc : γ 1 0 = p.c) (hd : γ 1 1 = p.d) (u : Circle) :
    modularBoundaryHomeomorph γ τ ((modularFilling (γ • τ)).meridianCircle 0 u) =
      markedMeridianCircle τ p u := by
  obtain ⟨x, rfl⟩ := Circle.exp_surjective u
  let t := x / (2 * Real.pi)
  have h : 2 * Real.pi * t = x := by
    dsimp [t]
    field_simp [Real.pi_ne_zero]
  rw [← h]
  exact (markedMeridian_eq τ p γ hc hd t).trans
    (markedMeridian_eq τ p p.completion p.completion_c p.completion_d t).symm

@[simp] theorem markedMeridian_polarIndex (τ : ℍ) (t : ℝ) :
    markedMeridian τ polarIndex t = (modularFilling τ).boundaryLift (t : ℂ) := by
  simp [markedMeridian, polarIndex]

private theorem det_eq (γ : SL(2, ℤ)) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using γ.det_coe

/-- The top-left entry of every completion is the inverse residue modulo (c). -/
theorem topLeft_modEq_inverseResidue (γ : SL(2, ℤ)) {c d : ℤ}
    (hc : γ 1 0 = c) (hd : γ 1 1 = d) (hcpos : 0 < c) :
    γ 0 0 ≡ inverseResidue c d [ZMOD c] := by
  have hprimitive := (exists_modular_bottomRow_iff c d).mp ⟨γ, hc, hd⟩
  have hdet := det_eq γ
  rw [hc, hd] at hdet
  have ha : d * γ 0 0 ≡ 1 [ZMOD c] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-γ 0 1, ?_⟩
    linear_combination -hdet
  simpa [hprimitive] using
    Int.ModEq.cancel_left_div_gcd hcpos
      (ha.trans (inverseResidue_spec hcpos hprimitive).2.2.symm)

local notation "κ" => (((2 * Real.pi : ℝ) : ℂ) * Complex.I)

private theorem vacuumPhase_eq (γ : SL(2, ℤ)) {c d : ℤ}
    (hc : γ 1 0 = c) (hd : γ 1 1 = d) (hcpos : 0 < c) :
    vacuumPhase c d = Complex.exp (-κ * ((γ 0 0 : ℂ) / (c : ℂ))) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hcpos)
  obtain ⟨k, hk⟩ := (topLeft_modEq_inverseResidue γ hc hd hcpos).symm.dvd
  have hk' : (γ 0 0 : ℂ) - (inverseResidue c d : ℂ) = (c : ℂ) * (k : ℂ) := by
    exact_mod_cast hk
  have h : (γ 0 0 : ℂ) / (c : ℂ) =
      (inverseResidue c d : ℂ) / (c : ℂ) + (k : ℂ) := by
    field_simp
    linear_combination hk'
  rw [h, mul_add, Complex.exp_add]
  have hperiod : Complex.exp (-κ * (k : ℂ)) = 1 := by
    simpa only [Int.cast_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul,
      mul_comm (2 * (Real.pi : ℂ) * Complex.I) (k : ℂ)] using
      Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [hperiod, mul_one]
  unfold vacuumPhase
  push_cast
  congr 1
  ring

/-- The vacuum summand subtracts the cusp phase of any matrix completing the
positive primitive bottom row. -/
theorem vacuumSummand_eq (γ : SL(2, ℤ)) (τ : ℍ) {c d : ℤ}
    (hc : γ 1 0 = c) (hd : γ 1 1 = d) (hcpos : 0 < c) :
    vacuumSummand c d τ =
      Complex.exp (-κ * ((γ • τ : ℍ) : ℂ)) -
        Complex.exp (-κ * ((γ 0 0 : ℂ) / (c : ℂ))) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hcpos)
  have hden : denominator c d τ ≠ 0 := by
    simpa only [modularFactor, denominator, hc, hd] using modularFactor_ne_zero γ τ
  have hdet := det_eq γ
  rw [hc, hd] at hdet
  have hdet' : (γ 0 0 : ℂ) * (d : ℂ) - (γ 0 1 : ℂ) * (c : ℂ) = 1 := by
    exact_mod_cast hdet
  have hsplit : ((γ • τ : ℍ) : ℂ) =
      (γ 0 0 : ℂ) / (c : ℂ) - 1 / ((c : ℂ) * denominator c d τ) := by
    have h := smul_mul_modularFactor γ τ
    rw [modularFactor, hc, hd] at h
    change _ * denominator c d τ = _ at h
    rw [(eq_div_iff hden).mpr h]
    field_simp
    unfold denominator
    linear_combination -hdet'
  rw [vacuumSummand, vacuumPhase_eq γ hc hd hcpos, mul_sub, mul_one, ← Complex.exp_add]
  congr 2
  rw [hsplit, vacuumArgument]
  ring

private def cutoffIndexEmbedding (N : ℕ) :
    {q // q ∈ cutoffPairs N} ↪ FillingIndex where
  toFun q :=
    ⟨q.1.1, q.1.2, (mem_cutoffPairs.mp q.2).2.2.2, Or.inl (mem_cutoffPairs.mp q.2).1⟩
  inj' := fun _ _ h =>
    Subtype.ext (Prod.ext (congrArg FillingIndex.c h) (congrArg FillingIndex.d h))

/-- The nonpolar marked fillings in the original rectangular cutoff. -/
def fillingCutoff (N : ℕ) : Finset FillingIndex :=
  (cutoffPairs N).attach.map (cutoffIndexEmbedding N)

@[simp] theorem mem_fillingCutoff {N : ℕ} {p : FillingIndex} :
    p ∈ fillingCutoff N ↔ 0 < p.c ∧ p.c < (N : ℤ) ∧ |p.d| < (N : ℤ) ^ 2 := by
  constructor
  · intro hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨hc, hN, hd, _⟩ := mem_cutoffPairs.mp q.2
    exact ⟨hc, hN, hd⟩
  · rintro ⟨hc, hN, hd⟩
    let q : {q // q ∈ cutoffPairs N} := ⟨(p.c, p.d), mem_cutoffPairs.mpr
      ⟨hc, hN, hd, p.primitive⟩⟩
    exact Finset.mem_map.mpr ⟨q, Finset.mem_attach _ _, FillingIndex.ext rfl rfl⟩

/-- The polar filling contributes (q^{-1}) and each positive marked filling
contributes its cusp-subtracted exponential in the literal rectangular cutoff. -/
theorem rademacherCutoff_eq_fillingCutoff (N : ℕ) (τ : ℍ) :
    rademacherCutoff N τ =
      Complex.exp (-κ * ((polarIndex.completion • τ : ℍ) : ℂ)) +
        ∑ p ∈ fillingCutoff N,
          (Complex.exp (-κ * ((p.completion • τ : ℍ) : ℂ)) -
            Complex.exp (-κ * ((p.completion 0 0 : ℂ) / (p.c : ℂ)))) := by
  have hpolar : Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * Complex.I * (τ : ℂ)) =
      Complex.exp (-κ * ((polarIndex.completion • τ : ℍ) : ℂ)) := by
    simp only [polarIndex_completion, one_smul, neg_mul]
  rw [rademacherCutoff, hpolar]
  congr 1
  rw [fillingCutoff, Finset.sum_map]
  calc
    _ = ∑ q ∈ (cutoffPairs N).attach, vacuumSummand q.1.1 q.1.2 τ :=
      (Finset.sum_attach _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      let p := cutoffIndexEmbedding N q
      exact vacuumSummand_eq p.completion τ p.completion_c p.completion_d
        (mem_cutoffPairs.mp q.2).1

end

/-- Normalize a primitive row by choosing its sign. -/
def normalizeRow (c d : ℤ) (h : Int.gcd c d = 1) : FillingIndex :=
  if hn : 0 < c ∨ (c = 0 ∧ d = 1) then ⟨c, d, h, hn⟩
  else ⟨-c, -d, by simpa using h, by
    rcases lt_trichotomy c 0 with hlt | rfl | hgt
    · exact Or.inl (neg_pos.mpr hlt)
    · simp only [Int.zero_gcd] at h
      exact Or.inr ⟨by simp, by omega⟩
    · exact (hn (Or.inl hgt)).elim⟩

/-- A primitive row has exactly one normalized representative up to sign. -/
theorem normalizeRow_eq_iff (c d : ℤ) (h : Int.gcd c d = 1) (p : FillingIndex) :
    normalizeRow c d h = p ↔
      (c = p.c ∧ d = p.d) ∨ (c = -p.c ∧ d = -p.d) := by
  unfold normalizeRow
  split
  · rw [FillingIndex.ext_iff]
    change (c = p.c ∧ d = p.d) ↔ _
    have hp := p.normalized
    omega
  · rw [FillingIndex.ext_iff]
    change (-c = p.c ∧ -d = p.d) ↔ _
    have hp := p.normalized
    omega

/-- The normalized bottom row of a modular matrix. -/
def fillingIndex (γ : SL(2, ℤ)) : FillingIndex :=
  normalizeRow (γ 1 0) (γ 1 1) ((exists_modular_bottomRow_iff _ _).mp ⟨γ, rfl, rfl⟩)

theorem fillingIndex_eq_iff_row (γ : SL(2, ℤ)) (p : FillingIndex) :
    fillingIndex γ = p ↔
      (γ 1 0 = p.c ∧ γ 1 1 = p.d) ∨ (γ 1 0 = -p.c ∧ γ 1 1 = -p.d) :=
  normalizeRow_eq_iff _ _ _ _

@[simp] theorem fillingIndex_completion (p : FillingIndex) : fillingIndex p.completion = p :=
  (fillingIndex_eq_iff_row _ _).mpr (Or.inl ⟨p.completion_c, p.completion_d⟩)

/-- The marked path of an arbitrary modular matrix is the normalized path
with the parameter reversed precisely when its bottom row is negated. -/
theorem markedMeridian_of_matrix (γ : SL(2, ℤ)) (τ : ℍ) (t : ℝ) :
    modularBoundaryHomeomorph γ τ
        ((modularFilling (γ • τ)).meridianCircle 0 (Circle.exp (2 * Real.pi * t))) =
      markedMeridian τ (fillingIndex γ)
        (if 0 < γ 1 0 ∨ (γ 1 0 = 0 ∧ γ 1 1 = 1) then t else -t) := by
  rw [modularBoundaryHomeomorph_meridianCircle]
  unfold markedMeridian fillingIndex normalizeRow
  split
  · rfl
  · simp only [modularFactor, Int.cast_neg, Complex.ofReal_neg]
    congr 1
    ring

/-- Two matrices have the same normalized index exactly when they differ by
a left translation, with an optional global sign. -/
theorem fillingIndex_eq_iff (γ δ : SL(2, ℤ)) :
    fillingIndex δ = fillingIndex γ ↔
      (∃ k : ℤ, δ = ModularGroup.T ^ k * γ) ∨
      (∃ k : ℤ, δ = ModularGroup.T ^ k * (-γ)) := by
  have rows (g : SL(2, ℤ)) :
      (δ 1 0 = g 1 0 ∧ δ 1 1 = g 1 1) ↔ ∃ k : ℤ, δ = ModularGroup.T ^ k * g := by
    rw [← modular_same_bottomRow_iff]
    exact ⟨fun ⟨hc, hd⟩ => funext (fun j => by fin_cases j <;> assumption),
      fun h => ⟨congrFun h 0, congrFun h 1⟩⟩
  rw [← rows γ, ← rows (-γ), fillingIndex_eq_iff_row]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  have hγ := (fillingIndex_eq_iff_row γ (fillingIndex γ)).mp rfl
  rcases hγ with hγ | hγ <;> omega

/-- The equivalence relation on modular matrices induced by left translations
and global sign. -/
def fillingSetoid : Setoid (SL(2, ℤ)) where
  r γ δ :=
    (∃ k : ℤ, δ = ModularGroup.T ^ k * γ) ∨
    (∃ k : ℤ, δ = ModularGroup.T ^ k * (-γ))
  iseqv := {
    refl := fun γ => (fillingIndex_eq_iff γ γ).mp rfl
    symm := fun {γ δ} h => (fillingIndex_eq_iff δ γ).mp ((fillingIndex_eq_iff γ δ).mpr h).symm
    trans := fun {γ δ η} h₁ h₂ => (fillingIndex_eq_iff γ η).mp
      (((fillingIndex_eq_iff δ η).mpr h₂).trans ((fillingIndex_eq_iff γ δ).mpr h₁)) }

/-- The quotient is classified by the normalized primitive rows, with an
explicit determinant-one representative for every class. -/
def fillingQuotientEquiv : Quotient fillingSetoid ≃ FillingIndex where
  toFun := Quotient.lift fillingIndex (fun γ δ h => ((fillingIndex_eq_iff γ δ).mpr h).symm)
  invFun p := Quotient.mk fillingSetoid p.completion
  left_inv q := Quotient.inductionOn q fun γ =>
    Quotient.sound ((fillingIndex_eq_iff (fillingIndex γ).completion γ).mp
      (fillingIndex_completion _).symm)
  right_inv := fillingIndex_completion

@[simp] theorem fillingQuotientEquiv_mk (γ : SL(2, ℤ)) :
    fillingQuotientEquiv (Quotient.mk fillingSetoid γ) = fillingIndex γ := rfl

@[simp] theorem fillingQuotientEquiv_symm_apply (p : FillingIndex) :
    fillingQuotientEquiv.symm p = Quotient.mk fillingSetoid p.completion := rfl

end D5.S3.Geometry.AdS3RademacherFilling
