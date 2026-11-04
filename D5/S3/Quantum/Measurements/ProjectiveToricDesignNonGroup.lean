/- GID: D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.claim; result=D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.result; claim=D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.claim
   digest: An inverse spread gives a non-group projective toric 2-design in dimension 27. -/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
The formal reading is the representative slice with first phase zero in
Iosue–Mooney–Ehrenberg–Gorshkov, arXiv:2311.13479v3, equations
`eq:repr-proj-toric` and `eq:toric-angle`. The identity-containing reading
of Conjecture 4.9 is fixed by preregistration #26419.
Mathlib calls the angle exponential `Real.Angle.toCircle`.
Admission basis: open-problem-resolution (refutation).
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup

/-- The second moment condition in representatives, multiplied by the cardinality. -/
def design2 {d : ℕ} (X : Finset (Fin d → Real.Angle)) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : Fin d,
    (((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁)) →
      ∑ φ ∈ X, (Real.Angle.toCircle (φ a₁ + φ a₂ - φ b₁ - φ b₂) : ℂ) = X.card) ∧
    ((¬ ((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁))) →
      ∑ φ ∈ X, (Real.Angle.toCircle (φ a₁ + φ a₂ - φ b₁ - φ b₂) : ℂ) = 0)

/-- The unnormalized MUB overlap condition. -/
def mubOverlap {d : ℕ} (X : Finset (Fin d → Real.Angle)) : Prop :=
  ∀ φ ∈ X, ∀ θ ∈ X, φ ≠ θ →
    ‖∑ j, (Real.Angle.toCircle (φ j - θ j) : ℂ)‖ ^ 2 = 0 ∨
    ‖∑ j, (Real.Angle.toCircle (φ j - θ j) : ℂ)‖ ^ 2 = (d : ℝ)

def claim : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (X : Finset (Fin d → Real.Angle)),
    (∀ φ ∈ X, φ ⟨0, hd⟩ = 0) → X.card = d ^ 2 → design2 X → mubOverlap X → 0 ∈ X →
      ∃ H : AddSubgroup (Fin d → Real.Angle), (H : Set (Fin d → Real.Angle)) = ↑X

private def coord : Fin 27 ≃ (Fin 3 → ZMod 3) :=
  (finFunctionFinEquiv (m := 3) (n := 3)).symm.trans
    (Equiv.piCongrRight fun _ => (ZMod.finEquiv 3).toEquiv)

private def phase_map : ZMod 3 →+ Real.Angle :=
  (AddCircle.equivAddCircle (1 : ℝ) (2 * Real.pi) one_ne_zero
    (mul_ne_zero two_ne_zero Real.pi_ne_zero)).toAddMonoidHom.comp ZMod.toAddCircle

private def matrices : Fin 27 → Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ![!![0, 0, 0; 0, 0, 0; 0, 0, 0],
    !![0, 1, 2; 1, 1, 2; 2, 2, 0],
    !![0, 2, 1; 2, 2, 1; 1, 1, 0],
    !![0, 0, 2; 0, 2, 1; 2, 1, 2],
    !![1, 1, 1; 1, 0, 2; 1, 2, 2],
    !![1, 2, 2; 2, 0, 2; 2, 2, 1],
    !![0, 0, 1; 0, 1, 2; 1, 2, 1],
    !![2, 1, 1; 1, 0, 1; 1, 1, 2],
    !![2, 2, 2; 2, 0, 1; 2, 1, 1],
    !![2, 0, 2; 0, 2, 0; 2, 0, 0],
    !![1, 2, 0; 2, 1, 2; 0, 2, 2],
    !![1, 2, 1; 2, 2, 0; 1, 0, 1],
    !![1, 1, 2; 1, 2, 2; 2, 2, 2],
    !![2, 2, 0; 2, 2, 2; 0, 2, 0],
    !![0, 2, 2; 2, 1, 0; 2, 0, 1],
    !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    !![2, 0, 1; 0, 0, 2; 1, 2, 0],
    !![1, 0, 0; 0, 2, 2; 0, 2, 1],
    !![1, 0, 1; 0, 1, 0; 1, 0, 0],
    !![2, 1, 2; 1, 1, 0; 2, 0, 2],
    !![2, 1, 0; 1, 2, 1; 0, 1, 1],
    !![0, 2, 0; 2, 0, 0; 0, 0, 2],
    !![2, 0, 0; 0, 1, 1; 0, 1, 2],
    !![1, 0, 2; 0, 0, 1; 2, 1, 0],
    !![2, 2, 1; 2, 1, 1; 1, 1, 1],
    !![0, 1, 1; 1, 2, 0; 1, 0, 2],
    !![1, 1, 0; 1, 1, 1; 0, 1, 0]]

private def polynomial (M : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (b x : Fin 3 → ZMod 3) : ZMod 3 := x ⬝ᵥ M.mulVec x + b ⬝ᵥ x

private def point (p : Fin 27 × (Fin 3 → ZMod 3)) (j : Fin 27) : Real.Angle :=
  phase_map (polynomial (matrices p.1) p.2 (coord j))

private def counterexample : Finset (Fin 27 → Real.Angle) := by
  classical
  exact Finset.univ.image point

private theorem phase_character (k : ZMod 3) :
    (Real.Angle.toCircle (phase_map k) : ℂ) = ZMod.stdAddChar k := by
  change (Real.Angle.toCircle (AddCircle.equivAddCircle (1 : ℝ) (2 * Real.pi) _ _
    (ZMod.toAddCircle k)) : ℂ) = _
  rw [ZMod.toAddCircle_apply, AddCircle.equivAddCircle_apply_mk]
  simp (config := { congrConsts := false }) only [inv_one, one_mul]
  change (Real.Angle.toCircle (((k.val : ℝ) / 3 * (2 * Real.pi) : ℝ) : Real.Angle) : ℂ) = _
  rw [Real.Angle.toCircle_coe, ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp]
  congr 2
  ring

private theorem phase_injective : Function.Injective phase_map :=
  (AddCircle.equivAddCircle (1 : ℝ) (2 * Real.pi) one_ne_zero
    (mul_ne_zero two_ne_zero Real.pi_ne_zero)).injective.comp (ZMod.toAddCircle_injective 3)

private theorem coord_zero : coord 0 = 0 := by
  change (finFunctionFinEquiv (m := 3) (n := 3)).symm (0 : Fin 27) =
    (fun _ : Fin 3 => (0 : Fin 3))
  apply finFunctionFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change 0 = (finFunctionFinEquiv (fun _ : Fin 3 => (0 : Fin 3)) : ℕ)
  rw [finFunctionFinEquiv_apply]
  simp (config := { congrConsts := false })

private theorem matrices_symmetric (i : Fin 27) : (matrices i).IsSymm := by
  revert i
  decide +kernel

private theorem spread (i j : Fin 27) (h : i ≠ j) : (matrices i - matrices j).det ≠ 0 := by
  revert i j h
  decide +kernel

private theorem matrices_not_add :
    ∀ i : Fin 27, matrices i ≠ matrices 1 + matrices 3 := by
  decide +kernel

private theorem character_orthogonality (w : Fin 3 → ZMod 3) :
    ∑ x : Fin 3 → ZMod 3, ZMod.stdAddChar (w ⬝ᵥ x) =
      if w = 0 then (27 : ℂ) else 0 := by
  classical
  by_cases hw : w = 0
  · simp (config := { congrConsts := false }) [hw]
  rw [ite_eq_right hw]
  let f : (Fin 3 → ZMod 3) →+ ZMod 3 :=
    (dotProductBilin (ZMod 3) (ZMod 3) w).toAddMonoidHom
  let ψ : AddChar (Fin 3 → ZMod 3) ℂ := ZMod.stdAddChar.compAddMonoidHom f
  change ∑ x, ψ x = 0
  apply AddChar.sum_eq_zero_of_ne_one
  intro h
  apply hw
  apply dotProduct_eq_zero
  intro x
  apply ZMod.injective_stdAddChar
  change ψ x = ZMod.stdAddChar 0
  rw [h, AddChar.one_apply, AddChar.map_zero_eq_one]

private theorem polynomial_shift (M : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hM : M.IsSymm) (b h y : Fin 3 → ZMod 3) :
    polynomial M b (h + y) - polynomial M b y =
      polynomial M b h + ((2 : ZMod 3) • M.mulVec h) ⬝ᵥ y := by
  rw [polynomial, polynomial, polynomial]
  simp (config := { congrConsts := false }) only [Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (M.mulVec h) y, hM.dotProduct_mulVec_comm (x := y) (y := h)]
  ring

private theorem quadratic_energy (M : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hM : M.IsSymm) (hD : M.det ≠ 0) (b : Fin 3 → ZMod 3) :
    ‖∑ x : Fin 3 → ZMod 3, ZMod.stdAddChar (polynomial M b x)‖ ^ 2 = 27 := by
  classical
  have hi : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hD))
  have hz (h : Fin 3 → ZMod 3) : (2 : ZMod 3) • M.mulVec h = 0 ↔ h = 0 := by
    rw [(isUnit_iff_ne_zero.mpr (by decide : (2 : ZMod 3) ≠ 0)).smul_eq_zero]
    simpa (config := { congrConsts := false }) only [Matrix.mulVec_zero] using
      (hi.eq_iff : M.mulVec h = M.mulVec 0 ↔ h = 0)
  have he : (∑ x : Fin 3 → ZMod 3, ZMod.stdAddChar (polynomial M b x)) *
      (∑ y : Fin 3 → ZMod 3, ZMod.stdAddChar (-polynomial M b y)) = (27 : ℂ) := by
    calc
      _ = ∑ x : Fin 3 → ZMod 3, ∑ y : Fin 3 → ZMod 3,
          ZMod.stdAddChar (polynomial M b x - polynomial M b y) := by
        simp (config := { congrConsts := false }) only
          [Fintype.sum_mul_sum, sub_eq_add_neg, AddChar.map_add_eq_mul]
      _ = ∑ h : Fin 3 → ZMod 3, ∑ y : Fin 3 → ZMod 3,
          ZMod.stdAddChar (polynomial M b h + ((2 : ZMod 3) • M.mulVec h) ⬝ᵥ y) := by
        rw [Finset.sum_comm]
        calc
          _ = ∑ y : Fin 3 → ZMod 3, ∑ h : Fin 3 → ZMod 3,
              ZMod.stdAddChar (polynomial M b h + ((2 : ZMod 3) • M.mulVec h) ⬝ᵥ y) := by
            apply Finset.sum_congr rfl
            intro y _
            symm
            apply Fintype.sum_equiv (Equiv.addRight y)
            intro h
            change ZMod.stdAddChar _ =
              ZMod.stdAddChar (polynomial M b (h + y) - polynomial M b y)
            rw [polynomial_shift M hM]
          _ = _ := Finset.sum_comm
      _ = ∑ h : Fin 3 → ZMod 3, ZMod.stdAddChar (polynomial M b h) *
          (∑ y : Fin 3 → ZMod 3,
            ZMod.stdAddChar (((2 : ZMod 3) • M.mulVec h) ⬝ᵥ y)) := by
        simp (config := { congrConsts := false }) only [AddChar.map_add_eq_mul, Finset.mul_sum]
      _ = _ := by
        simp_rw (config := { congrConsts := false }) [character_orthogonality, hz]
        simp (config := { congrConsts := false }) [polynomial]
  apply Complex.ofReal_injective
  push_cast (config := { congrConsts := false })
  rw [← Complex.mul_conj']
  convert he using 1
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact AddChar.starComp_apply
    (by norm_num (config := { congrConsts := false }) [ZMod.ringChar_zmod_n] :
      0 < ringChar (ZMod 3)) (polynomial M b y)

private theorem spread_evaluation (g : Fin 3 → ZMod 3) (hg : g ≠ 0) :
    Function.Bijective (fun i : Fin 27 => (matrices i).mulVec g) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by norm_num (config := { congrConsts := false }) [Fintype.card_fun]⟩
  intro i j hij
  by_contra hne
  change matrices i *ᵥ g = matrices j *ᵥ g at hij
  have hu : IsUnit (matrices i - matrices j) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (spread i j hne))
  apply hg
  apply Matrix.mulVec_injective_iff_isUnit.mpr hu
  rw [Matrix.sub_mulVec, hij, sub_self, Matrix.mulVec_zero]

private theorem polynomial_unique (A B : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hA : A.IsSymm) (hB : B.IsSymm) (b c : Fin 3 → ZMod 3)
    (h : ∀ x, polynomial A b x = polynomial B c x) : A = B ∧ b = c := by
  have ht : (2 : ZMod 3) ≠ 0 := by decide
  have hp (x y : Fin 3 → ZMod 3) : 2 * (x ⬝ᵥ A.mulVec y - x ⬝ᵥ B.mulVec y) = 0 := by
    have hxy := h (x + y)
    have hx := h x
    have hy := h y
    simp (config := { congrConsts := false }) only
      [polynomial, Matrix.mulVec_add, dotProduct_add, add_dotProduct] at hxy hx hy
    rw [hA.dotProduct_mulVec_comm (x := y) (y := x),
      hB.dotProduct_mulVec_comm (x := y) (y := x)] at hxy
    linear_combination hxy - hx - hy
  have hAB : A = B := by
    apply Matrix.mulVec_injective
    funext y
    apply dotProduct_eq
    intro x
    simpa (config := { congrConsts := false }) only [dotProduct_comm] using
      sub_eq_zero.mp ((mul_eq_zero.mp (hp x y)).resolve_left ht)
  refine ⟨hAB, dotProduct_eq b c ?_⟩
  intro x
  exact add_left_cancel
    (by simpa (config := { congrConsts := false }) only [polynomial, hAB] using h x)

private theorem exponent_overlap (i k : Fin 27) (b c : Fin 3 → ZMod 3)
    (h : (i, b) ≠ (k, c)) :
    ‖∑ x : Fin 3 → ZMod 3,
      ZMod.stdAddChar (polynomial (matrices i) b x - polynomial (matrices k) c x)‖ ^ 2 = 0 ∨
    ‖∑ x : Fin 3 → ZMod 3,
      ZMod.stdAddChar (polynomial (matrices i) b x - polynomial (matrices k) c x)‖ ^ 2 = 27 := by
  classical
  by_cases hik : i = k
  · subst k
    have hbc : b ≠ c := by
      intro he
      exact h (by rw [he])
    left
    have he (x : Fin 3 → ZMod 3) :
        polynomial (matrices i) b x - polynomial (matrices i) c x = (b - c) ⬝ᵥ x := by
      simp (config := { congrConsts := false }) only [polynomial, sub_dotProduct]
      ring
    simp_rw (config := { congrConsts := false }) [he]
    rw [character_orthogonality, ite_eq_right (sub_ne_zero.mpr hbc)]
    norm_num (config := { congrConsts := false })
  · right
    have he : (∑ x : Fin 3 → ZMod 3,
        ZMod.stdAddChar (polynomial (matrices i) b x - polynomial (matrices k) c x)) =
        ∑ x : Fin 3 → ZMod 3,
          ZMod.stdAddChar (polynomial (matrices i - matrices k) (b - c) x) := by
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (fun k : ZMod 3 => ZMod.stdAddChar k)
      simp (config := { congrConsts := false }) only
        [polynomial, Matrix.sub_mulVec, dotProduct_sub, sub_dotProduct]
      ring
    rw [he]
    exact quadratic_energy _ ((matrices_symmetric i).sub (matrices_symmetric k))
      (spread i k hik) (b - c)

private theorem quadratic_rectangle (M : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hM : M.IsSymm) (a₁ a₂ b₁ b₂ : Fin 3 → ZMod 3) (hs : a₁ + a₂ = b₁ + b₂) :
    a₁ ⬝ᵥ M.mulVec a₁ + a₂ ⬝ᵥ M.mulVec a₂ - b₁ ⬝ᵥ M.mulVec b₁ - b₂ ⬝ᵥ M.mulVec b₂ =
      ((2 : ZMod 3) • (a₁ - b₁)) ⬝ᵥ M.mulVec (a₁ - b₂) := by
  have ha₂ : a₂ = b₁ + b₂ - a₁ :=
    eq_sub_iff_add_eq.mpr ((add_comm a₂ a₁).trans hs)
  rw [ha₂]
  simp (config := { congrConsts := false }) only
    [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, dotProduct_sub,
    add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hM.dotProduct_mulVec_comm (x := b₁) (y := a₁),
    hM.dotProduct_mulVec_comm (x := b₂) (y := a₁),
    hM.dotProduct_mulVec_comm (x := b₂) (y := b₁)]
  ring

private theorem exponent_moment (a₁ a₂ b₁ b₂ : Fin 3 → ZMod 3) :
    (let S := ∑ i : Fin 27, ∑ c : Fin 3 → ZMod 3,
      ZMod.stdAddChar (polynomial (matrices i) c a₁ + polynomial (matrices i) c a₂ -
        polynomial (matrices i) c b₁ - polynomial (matrices i) c b₂)
    (((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁)) → S = 729) ∧
    ((¬ ((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁))) → S = 0)) := by
  classical
  dsimp only
  constructor
  · intro h
    have hz (i : Fin 27) (c : Fin 3 → ZMod 3) :
        polynomial (matrices i) c a₁ + polynomial (matrices i) c a₂ -
          polynomial (matrices i) c b₁ - polynomial (matrices i) c b₂ = 0 := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
    simp_rw (config := { congrConsts := false }) [hz, AddChar.map_zero_eq_one]
    norm_num (config := { congrConsts := false }) [Fintype.card_fun]
  · intro hn
    let s := a₁ + a₂ - b₁ - b₂
    let q := fun i : Fin 27 => a₁ ⬝ᵥ (matrices i).mulVec a₁ +
      a₂ ⬝ᵥ (matrices i).mulVec a₂ - b₁ ⬝ᵥ (matrices i).mulVec b₁ -
      b₂ ⬝ᵥ (matrices i).mulVec b₂
    have he (i : Fin 27) (c : Fin 3 → ZMod 3) :
        polynomial (matrices i) c a₁ + polynomial (matrices i) c a₂ -
          polynomial (matrices i) c b₁ - polynomial (matrices i) c b₂ = q i + s ⬝ᵥ c := by
      rw [dotProduct_comm s c]
      dsimp only [q, s]
      simp (config := { congrConsts := false }) only [polynomial, dotProduct_add, dotProduct_sub]
      ring
    have hsum : (∑ i : Fin 27, ∑ c : Fin 3 → ZMod 3,
        ZMod.stdAddChar (polynomial (matrices i) c a₁ + polynomial (matrices i) c a₂ -
          polynomial (matrices i) c b₁ - polynomial (matrices i) c b₂)) =
        (∑ i : Fin 27, ZMod.stdAddChar (q i)) * (if s = 0 then (27 : ℂ) else 0) := by
      simp_rw (config := { congrConsts := false })
        [he, AddChar.map_add_eq_mul, ← Finset.mul_sum, character_orthogonality]
      exact (Finset.sum_mul _ _ _).symm
    rw [hsum]
    by_cases hs : s = 0
    · rw [ite_eq_left hs]
      have hpair : a₁ + a₂ = b₁ + b₂ :=
        sub_eq_zero.mp (by simpa (config := { congrConsts := false }) only [s, sub_sub] using hs)
      have hh : a₁ - b₁ ≠ 0 := by
        intro hz
        have ha : a₁ = b₁ := sub_eq_zero.mp hz
        apply hn
        exact Or.inl ⟨ha, add_left_cancel (by simpa (config := { congrConsts := false }) only
          [ha] using hpair)⟩
      have hg : a₁ - b₂ ≠ 0 := by
        intro hz
        have ha : a₁ = b₂ := sub_eq_zero.mp hz
        apply hn
        refine Or.inr ⟨ha, ?_⟩
        apply add_left_cancel (a := b₂)
        calc
          b₂ + a₂ = a₁ + a₂ := by rw [ha]
          _ = b₁ + b₂ := hpair
          _ = b₂ + b₁ := add_comm _ _
      have hq (i : Fin 27) : q i =
          ((2 : ZMod 3) • (a₁ - b₁)) ⬝ᵥ (matrices i).mulVec (a₁ - b₂) :=
        quadratic_rectangle _ (matrices_symmetric i) _ _ _ _ hpair
      have hzero : (∑ i : Fin 27, ZMod.stdAddChar (q i)) = 0 := by
        calc
          _ = ∑ i : Fin 27, ZMod.stdAddChar
              (((2 : ZMod 3) • (a₁ - b₁)) ⬝ᵥ (matrices i).mulVec (a₁ - b₂)) := by
            simp_rw (config := { congrConsts := false }) [hq]
          _ = ∑ y : Fin 3 → ZMod 3,
              ZMod.stdAddChar (((2 : ZMod 3) • (a₁ - b₁)) ⬝ᵥ y) :=
            Fintype.sum_bijective _ (spread_evaluation _ hg) _ _ (fun _ => rfl)
          _ = 0 := by
            rw [character_orthogonality, ite_eq_right (smul_ne_zero (by decide) hh)]
      rw [hzero, zero_mul]
    · rw [ite_eq_right hs, mul_zero]

private theorem point_injective : Function.Injective point := by
  classical
  intro p q hp
  by_contra hne
  have he (x : Fin 3 → ZMod 3) : polynomial (matrices p.1) p.2 x =
      polynomial (matrices q.1) q.2 x := by
    apply phase_injective
    have hp_at := congrFun hp (coord.symm x)
    rw [point, point] at hp_at
    simpa (config := { congrConsts := false }) only [Equiv.apply_symm_apply] using hp_at
  have hs : (∑ x : Fin 3 → ZMod 3,
      ZMod.stdAddChar (polynomial (matrices p.1) p.2 x - polynomial (matrices q.1) q.2 x)) =
      27 := by
    simp_rw (config := { congrConsts := false }) [he, sub_self, AddChar.map_zero_eq_one]
    norm_num (config := { congrConsts := false }) [Fintype.card_fun]
  rcases exponent_overlap p.1 q.1 p.2 q.2 hne with hz | hz
  all_goals rw [hs] at hz; norm_num (config := { congrConsts := false }) at hz

private theorem counterexample_anchored :
    ∀ φ ∈ counterexample, φ ⟨0, by decide⟩ = 0 := by
  classical
  intro φ hφ
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hφ
  change phase_map (polynomial (matrices p.1) p.2 (coord 0)) = 0
  rw [coord_zero]
  norm_num (config := { congrConsts := false }) [polynomial]

private theorem counterexample_card : counterexample.card = 27 ^ 2 := by
  classical
  rw [counterexample, Finset.card_image_of_injective _ point_injective]
  norm_num (config := { congrConsts := false }) [Fintype.card_fun]

private theorem counterexample_design : design2 counterexample := by
  classical
  intro a₁ a₂ b₁ b₂
  have he : (∑ φ ∈ counterexample,
      (Real.Angle.toCircle (φ a₁ + φ a₂ - φ b₁ - φ b₂) : ℂ)) =
      ∑ i : Fin 27, ∑ c : Fin 3 → ZMod 3,
        ZMod.stdAddChar (polynomial (matrices i) c (coord a₁) +
          polynomial (matrices i) c (coord a₂) - polynomial (matrices i) c (coord b₁) -
          polynomial (matrices i) c (coord b₂)) := by
    rw [counterexample, Finset.sum_image (fun _ _ _ _ h => point_injective h),
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro c _
    change (Real.Angle.toCircle (phase_map _ + phase_map _ - phase_map _ - phase_map _) : ℂ) = _
    rw [← map_add phase_map, ← map_sub phase_map, ← map_sub phase_map]
    exact phase_character _
  have hm := exponent_moment (coord a₁) (coord a₂) (coord b₁) (coord b₂)
  have hc : (counterexample.card : ℂ) = 729 := by
    rw [counterexample_card]
    norm_num (config := { congrConsts := false })
  constructor
  · intro h
    rw [he, hc]
    exact hm.1 (by simpa (config := { congrConsts := false }) only [coord.injective.eq_iff] using h)
  · intro h
    rw [he]
    exact hm.2 (by simpa (config := { congrConsts := false }) only [coord.injective.eq_iff] using h)

private theorem counterexample_overlap : mubOverlap counterexample := by
  classical
  intro φ hφ θ hθ hne
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hφ
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hθ
  have hpq : p ≠ q := by rintro rfl; exact hne rfl
  have he : (∑ j : Fin 27, (Real.Angle.toCircle (point p j - point q j) : ℂ)) =
      ∑ x : Fin 3 → ZMod 3,
        ZMod.stdAddChar (polynomial (matrices p.1) p.2 x - polynomial (matrices q.1) q.2 x) := by
    apply Fintype.sum_equiv coord
    intro j
    change (Real.Angle.toCircle (phase_map _ - phase_map _) : ℂ) = _
    rw [← map_sub phase_map]
    exact phase_character _
  rw [he]
  exact exponent_overlap p.1 q.1 p.2 q.2 hpq

private theorem counterexample_zero : 0 ∈ counterexample := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(0, 0), Finset.mem_univ _, ?_⟩
  funext j
  change phase_map (polynomial (matrices 0) 0 (coord j)) = 0
  have hz : matrices 0 = 0 := by decide
  simp (config := { congrConsts := false }) [polynomial, hz]

private theorem counterexample_not_group :
    ¬ ∃ H : AddSubgroup (Fin 27 → Real.Angle),
      (H : Set (Fin 27 → Real.Angle)) = ↑counterexample := by
  classical
  rintro ⟨H, hH⟩
  have hm (p : Fin 27 × (Fin 3 → ZMod 3)) : point p ∈ H := by
    change point p ∈ (H : Set (Fin 27 → Real.Angle))
    rw [hH]
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  have hs := H.add_mem (hm (1, 0)) (hm (3, 0))
  change point (1, 0) + point (3, 0) ∈ (H : Set (Fin 27 → Real.Angle)) at hs
  rw [hH] at hs
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hs
  have he (x : Fin 3 → ZMod 3) : polynomial (matrices p.1) p.2 x =
      polynomial (matrices 1 + matrices 3) 0 x := by
    apply phase_injective
    calc
      _ = phase_map (polynomial (matrices 1) 0 x) +
          phase_map (polynomial (matrices 3) 0 x) := by
        simpa (config := { congrConsts := false }) only
          [point, Pi.add_apply, Equiv.apply_symm_apply] using
          congrFun hp (coord.symm x)
      _ = _ := by
        rw [← map_add phase_map]
        congr 1
        simp (config := { congrConsts := false }) only
          [polynomial, Matrix.add_mulVec, dotProduct_add, zero_dotProduct, add_zero]
  exact matrices_not_add p.1
    (polynomial_unique _ _ (matrices_symmetric p.1)
      ((matrices_symmetric 1).add (matrices_symmetric 3)) p.2 0 he).1

theorem result : ¬ claim := by
  intro h
  exact counterexample_not_group
    (h 27 (by decide) counterexample counterexample_anchored counterexample_card
      counterexample_design counterexample_overlap counterexample_zero)

end D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup
