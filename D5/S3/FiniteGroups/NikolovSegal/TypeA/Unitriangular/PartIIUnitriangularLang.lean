/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite explicit inverses and root-weight obstructions for the height-torus Lang map. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLangLinear
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularActions
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnitriangular

set_option autoImplicit false

/-! The height-torus Lang map on the upper-unitriangular subgroup has a finite
inverse under root-weight nonresonance and explicit obstructions at resonant roots. -/
namespace NikolovSegal.PartIIUnitriangularLang

open Matrix PartIIUnitriangularLayers PartIIUnitriangularActions SLnNormalizer
open scoped BigOperators

universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) F

theorem uplus_depth (g : Uplus n F) : LayerDepth 1 (g.val.val - 1) := by
  rcases (mem_Uplus_iff g.val).mp g.property with ⟨hu, hd⟩
  intro i j hij
  by_cases he : i = j
  · subst j
    simp [Matrix.sub_apply, hd i]
  · have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
    have hji : j.val < i.val := by omega
    simp [Matrix.sub_apply, Matrix.one_apply, he, hu i j hji]

theorem depth_mem_Uplus (g : SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val - 1)) : g ∈ Uplus n F := by
  apply (mem_Uplus_iff g).mpr
  constructor
  · intro i j hij
    have he : i ≠ j := by intro h; subst j; omega
    have h := hg i j (by omega)
    simpa only [Matrix.sub_apply, Matrix.one_apply, if_neg he, sub_zero] using h
  · intro i
    have h := hg i i (by omega)
    exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply, Matrix.one_apply_eq] using h)

/-- A genuine element of the EXISTING subgroup of SL, constructed from its
    matrix entries. The determinant proof uses upper triangularity directly. -/
noncomputable def unitOfStrict (X : Mat) (hX : LayerDepth 1 X) : Uplus n F :=
  ⟨⟨1 + X, by
    classical
    have ht : Matrix.IsUpperTriangular (1 + X) := by
      intro i j hij
      have hji : j.val < i.val := hij
      have he : i ≠ j := by intro h; subst j; omega
      simp [Matrix.add_apply, Matrix.one_apply, he, hX i j (by omega)]
    rw [Matrix.det_of_isUpperTriangular ht]
    apply Finset.prod_eq_one
    intro i hi
    simp [Matrix.add_apply, hX i i (by omega)]⟩,
    depth_mem_Uplus _ (by
      change LayerDepth 1 ((1 + X) - 1)
      simpa only [add_sub_cancel_left] using hX)⟩

/-- Restriction of the existing heightTorus, with its actual inverse, to
    the existing actual Uplus. No abstract replacement group is introduced. -/
noncomputable def sigma (a : Fˣ) : MulAut (Uplus n F) where
  toFun g := ⟨heightTorus a g.val,
    depth_mem_Uplus _ (torus_depth a 1 g.val (uplus_depth g))⟩
  invFun g := ⟨heightTorus a⁻¹ g.val,
    depth_mem_Uplus _ (torus_depth a⁻¹ 1 g.val (uplus_depth g))⟩
  left_inv g := by
    apply Subtype.ext
    exact (heightTorus a).left_inv g.val
  right_inv g := by
    apply Subtype.ext
    exact (heightTorus a).right_inv g.val
  map_mul' g h := by
    apply Subtype.ext
    exact (heightTorus a).map_mul g.val h.val

/-- The requested orientation is Sigma(g) * g^{-1}. -/
noncomputable def psi (a : Fˣ) (g : Uplus n F) : Uplus n F :=
  sigma a g * g⁻¹

theorem heightTorus_upper_entry (a : Fˣ) (g : SpecialLinearGroup (Fin n) F)
    (i j : Fin n) (hij : i.val ≤ j.val) :
    heightTorus a g i j = (a : F) ^ (j.val - i.val) * g i j := by
  rw [torus_entry]
  have hp : (a : F) ^ j.val = (a : F) ^ i.val * (a : F) ^ (j.val - i.val) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : ((a⁻¹ : Fˣ) : F) ^ i.val * (a : F) ^ i.val = 1 := by
    rw [← mul_pow]
    simp
  rw [hp]
  calc
    _ = (((a⁻¹ : Fˣ) : F) ^ i.val * (a : F) ^ i.val) *
        ((a : F) ^ (j.val - i.val) * g i j) := by ring
    _ = _ := by rw [hc, one_mul]

/-- The matrix difference is tied to the existing automorphism, rather
    than introduced as an assumed action/decomposition. -/
theorem heightTorus_delta (a : Fˣ) (g : SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val - 1)) :
    (heightTorus a g).val = g.val + delta a (g.val - 1) := by
  ext i j
  by_cases hij : i.val ≤ j.val
  · rw [Matrix.add_apply, heightTorus_upper_entry a g i j hij]
    by_cases he : i = j
    · subst j
      simp [delta]
    · simp only [delta, Matrix.sub_apply, Matrix.one_apply, if_neg he, sub_zero]
      ring
  · have hji : j.val < i.val := by omega
    have he : i ≠ j := by intro h; subst j; omega
    have hzero : g i j = 0 := by
      simpa only [Matrix.sub_apply, Matrix.one_apply, if_neg he, sub_zero]
        using hg i j (by omega)
    rw [Matrix.add_apply, torus_entry]
    simp [delta, Matrix.sub_apply, Matrix.one_apply, he, hzero]

theorem psi_eq_iff_delta (a : Fˣ) (g y : Uplus n F) :
    psi a g = y ↔
      delta a (g.val.val - 1) =
        (y.val.val - 1) + (y.val.val - 1) * (g.val.val - 1) := by
  have hgroup : psi a g = y ↔ sigma a g = y * g := by
    change sigma a g * g⁻¹ = y ↔ sigma a g = y * g
    constructor
    · intro h
      calc
        sigma a g = (sigma a g * g⁻¹) * g := by simp [mul_assoc]
        _ = y * g := by rw [h]
    · intro h
      rw [h]
      simp [mul_assoc]
  rw [hgroup]
  constructor
  · intro h
    have hm := congrArg (fun z : Uplus n F => z.val.val) h
    change (heightTorus a g.val).val = y.val.val * g.val.val at hm
    rw [heightTorus_delta a g.val (uplus_depth g)] at hm
    calc
      delta a (g.val.val - 1) = y.val.val * g.val.val - g.val.val := by
        rw [← hm]
        noncomm_ring
      _ = (y.val.val - 1) + (y.val.val - 1) * (g.val.val - 1) := by noncomm_ring
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    change (heightTorus a g.val).val = y.val.val * g.val.val
    rw [heightTorus_delta a g.val (uplus_depth g), h]
    noncomm_ring

/-- The displayed finite sum defines an actual Uplus element. Nonresonance
    is a hypothesis of the inverse laws, not a hidden assumption of a model. -/
noncomputable def langInverse (a : Fˣ) (y : Uplus n F) : Uplus n F :=
  unitOfStrict (finiteSolution a (y.val.val - 1))
    (finiteSolution_depth a (uplus_depth y))

theorem langInverse_matrix (a : Fˣ) (y : Uplus n F) :
    (langInverse a y).val.val = 1 +
      ∑ k ∈ Finset.range (n - 1),
        ((targetOp a (y.val.val - 1)) ^ k) (deltaInv a (y.val.val - 1)) := by
  change 1 + finiteSolution a (y.val.val - 1) = _
  rw [finiteSolution_eq_sum]

theorem psi_langInverse (a : Fˣ) (ha : Nonresonant (n := n) a)
    (y : Uplus n F) : psi a (langInverse a y) = y := by
  apply (psi_eq_iff_delta a _ y).mpr
  simpa only [langInverse_matrix, add_sub_cancel_left, finiteSolution_eq_sum]
    using finiteSolution_equation a ha (uplus_depth y)

theorem langInverse_psi (a : Fˣ) (ha : Nonresonant (n := n) a)
    (g : Uplus n F) : langInverse a (psi a g) = g := by
  have he := (psi_eq_iff_delta a g (psi a g)).mp rfl
  have huniq := finiteSolution_unique a ha (uplus_depth (psi a g)) (uplus_depth g) he
  apply Subtype.ext
  apply Subtype.ext
  change 1 + finiteSolution a ((psi a g).val.val - 1) = g.val.val
  rw [← huniq]
  abel

/-- Every resonant height supplies a specific unreachable transvection.
    The b*X entry is X_jj = 0; no induction over other resonant heights and
    no cardinality argument is involved. -/
theorem resonant_transvection_not_range (a : Fˣ) (d : ℕ)
    (hd : 1 ≤ d ∧ d < n) (ha : (a : F) ^ d = 1) :
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨d, hd.2⟩
    let y : Uplus n F :=
      ⟨SpecialLinearGroup.transvection (ne_of_lt (show i < j by change 0 < d; omega)) (1 : F),
        transvection_mem_Uplus (show i.val < j.val by change 0 < d; omega) (1 : F)⟩
    y ∉ Set.range (psi a) := by
  classical
  dsimp only
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨d, hd.2⟩
  let y : Uplus n F :=
    ⟨SpecialLinearGroup.transvection (ne_of_lt (show i < j by change 0 < d; omega)) (1 : F),
      transvection_mem_Uplus (show i.val < j.val by change 0 < d; omega) (1 : F)⟩
  change y ∉ Set.range (psi a)
  rintro ⟨g, hg⟩
  have he := (psi_eq_iff_delta a g y).mp hg
  have hb : y.val.val - 1 = Matrix.single i j (1 : F) := by
    change ((1 : Mat) + Matrix.single i j (1 : F)) - 1 = _
    abel
  rw [hb] at he
  have e := congrArg (fun X : Mat => X i j) he
  have hdiag : (g.val.val - 1) j j = 0 := uplus_depth g j j (by omega)
  have hw : (a : F) ^ (j.val - i.val) - 1 = 0 := by
    change (a : F) ^ (d - 0) - 1 = 0
    simp [ha]
  have hleft : delta a (g.val.val - 1) i j = 0 := by
    simp only [delta, hw, zero_mul]
  have hright : (Matrix.single i j (1 : F) +
      Matrix.single i j (1 : F) * (g.val.val - 1)) i j = 1 := by
    rw [Matrix.add_apply, Matrix.single_apply_same, Matrix.single_mul_apply_same,
      hdiag, mul_zero, add_zero]
  rw [hleft, hright] at e
  exact zero_ne_one e

/-- Exact arbitrary-field criterion in the actual model. Inverse laws above
    supply the finite inverse; surjectivity implies nonresonance by the
    explicit target obstruction. There are no rank/finite-field/characteristic
    assumptions beyond the quantified natural rank and field structure. -/
theorem heightTorus_lang_criterion (a : Fˣ) :
    (Function.Surjective (psi (n := n) a) ↔ Function.Bijective (psi (n := n) a)) ∧
    (Function.Bijective (psi (n := n) a) ↔
      ∀ d : ℕ, 1 ≤ d ∧ d < n → (a : F) ^ d ≠ 1) := by
  have necessary : Function.Surjective (psi (n := n) a) → Nonresonant (n := n) a := by
    intro hs d hd ha
    have h := resonant_transvection_not_range a d hd ha
    dsimp only at h
    exact h (hs _)
  have sufficient : Nonresonant (n := n) a → Function.Bijective (psi (n := n) a) := by
    intro ha
    constructor
    · intro g h he
      have e := congrArg (langInverse a) he
      simpa only [langInverse_psi a ha] using e
    · intro y
      exact ⟨langInverse a y, psi_langInverse a ha y⟩
  exact ⟨⟨fun h => sufficient (necessary h), fun h => h.2⟩,
    ⟨fun h => necessary h.2, sufficient⟩⟩

end NikolovSegal.PartIIUnitriangularLang
