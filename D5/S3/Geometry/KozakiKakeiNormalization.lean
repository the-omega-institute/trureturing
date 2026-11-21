/- GID: D5/S3/Geometry/KozakiKakeiNormalization
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Existence and uniqueness of the source double normal form on the even level locus. -/
import D5.S3.Geometry.KozakiKakeiMatrixEquiv
import Mathlib.Tactic.FieldSimp

namespace D5.S3.Geometry.KozakiKakei
open scoped BigOperators
noncomputable section

def UnitAdjacent {m : ℕ} (Z : Chart K m) : Prop :=
  ∀ (i : Col m) (hi : i.val + 1 < 2 * m), minor Z i ⟨i.val + 1, hi⟩ = 1

private theorem consecutive_products {m : ℕ} (hm : 2 ≤ m) {Z : Chart K m}
    (h : UnitAdjacent Z) :
    oddProduct Z = 1 ∧ evenProduct Z = minor Z (first hm) (last hm) := by
  constructor
  · unfold oddProduct
    apply Finset.prod_eq_one
    intro i _
    exact h (oddVertex (i, false)) (by have := i.isLt; change 2*i.val+1 < 2*m; omega)
  · unfold evenProduct
    let e : Fin m := ⟨0, by omega⟩
    rw [Finset.prod_eq_single e]
    · rfl
    · intro j _ hj
      have hj0 : j.val ≠ 0 := fun hh => hj (Fin.ext hh)
      have hleft : (evenVertex (j, false)).val = 2 * j.val - 1 := by simp [evenVertex, hj0]
      have hr : (evenVertex (j, true)).val = 2 * j.val := by simp [evenVertex, hj0]
      have hjlt := j.isLt
      have hbound : (evenVertex (j, false)).val + 1 < 2*m := by rw [hleft]; omega
      have he : (⟨(evenVertex (j, false)).val + 1, hbound⟩ : Col m) = evenVertex (j, true) :=
        Fin.ext (by
          change (evenVertex (j, false)).val + 1 = (evenVertex (j, true)).val
          rw [hleft, hr]
          omega)
      simpa only [he] using h (evenVertex (j, false)) hbound
    · simp

theorem normalized_level {m : ℕ} {hm : 2 ≤ m} {Z : Chart K m} (h : Normalized hm Z) :
    evenProduct Z = oddProduct Z := by
  obtain ⟨_, _, _, _, _, _, _, hadj, hlast⟩ := h
  obtain ⟨ho, he⟩ := consecutive_products hm (Z := Z) hadj
  rw [he, hlast, ho]

private def adjacentMinor {m : ℕ} (Z : Chart K m) (i : ℕ) : K :=
  if h : i + 1 < 2*m then minor Z ⟨i, by omega⟩ ⟨i+1, h⟩ else 1

private theorem adjacentMinor_ne_zero {m : ℕ} {Z : Chart K m} (hZ : Admissible Z) (i : ℕ) :
    adjacentMinor Z i ≠ 0 := by
  unfold adjacentMinor
  split
  · apply hZ
    intro h
    have h' := congrArg Fin.val h
    dsimp at h'
    omega
  · exact one_ne_zero

private def scaleSequence {m : ℕ} (Z : Chart K m) (d initial : K) : ℕ → K
  | 0 => initial
  | i + 1 => (d * scaleSequence Z d initial i * adjacentMinor Z i)⁻¹

private theorem scaleSequence_ne_zero {m : ℕ} {Z : Chart K m} (hZ : Admissible Z)
    {d initial : K} (hd : d ≠ 0) (hinit : initial ≠ 0) (i : ℕ) :
    scaleSequence Z d initial i ≠ 0 := by
  induction i with
  | zero => exact hinit
  | succ i ih =>
    rw [scaleSequence]
    exact inv_ne_zero (mul_ne_zero (mul_ne_zero hd ih) (adjacentMinor_ne_zero hZ i))

theorem normalized_exists {m : ℕ} (hm : 2 ≤ m) {Z : Chart K m} (hZ : Admissible Z)
    (hlevel : evenProduct Z = oddProduct Z) :
    ∃ W, Normalized hm W ∧ MatEquivalent W Z := by
  let v₀ := first hm
  let v₁ := second hm
  let v₂ := third hm
  have hn₀₁ : v₀ ≠ v₁ := by intro h; have := congrArg Fin.val h; contradiction
  have hn₀₂ : v₀ ≠ v₂ := by intro h; have := congrArg Fin.val h; contradiction
  have hn₁₂ : v₁ ≠ v₂ := by
    intro h
    have he : 1 = (2 : ℕ) := congrArg Fin.val h
    omega
  let d₀₁ := minor Z v₀ v₁
  let d₀₂ := minor Z v₀ v₂
  let d₁₂ := minor Z v₁ v₂
  have h₀₁ : d₀₁ ≠ 0 := hZ v₀ v₁ hn₀₁
  have h₀₂ : d₀₂ ≠ 0 := hZ v₀ v₂ hn₀₂
  have h₁₂ : d₁₂ ≠ 0 := hZ v₁ v₂ hn₁₂
  let μ := d₁₂ / d₀₂
  have hμ : μ ≠ 0 := div_ne_zero h₁₂ h₀₂
  let L : Square := !![-(μ * Z 1 v₀), μ * Z 0 v₀; -Z 1 v₁, Z 0 v₁]
  let δ := L.det
  have hdet : δ = μ * d₀₁ := by
    rw [show δ = L.det from rfl, Matrix.det_fin_two]
    simp only [L, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val', Fin.isValue]
    change -(μ * Z 1 v₀) * Z 0 v₁ - μ * Z 0 v₀ * (-Z 1 v₁) = μ * d₀₁
    unfold d₀₁ minor
    ring
  have hδ : δ ≠ 0 := by rw [hdet]; exact mul_ne_zero hμ h₀₁
  let scales := scaleSequence Z δ d₀₁⁻¹
  have hscale (i : ℕ) : scales i ≠ 0 := scaleSequence_ne_zero hZ hδ (inv_ne_zero h₀₁) i
  let d : Col m → K := fun i => scales i.val
  let W := scaled L d Z
  have hWadm : Admissible W := scaled_admissible hδ (fun i => hscale i.val) hZ
  have hWadj : UnitAdjacent W := by
    intro i hi
    have hminor : adjacentMinor Z i.val = minor Z i ⟨i.val + 1, hi⟩ := by
      simp [adjacentMinor, hi]
    rw [show W = scaled L d Z from rfl, minor_scaled]
    change δ * scales i.val * scales (i.val + 1) * minor Z i ⟨i.val + 1, hi⟩ = 1
    rw [← hminor]
    have hs : scales (i.val+1) = (δ * scales i.val * adjacentMinor Z i.val)⁻¹ := rfl
    rw [hs]
    have hprod : δ * scales i.val * adjacentMinor Z i.val ≠ 0 :=
      mul_ne_zero (mul_ne_zero hδ (hscale _)) (adjacentMinor_ne_zero hZ _)
    calc
      _ = (δ * scales i.val * adjacentMinor Z i.val) *
            (δ * scales i.val * adjacentMinor Z i.val)⁻¹ := by ac_rfl
      _ = 1 := mul_inv_cancel₀ hprod
  have hWlevel : evenProduct W = oddProduct W :=
    (level_scaled_iff hδ (fun i => hscale i.val) Z).mpr hlevel
  obtain ⟨hO, hE⟩ := consecutive_products hm hWadj
  have hWlast : minor W v₀ (last hm) = 1 := by rwa [hE, hO] at hWlevel
  have ha₀ : adjacentMinor Z 0 = d₀₁ := by
    rw [adjacentMinor, dite_eq_left (by omega)]
    rfl
  have ha₁ : adjacentMinor Z 1 = d₁₂ := by
    rw [adjacentMinor, dite_eq_left (by omega)]
    rfl
  have hscale₀ : scales 0 = d₀₁⁻¹ := rfl
  have hscale₁ : scales 1 = δ⁻¹ := by
    change (δ * scales 0 * adjacentMinor Z 0)⁻¹ = δ⁻¹
    rw [hscale₀, ha₀, mul_assoc, inv_mul_cancel₀ h₀₁, mul_one]
  have hscale₂ : scales 2 = d₁₂⁻¹ := by
    change (δ * scales 1 * adjacentMinor Z 1)⁻¹ = d₁₂⁻¹
    rw [hscale₁, ha₁, mul_inv_cancel₀ hδ, one_mul]
  have hrow₀ (i : Col m) : W 0 i = (μ * minor Z v₀ i) * d i := by
    rw [show W = scaled L d Z from rfl, scaled_apply]
    change (-(μ * Z 1 v₀) * Z 0 i + μ * Z 0 v₀ * Z 1 i) * d i = _
    unfold minor
    ring
  have hrow₁ (i : Col m) : W 1 i = minor Z v₁ i * d i := by
    rw [show W = scaled L d Z from rfl, scaled_apply]
    change ((-Z 1 v₁) * Z 0 i + Z 0 v₁ * Z 1 i) * d i = _
    unfold minor
    ring
  have hcol₀₀ : W 0 v₀ = 0 := by rw [hrow₀]; simp [minor, mul_comm]
  have hcol₁₀ : W 1 v₀ = -1 := by
    rw [hrow₁, minor_swap Z v₁ v₀]
    change -d₀₁ * scales 0 = -1
    rw [hscale₀, neg_mul, mul_inv_cancel₀ h₀₁]
  have hcol₀₁ : W 0 v₁ = 1 := by
    rw [hrow₀]
    change μ * d₀₁ * scales 1 = 1
    rw [← hdet, hscale₁, mul_inv_cancel₀ hδ]
  have hcol₁₁ : W 1 v₁ = 0 := by rw [hrow₁]; simp [minor, mul_comm]
  have hcol₀₂ : W 0 v₂ = 1 := by
    rw [hrow₀]
    change μ * d₀₂ * scales 2 = 1
    rw [show μ * d₀₂ = d₁₂ from div_mul_cancel₀ _ h₀₂, hscale₂, mul_inv_cancel₀ h₁₂]
  have hcol₁₂ : W 1 v₂ = 1 := by
    rw [hrow₁]
    change d₁₂ * scales 2 = 1
    rw [hscale₂, mul_inv_cancel₀ h₁₂]
  have hLu : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr hδ.isUnit
  refine ⟨W, ⟨hWadm, hcol₀₀, hcol₁₀, hcol₀₁, hcol₁₁, hcol₀₂, hcol₁₂, hWadj, hWlast⟩,
    hLu.unit, fun i => Units.mk0 (d i) (hscale i.val), ?_⟩
  change W = scaled hLu.unit.val d Z
  rw [IsUnit.unit_spec]

theorem normalized_unique_of_equiv {m : ℕ} {hm : 2 ≤ m} {Z W : Chart K m}
    (hZ : Normalized hm Z) (hW : Normalized hm W) (h : MatEquivalent W Z) : W = Z := by
  obtain ⟨_, z₀₀, z₁₀, z₀₁, z₁₁, z₀₂, z₁₂, zAdj, _⟩ := hZ
  obtain ⟨_, w₀₀, w₁₀, w₀₁, w₁₁, w₀₂, w₁₂, wAdj, _⟩ := hW
  obtain ⟨L, d, heq⟩ := h
  change W = scaled L.val (fun i => (d i).val) Z at heq
  let D := fun i => (d i).val
  let L' := L.val
  have apply_W (a : Fin 2) (i : Col m) :
      W a i = (L' a 0 * Z 0 i + L' a 1 * Z 1 i) * D i := by rw [heq, scaled_apply]
  have h₀₁ : L' 0 1 = 0 := by
    rw [apply_W, z₀₀, z₁₀, mul_zero, mul_neg_one, zero_add, neg_mul] at w₀₀
    exact (mul_eq_zero.mp (neg_eq_zero.mp w₀₀)).resolve_right (d _).ne_zero
  have h₁₀ : L' 1 0 = 0 := by
    rw [apply_W, z₀₁, z₁₁, mul_one, mul_zero, add_zero] at w₁₁
    exact (mul_eq_zero.mp w₁₁).resolve_right (d _).ne_zero
  have h₀ : L' 0 0 * D (second hm) = 1 := by
    simpa only [apply_W, z₀₁, z₁₁, mul_one, mul_zero, add_zero] using w₀₁
  have h₁ : L' 1 1 * D (first hm) = 1 := by
    rw [apply_W, z₀₀, z₁₀, mul_zero, mul_neg_one, zero_add, neg_mul] at w₁₀
    exact neg_injective w₁₀
  have h₂ : L' 0 0 * D (third hm) = 1 := by
    simpa only [apply_W, z₀₂, z₁₂, h₀₁, mul_one, add_zero] using w₀₂
  have h₃ : L' 1 1 * D (third hm) = 1 := by
    simpa only [apply_W, z₀₂, z₁₂, h₁₀, mul_one, zero_add] using w₁₂
  have hL₀ : L' 0 0 ≠ 0 := by intro hz; rw [hz, zero_mul] at h₀; exact zero_ne_one h₀
  have hL₁ : L' 1 1 ≠ 0 := by intro hz; rw [hz, zero_mul] at h₁; exact zero_ne_one h₁
  have hd₁ : D (second hm) = D (first hm) :=
    (mul_left_cancel₀ hL₀ (h₀.trans h₂.symm)).trans (mul_left_cancel₀ hL₁ (h₃.trans h₁.symm))
  have hscales (i : Col m) (hi : i.val + 1 < 2*m) :
      L'.det * D i * D ⟨i.val + 1, hi⟩ = 1 := by
    have h := wAdj i hi
    rw [heq, minor_scaled, zAdj i hi, mul_one] at h
    exact h
  have hstart : L'.det * D (first hm) * D (first hm) = 1 := by
    rw [← hd₁]
    have h := hscales (first hm) (by change 1 < 2*m; omega)
    change L'.det * D (first hm) * D (second hm) = 1 at h
    rw [hd₁] at h
    simpa only [hd₁] using h
  have hall (i : Col m) : D i = D (first hm) := by
    have hn : ∀ (k : ℕ) (hk : k < 2*m), D ⟨k,hk⟩ = D (first hm) := by
      intro k
      induction k with
      | zero => intro hk; rfl
      | succ k ih =>
        intro hk
        have hs := hscales ⟨k, by omega⟩ hk
        rw [ih (by omega)] at hs
        exact mul_left_cancel₀ (mul_ne_zero (unit_det_ne_zero L) (d _).ne_zero) (hs.trans hstart.symm)
    exact hn i.val i.isLt
  ext a i
  rw [apply_W, hall i]
  fin_cases a
  · change (L' 0 0 * Z 0 i + L' 0 1 * Z 1 i) * D (first hm) = Z 0 i
    rw [h₀₁, zero_mul, add_zero, mul_right_comm, ← hd₁, h₀, one_mul]
  · change (L' 1 0 * Z 0 i + L' 1 1 * Z 1 i) * D (first hm) = Z 1 i
    rw [h₁₀, zero_mul, zero_add, mul_right_comm, h₁, one_mul]

theorem normalized_representative_iff {m : ℕ} (hm : 2 ≤ m) (Z : Chart K m)
    (hZ : Admissible Z) :
    (∃! W, Normalized hm W ∧ MatEquivalent W Z) ↔ evenProduct Z = oddProduct Z := by
  constructor
  · rintro ⟨W, ⟨hW, heq⟩, _⟩
    exact (level_equiv heq).mp (normalized_level hW)
  · intro h
    obtain ⟨W, hW, heq⟩ := normalized_exists hm hZ h
    refine ⟨W, ⟨hW, heq⟩, ?_⟩
    rintro V ⟨hV, hv⟩
    exact normalized_unique_of_equiv hW hV (matEquivalent_trans hv (matEquivalent_symm heq))

#print axioms normalized_representative_iff

end
end D5.S3.Geometry.KozakiKakei
