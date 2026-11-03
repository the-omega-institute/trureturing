/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreRestore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreRestore
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Explicit signed insertion reconstructs the actual deleted height function. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreNormal

/-! Actual inverse insertion, with unit edges and exact residual invariants. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraCoreRestore
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreResidual MiuraCoreJoint MiuraSlabIncidence

variable {m n : ℕ}

/-- The inserted column repeats the preceding profile, translated by one signed step. -/
def restoreColumn (g : Cell m (n - 1) → ℤ) (j : Fin n)
    (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ) : Cell m n → ℤ :=
  fun p => if hp : p.2.val < j.val then
    g (p.1, ⟨p.2.val, by omega⟩)
  else g (p.1, ⟨p.2.val - 1, by have := p.2.isLt; omega⟩) + s

private theorem restore_horizontal (g : Cell m (n - 1) → ℤ) (hg : IsHeight g)
    (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (i : Fin m) (x y : Fin n) (hxy : x.val + 1 = y.val) :
    |restoreColumn g j hj0 hj1 s (i, x) - restoreColumn g j hj0 hj1 s (i, y)| = 1 := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases hyl : y.val < j.val
  · have hxl : x.val < j.val := by omega
    simp only [restoreColumn, hxl, hyl, dite_true]
    apply hg
    simp only [adj, gdist]
    omega
  · by_cases hxl : x.val < j.val
    · have hyj : y.val = j.val := by omega
      have he : (⟨x.val, by omega⟩ : Fin (n - 1)) = ⟨y.val - 1, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_mk]; omega)
      simp only [restoreColumn, hxl, hyl, dite_true, dite_false, he]
      rcases hs with rfl | rfl <;> simp
    · simp only [restoreColumn, hxl, hyl, dite_false]
      rw [add_sub_add_right_eq_sub]
      apply hg
      simp only [adj, gdist]
      omega

/-- Signed insertion preserves all unit grid edges, including its new seam. -/
theorem restoreColumn_isHeight (g : Cell m (n - 1) → ℤ) (hg : IsHeight g)
    (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ)
    (hs : s = 1 ∨ s = -1) : IsHeight (restoreColumn g j hj0 hj1 s) := by
  intro ⟨i, x⟩ ⟨k, y⟩ hpq
  have hadj := hpq
  simp only [adj, gdist] at hadj
  by_cases he : x = y
  · subst y
    by_cases hlt : x.val < j.val
    · simp only [restoreColumn, hlt, dite_true]
      apply hg
      simp only [adj, gdist]
      omega
    · simp only [restoreColumn, hlt, dite_false]
      rw [add_sub_add_right_eq_sub]
      apply hg
      simp only [adj, gdist]
      omega
  · have hne : x.val ≠ y.val := fun heq => he (Fin.ext heq)
    have her : i = k := Fin.ext (by omega)
    have hstep : x.val + 1 = y.val ∨ y.val + 1 = x.val := by omega
    subst k
    rcases hstep with hxy | hyx
    · exact restore_horizontal g hg j hj0 hj1 s hs i x y hxy
    · rw [abs_sub_comm]
      exact restore_horizontal g hg j hj0 hj1 s hs i y x hyx

/-- A constant signed seam is exactly the local information needed for a frozen insertion. -/
def SeamSlope (g : Cell m (n - 1) → ℤ) (j : Fin n)
    (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ) : Prop :=
  ∀ i : Fin m, g (i, ⟨j.val, by omega⟩) - g (i, ⟨j.val - 1, by omega⟩) = s

/-- Under its actual seam slope, the inserted column is genuinely frozen. -/
theorem restoreColumn_frozen (g : Cell m (n - 1) → ℤ) (j : Fin n)
    (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ)
    (hseam : SeamSlope g j hj0 hj1 s) :
    frozenColumn (restoreColumn g j hj0 hj1 s) j := by
  refine ⟨hj0, hj1, ?_⟩
  intro i
  have hs := hseam i
  have hl : j.val - 1 < j.val := by omega
  have hr : ¬ j.val + 1 < j.val := by omega
  simp only [restoreColumn, Fin.val_mk, hl, hr, lt_self_iff_false,
    dite_true, dite_false, Nat.add_sub_cancel]
  omega

private theorem restored_slope (g : Cell m (n - 1) → ℤ) (hm : 0 < m)
    (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ)
    (hfr : frozenColumn (restoreColumn g j hj0 hj1 s) j) :
    frozenSlope (restoreColumn g j hj0 hj1 s) hm j hfr = s := by
  have hl : j.val - 1 < j.val := by omega
  simp only [frozenSlope, restoreColumn, Fin.val_mk, lt_self_iff_false,
    hl, dite_true, dite_false]
  ring

/-- Contracting this insertion recovers the original complete function. -/
theorem contractAt_restoreColumn (g : Cell m (n - 1) → ℤ) (hm : 0 < m)
    (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ)
    (hseam : SeamSlope g j hj0 hj1 s) :
    contractAt (restoreColumn g j hj0 hj1 s) hm j
      (restoreColumn_frozen g j hj0 hj1 s hseam) = g := by
  funext p
  have hs := restored_slope g hm j hj0 hj1 s (restoreColumn_frozen g j hj0 hj1 s hseam)
  by_cases hp : p.2.val < j.val
  · simp only [contractAt, hp, ite_true, restoreColumn, Fin.val_mk, hp, dite_true]
  · have hpr : ¬ p.2.val + 1 < j.val := by omega
    simp only [contractAt, hp, ite_false, hs, restoreColumn, Fin.val_mk,
      hpr, dite_false, Nat.add_sub_cancel, add_sub_cancel_right]

/-- The explicit inverse returns every deleted and every retained value of the actual height. -/
theorem restoreColumn_contractAt (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) :
    restoreColumn (contractAt h hm j hj) j hj.1 hj.2.1 (frozenSlope h hm j hj) = h := by
  funext p
  have hp := p.2.isLt
  by_cases hl : p.2.val < j.val
  · simp only [restoreColumn, hl, dite_true, contractAt, Fin.val_mk, hl, ite_true]
  · by_cases he : p.2.val = j.val
    · have hprev : p.2.val - 1 < j.val := by have := hj.1; omega
      have hjp : p.2 = j := Fin.ext he
      have hsl := frozenSlope_eq h hh hm j hj p.1
      simp only [restoreColumn, hl, dite_false, contractAt, Fin.val_mk, hprev, ite_true]
      have heprev : (⟨p.2.val - 1, by omega⟩ : Fin n) =
          ⟨j.val - 1, by have := hj.1; omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      have hpval : h p = h (p.1, j) := congrArg h (Prod.ext rfl hjp)
      rw [heprev]
      omega
    · have hprev : ¬ p.2.val - 1 < j.val := by omega
      have hback : (⟨p.2.val - 1 + 1, by omega⟩ : Fin n) = p.2 := Fin.ext (by simp only [Fin.val_mk]; omega)
      simp only [restoreColumn, hl, dite_false, contractAt, Fin.val_mk, hprev, ite_false,
        hback, sub_add_cancel]

/-- Insertion with a genuine signed seam preserves the original exact residual class. -/
theorem restoreColumn_residual (a b : ℕ) (g : Cell m (n - 1) → ℤ) (hm : 0 < m)
    (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (hseam : SeamSlope g j hj0 hj1 s)
    (hg : Residual a b g) : Residual a b (restoreColumn g j hj0 hj1 s) := by
  let h := restoreColumn g j hj0 hj1 s
  have hh : IsHeight h := restoreColumn_isHeight g hg.1.1 j hj0 hj1 s hs
  have hf : frozenColumn h j := restoreColumn_frozen g j hj0 hj1 s hseam
  have he : contractAt h hm j hf = g := contractAt_restoreColumn g hm j hj0 hj1 s hseam
  refine ⟨⟨hh, ?_⟩, ?_, ?_, ?_⟩
  · intro p hp hq
    have hlt : p.2.val < j.val := by omega
    simp only [h, restoreColumn, hlt, dite_true]
    exact hg.1.2 _ hp hq
  · rw [← contractAt_minima_card h hh hm j hf, he]
    exact hg.2.1
  · rw [← contractAt_maxima_card h hh hm j hf, he]
    exact hg.2.2.1
  · rintro ⟨sd, hside⟩
    have hside' := (contractAt_all_minima_side_iff h hh hm j hf sd).mpr hside
    rw [he] at hside'
    exact hg.2.2.2 ⟨sd, hside'⟩

end D5.S3.Combinatorics.Geometry.MiuraCoreRestore
