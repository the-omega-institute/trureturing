/- GID: D5/S3/Combinatorics/Geometry/MiuraStripRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraStripRigidity
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: A finite strip with one uphill exit is a vertical extrusion. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraHeightEnvelope

/-! Rigidity from the finite extremum envelope on an actual rectangular strip. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraStripRigidity

open MiuraHeightEnvelope

variable {m n : ℕ}

/-- Multiple maxima on the last row force a vertical extrusion of that row. -/
private theorem maxima_last_row_rigid {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 1 ≤ m) (hmax : ∀ q, IsStrictLocalMax h q → q.1.val + 1 = m)
    (v : Cell m n) :
    h v = h (⟨m - 1, by omega⟩, v.2) - ((m - 1 - v.1.val : ℕ) : ℤ) := by
  obtain ⟨⟨q, hq, heq⟩, _⟩ := envelope_max hh v
  have hlast := hmax q hq
  let b : Cell m n := (⟨m - 1, by omega⟩, v.2)
  have hqb := envelope_le hh b q
  have hvb := envelope_le hh v b
  have hqv : gdist q v = ((m - 1 - v.1.val : ℕ) : ℤ) + gdist b q := by
    simp only [gdist, b]
    have := v.1.isLt
    omega
  have hbv : gdist v b = ((m - 1 - v.1.val : ℕ) : ℤ) := by
    simp only [gdist, b]
    have := v.1.isLt
    omega
  change h v = h b - _
  omega

/-- The row offset embeds a full-width strip into its actual ambient grid. -/
def stripMap (p r : ℕ) (hpr : p + r ≤ m) (v : Cell r n) : Cell m n :=
  (⟨p + v.1.val, by have := v.1.isLt; omega⟩, v.2)

/-- A strip with no ambient maximum before its last row, whose outward edges
above it are downhill, is rigid. The last row is the exit row. Physical top
boundaries satisfy the outward-edge hypothesis vacuously. -/
theorem one_exit_strip_rigid {h : Cell m n → ℤ} (hh : IsHeight h)
    (p r : ℕ) (hr : 1 ≤ r) (hpr : p + r ≤ m)
    (hno : ∀ v : Cell r n, v.1.val + 1 < r →
      ¬ IsStrictLocalMax h (stripMap p r hpr v))
    (htop : ∀ (v : Cell r n) (u : Cell m n),
      adj (stripMap p r hpr v) u → u.1.val < p →
      h u = h (stripMap p r hpr v) - 1)
    (v : Cell r n) :
    h (stripMap p r hpr v) =
      h (stripMap p r hpr (⟨r - 1, by omega⟩, v.2)) -
        ((r - 1 - v.1.val : ℕ) : ℤ) := by
  let f : Cell r n → ℤ := fun w => h (stripMap p r hpr w)
  have hd (a b : Cell r n) :
      gdist (stripMap p r hpr a) (stripMap p r hpr b) = gdist a b := by
    simp only [gdist, stripMap, Fin.val_mk]
    omega
  have hf : IsHeight f := by
    intro a b hab
    exact hh _ _ (by simpa only [adj, hd] using hab)
  apply maxima_last_row_rigid hf hr ?_ v
  intro q hq
  by_contra hlast
  have hqint : q.1.val + 1 < r := by have := q.1.isLt; omega
  apply hno q hqint
  intro u hu
  by_cases hlow : u.1.val < p
  · exact htop q u hu hlow
  · have hurow : u.1.val < p + r := by
      have hqu := hu
      simp only [adj, gdist, stripMap, Fin.val_mk] at hqu
      have := q.1.isLt
      omega
    let w : Cell r n := (⟨u.1.val - p, by omega⟩, u.2)
    have hw : stripMap p r hpr w = u := by
      apply Prod.ext
      · apply Fin.ext
        simp only [stripMap, w, Fin.val_mk]
        omega
      · rfl
    have hqw : adj q w := by
      have : adj (stripMap p r hpr q) (stripMap p r hpr w) := hw.symm ▸ hu
      simpa only [adj, hd] using this
    have heq := hq w hqw
    change h (stripMap p r hpr w) = h (stripMap p r hpr q) - 1 at heq
    simpa only [hw] using heq

/-- An occupied internal strip with downhill outward top edges contains an
ambient maximum before its exit row. This is the maximum half of the neutral
slab extremum-forcing argument. -/
theorem occupied_internal_strip_has_maximum {h : Cell m n → ℤ} (hh : IsHeight h)
    (p r : ℕ) (hp : 0 < p) (hr : 1 ≤ r) (hpr : p + r ≤ m)
    (htop : ∀ (v : Cell r n) (u : Cell m n),
      adj (stripMap p r hpr v) u → u.1.val < p →
      h u = h (stripMap p r hpr v) - 1)
    (hoccupied : ∃ v : Cell r n, v.1.val + 1 < r ∧
      (IsStrictLocalMax h (stripMap p r hpr v) ∨
       IsStrictLocalMin h (stripMap p r hpr v))) :
    ∃ v : Cell r n, v.1.val + 1 < r ∧
      IsStrictLocalMax h (stripMap p r hpr v) := by
  classical
  by_contra hnone
  have hno (w : Cell r n) (hw : w.1.val + 1 < r) :
      ¬ IsStrictLocalMax h (stripMap p r hpr w) :=
    fun hmax => hnone ⟨w, hw, hmax⟩
  obtain ⟨w, hw, hmax | hmin⟩ := hoccupied
  · exact hno w hw hmax
  · by_cases hw0 : w.1.val = 0
    · let u : Cell m n := (⟨p - 1, by omega⟩, w.2)
      have hadj : adj (stripMap p r hpr w) u := by
        simp only [adj, gdist, stripMap, u, Fin.val_mk]
        omega
      have hup := htop w u hadj (by simp only [u]; omega)
      have hdown := hmin u hadj
      omega
    · let u : Cell r n := (⟨w.1.val - 1, by have := w.1.isLt; omega⟩, w.2)
      have hadj : adj (stripMap p r hpr w) (stripMap p r hpr u) := by
        simp only [adj, gdist, stripMap, u, Fin.val_mk]
        omega
      have hminup := hmin _ hadj
      have hwrig := one_exit_strip_rigid hh p r hr hpr hno htop w
      have hurig := one_exit_strip_rigid hh p r hr hpr hno htop u
      simp only [u] at hminup hurig
      have := w.1.isLt
      omega

/- The following adjacency decomposition is adapted verbatim from Chakshu Gupta,
SequelEdContractExtremum.lean, blob bfd29f90788f3c03a8467d2b850bea239a4d8213.
CC BY 4.0, with attribution and full license in docs/reports/miura-suppliers/.
It is used in the slope-reversal argument below. Its transplant has the same
pinned-mathlib retirement criterion as MiuraHeightEnvelope.
-/
lemma adj_row_or_col {N : ℕ} {p q : Cell m N} (h : adj p q) :
    (p.1 = q.1 ∧ ((p.2.val : ℤ) - q.2.val).natAbs = 1) ∨
    (p.2 = q.2 ∧ ((p.1.val : ℤ) - q.1.val).natAbs = 1) := by
  unfold adj gdist at h
  set a := ((p.1.val : ℤ) - q.1.val).natAbs with ha
  set b := ((p.2.val : ℤ) - q.2.val).natAbs with hb
  have hab : (a : ℤ) + b = 1 := by exact_mod_cast h
  by_cases h1 : a = 0
  · left
    have hbv : b = 1 := by omega
    refine ⟨?_, hbv⟩
    apply Fin.ext
    have hz : ((p.1.val : ℤ) - q.1.val) = 0 := by
      have := Int.natAbs_eq_zero.mp h1; omega
    omega
  · right
    have hav : a = 1 := by omega
    have hbv : b = 0 := by omega
    refine ⟨?_, hav⟩
    apply Fin.ext
    have hz : ((p.2.val : ℤ) - q.2.val) = 0 := by
      have := Int.natAbs_eq_zero.mp hbv; omega
    omega


/-- A first downward reversal after an upward cut exposes an ambient maximum.
The reversal column is selected from the actual next row, including endpoints. -/
theorem first_reversal_has_maximum {h : Cell m n → ℤ} (hh : IsHeight h)
    (i : Fin m) (hi0 : 0 < i.val) (hi1 : i.val + 1 < m)
    (hprev : ∀ j : Fin n,
      h (i, j) = h (⟨i.val - 1, by omega⟩, j) + 1)
    (hrev : ∃ j : Fin n, h (⟨i.val + 1, hi1⟩, j) = h (i, j) - 1) :
    ∃ j : Fin n, IsStrictLocalMax h (i, j) ∧
      h (⟨i.val + 1, hi1⟩, j) = h (i, j) - 1 := by
  classical
  let D : Finset (Fin n) := Finset.univ.filter
    (fun j => h (⟨i.val + 1, hi1⟩, j) = h (i, j) - 1)
  have hD : D.Nonempty := by
    obtain ⟨j, hj⟩ := hrev
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image D (fun j => h (i, j)) hD
  have hjdown := (Finset.mem_filter.mp hj).2
  have hhorizontal (k : Fin n) (hadj : adj ((i, j) : Cell m n) (i, k)) :
      h (i, k) = h (i, j) - 1 := by
    have hupper := hh _ _ hadj
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hupper
    by_cases hk : k ∈ D
    · have hle := hjmax k hk
      omega
    · have hknot : h (⟨i.val + 1, hi1⟩, k) ≠ h (i, k) - 1 := by
        simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      have hvertical := hh (i, k) (⟨i.val + 1, hi1⟩, k) (by
        simp only [adj, gdist]; omega)
      have hbottom := hh (⟨i.val + 1, hi1⟩, j) (⟨i.val + 1, hi1⟩, k) (by
        simp only [adj, gdist] at hadj ⊢
        omega)
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hvertical hbottom
      omega
  refine ⟨j, ?_, hjdown⟩
  intro u hu
  obtain ⟨ur, uc⟩ := u
  rcases adj_row_or_col hu with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
  · change i = ur at hrow
    subst ur
    exact hhorizontal uc hu
  · change j = uc at hcol
    subst uc
    have hcases : ur.val = i.val - 1 ∨ ur.val = i.val + 1 := by
      change ((i.val : ℤ) - ur.val).natAbs = 1 at hrow
      omega
    rcases hcases with hup | hdown
    · have heq : ur = (⟨i.val - 1, by omega⟩ : Fin m) := Fin.ext hup
      rw [heq]
      have := hprev j
      omega
    · have heq : ur = (⟨i.val + 1, hi1⟩ : Fin m) := Fin.ext hdown
      rw [heq]
      exact hjdown

end D5.S3.Combinatorics.Geometry.MiuraStripRigidity
