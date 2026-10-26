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
    simp only [gdist, b, Fin.val_mk]
    have := v.1.isLt
    omega
  have hbv : gdist v b = ((m - 1 - v.1.val : ℕ) : ℤ) := by
    simp only [gdist, b, Fin.val_mk]
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

end D5.S3.Combinatorics.Geometry.MiuraStripRigidity
