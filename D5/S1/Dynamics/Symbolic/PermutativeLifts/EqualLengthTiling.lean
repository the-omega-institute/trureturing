/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal-length tiling phases, recognizability, and periodic common columns. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.MarkedTiling

/-! # Equal-length marked tiling phases and recognizability

Physical offsets give two-sided cyclic phases. Visible words and boundaries
identify marked tilings, and shared columns give periodic coordinates. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

private theorem tile_state_ext (W : Bool → List Bool) {s t : TileState W}
    (ha : s.1 = t.1) (ho : s.2.val = t.2.val) : s = t := by
  rcases s with ⟨a, p⟩
  rcases t with ⟨b, q⟩
  dsimp at ha ho
  subst b
  exact congrArg (Sigma.mk a) (Fin.ext ho)

private theorem tile_next_offset_eq_iff (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) {s t u v : TileState W}
    (hst : TileNext W s t) (huv : TileNext W u v) :
    s.2.val = u.2.val ↔ t.2.val = v.2.val := by
  have hs : s.2.val < L := by simpa only [hW] using s.2.isLt
  have ht : t.2.val < L := by simpa only [hW] using t.2.isLt
  have hu : u.2.val < L := by simpa only [hW] using u.2.isLt
  have hv : v.2.val < L := by simpa only [hW] using v.2.isLt
  rcases hst with hst | hst <;> rcases huv with huv | huv <;>
    simp only [hW] at * <;> constructor <;> intro h <;> omega

/-- The phase advances by physical translation, on both sides of the origin. -/
theorem tiled_offset_phase (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) (hL : 0 < L)
    (x : MarkedTiling W) (i : ℤ) :
    ((x.1 i).2.val : ℤ) = (i + ((x.1 0).2.val : ℤ)) % (L : ℤ) := by
  have hf : 0 < (W false).length := by rw [hW]; exact hL
  let y : ℤ → TileState W := fun j =>
    periodicTile W false hf (j + ((x.1 0).2.val : ℤ))
  have hy : Tiled W y := by
    intro j
    simpa only [y, add_assoc, add_left_comm, add_comm] using
      periodicTile_tiled W false hf (j + ((x.1 0).2.val : ℤ))
  have heq (j : ℤ) : (x.1 j).2.val = (y j).2.val := by
    induction j using Int.induction_on with
    | zero =>
      have hxlt : ((x.1 0).2.val : ℤ) < (L : ℤ) := by
        have hh : (x.1 0).2.val < L := by
          simpa only [hW] using (x.1 0).2.isLt
        omega
      simp only [y, periodicTile, hW, zero_add]
      rw [Int.emod_eq_of_lt (by omega) hxlt]
      simp
    | succ n ih =>
      exact (tile_next_offset_eq_iff W L hW (x.2 (n : ℤ)) (hy (n : ℤ))).1 ih
    | pred n ih =>
      apply (tile_next_offset_eq_iff W L hW (x.2 (-(n : ℤ) - 1))
        (hy (-(n : ℤ) - 1))).2
      have hi : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
      exact Eq.mpr (congrArg
        (fun z : ℤ => (x.1 z).2.val = (y z).2.val) hi) ih
  have hm0 := Int.emod_nonneg (i + ((x.1 0).2.val : ℤ))
    (show (L : ℤ) ≠ 0 by omega)
  have hm := heq i
  dsimp [y, periodicTile] at hm
  have hm' : (x.1 i).2.val = ((i + ((x.1 0).2.val : ℤ)) % (L : ℤ)).toNat := by
    simpa only [hW] using hm
  omega

/-- Every integer multiple of the common length preserves all offsets. -/
theorem tiled_offset_periodic (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) (hL : 0 < L)
    (x : MarkedTiling W) (i k : ℤ) :
    (x.1 (i + k * (L : ℤ))).2.val = (x.1 i).2.val := by
  have h₁ := tiled_offset_phase W L hW hL x (i + k * (L : ℤ))
  have h₂ := tiled_offset_phase W L hW hL x i
  rw [show i + k * (L : ℤ) + ((x.1 0).2.val : ℤ) =
    (i + ((x.1 0).2.val : ℤ)) + k * (L : ℤ) by omega,
    Int.add_mul_emod_self_right] at h₁
  omega

/-- With a boundary at zero, the phase is the ordinary nonnegative remainder. -/
theorem tiled_offset_aligned (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) (hL : 0 < L)
    (x : MarkedTiling W) (hzero : (x.1 0).2.val = 0) (i : ℤ) :
    ((x.1 i).2.val : ℤ) = i % (L : ℤ) := by
  simpa [hzero] using tiled_offset_phase W L hW hL x i

private theorem read_tile_eq_get (W : Bool → List Bool) (s : TileState W)
    (a : Bool) (j : ℕ) (hj : j < (W a).length)
    (ha : s.1 = a) (ho : s.2.val = j) :
    readTile W s = (W a).get ⟨j, hj⟩ := by
  have heq : s = ⟨a, ⟨j, hj⟩⟩ := tile_state_ext W ha ho
  rw [heq]
  rfl

/-- Equal readout and equal boundaries identify tiles whose words, rather than
whose lengths, are distinct. The common length may be the same for both types. -/
theorem equal_length_tiling_eq_of_read_boundaries (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) (hinj : Function.Injective W)
    (x y : MarkedTiling W) (hr : readTiling W x = readTiling W y)
    (hb : ∀ i, (x.1 i).2.val = 0 ↔ (y.1 i).2.val = 0) : x = y := by
  apply Subtype.ext
  funext i
  have hoff := tiled_offset_eq_of_boundaries W x.2 y.2 hb i
  let b : ℤ := i - ((x.1 i).2.val : ℤ)
  have hxb := tiled_boundary_behind W x.2 i
  have hyb := tiled_boundary_behind W y.2 i
  have hxyb : i - ((y.1 i).2.val : ℤ) = b := by dsimp [b]; omega
  rw [hxyb] at hyb
  change (x.1 b).1 = (x.1 i).1 ∧ (x.1 b).2.val = 0 at hxb
  have hwords : W (x.1 b).1 = W (y.1 b).1 := by
    apply List.ext_get (by rw [hW, hW])
    intro j hjx hjy
    have hfx := tiled_forwards W x.2 b j (by omega)
    have hfy := tiled_forwards W y.2 b j (by omega)
    have hxread := readTile_of_coordinates W (x.1 (b + (j : ℤ))) (x.1 b).1 j hjx
      hfx.1 (by omega)
    have hyread := readTile_of_coordinates W (y.1 (b + (j : ℤ))) (y.1 b).1 j hjy
      hfy.1 (by omega)
    simpa only [List.get_eq_getElem] using
      hxread.symm.trans ((congrFun hr (b + (j : ℤ))).trans hyread)
  exact tile_state_ext W (hxb.1.symm.trans ((hinj hwords).trans hyb.1)) hoff

/-- A column shared by the two words has a type-independent readout. -/
theorem tiled_read_common_column (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) (hL : 0 < L)
    (x : MarkedTiling W) (hzero : (x.1 0).2.val = 0)
    (j : ℕ) (hj : j < L)
    (hc : (W false).get ⟨j, by rw [hW]; exact hj⟩ =
      (W true).get ⟨j, by rw [hW]; exact hj⟩)
    (i : ℤ) (hi : i % (L : ℤ) = (j : ℤ)) :
    readTiling W x i = (W false).get ⟨j, by rw [hW]; exact hj⟩ := by
  have hoff : (x.1 i).2.val = j := by
    have := tiled_offset_aligned W L hW hL x hzero i
    omega
  have hr := readTile_of_coordinates W (x.1 i) (x.1 i).1 j (by rw [hW]; exact hj) rfl hoff
  change readTile W (x.1 i) = _
  simp only [List.get_eq_getElem]
  rw [hr]
  cases (x.1 i).1
  · rfl
  · exact (by simpa only [List.get_eq_getElem] using hc.symm)

/-- Every point in a shared phase column is periodic with the full tile length. -/
theorem tiled_common_column_periodic (W : Bool → List Bool) (L : ℕ)
    (hW : ∀ a, (W a).length = L) (hL : 0 < L)
    (x : MarkedTiling W) (i : ℤ)
    (hc : (W false).get ⟨(x.1 i).2.val, by
        simpa only [hW] using (x.1 i).2.isLt⟩ =
      (W true).get ⟨(x.1 i).2.val, by
        simpa only [hW] using (x.1 i).2.isLt⟩)
    (k : ℤ) : readTiling W x (i + k * (L : ℤ)) = readTiling W x i := by
  have hlt : (x.1 i).2.val < L := by simpa only [hW] using (x.1 i).2.isLt
  have h₁ := readTile_of_coordinates W (x.1 (i + k * (L : ℤ)))
    (x.1 (i + k * (L : ℤ))).1 (x.1 i).2.val (by simpa only [hW] using hlt) rfl
    (tiled_offset_periodic W L hW hL x i k)
  have h₂ := readTile_of_coordinates W (x.1 i) (x.1 i).1 (x.1 i).2.val
    (by simpa only [hW] using hlt) rfl rfl
  have hcommon (a b : Bool) :
      (W a).get ⟨(x.1 i).2.val, by simpa only [hW] using hlt⟩ =
        (W b).get ⟨(x.1 i).2.val, by simpa only [hW] using hlt⟩ := by
    cases a <;> cases b
    · rfl
    · exact hc
    · exact (by simpa only [List.get_eq_getElem] using hc.symm)
    · rfl
  simp only [List.get_eq_getElem] at hcommon
  exact h₁.trans ((hcommon _ _).trans h₂.symm)

end D5.S1.Dynamics.Symbolic.PermutativeLifts
