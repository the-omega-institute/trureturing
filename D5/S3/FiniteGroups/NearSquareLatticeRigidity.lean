/- GID: D5/S3/FiniteGroups/NearSquareLatticeRigidity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NearSquareLatticeRigidity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integer lattice rigidity for a square covering a quotient of near maximal order. -/

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Order.Int.LeastGreatest
import Mathlib.Tactic

/-! Square covering rigidity in the integer plane, measured by the actual finite quotient. -/

/- proof_shape: span_pair_index: bind-only; consumers: index_dvd_det, span_eq_of_det,
   BajnokBeattyCayleyNecessity.sumDiff_index.
   proof_shape: near_square_rigidity: content.
   escape_witness: rigid_vectors (the least positive and negative column displacements
   force their sum to be n and one horizontal displacement to be n).
   admission_basis: escape-witness. Direct frozen dependencies: none.
   The determinant-index identity is supplied by pinned Mathlib; it is not new content. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.NearSquareLatticeRigidity

abbrev Plane := Fin 2 → ℤ

/-- Every lattice coset has a representative in the indicated integer rectangle. -/
def RectangleCovers (L : Submodule ℤ Plane) (w h : ℤ) : Prop :=
  ∀ z : Plane, ∃ x y : ℤ,
    0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < h ∧ z - ![x, y] ∈ L

private def det2 (u v : Plane) : ℤ := u 0 * v 1 - u 1 * v 0

/-- The order of a two-generator lattice quotient is the absolute determinant. -/
theorem span_pair_index (u v : Plane) (hd : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    (Submodule.span ℤ (Set.range ![u, v])).toAddSubgroup.index =
      (u 0 * v 1 - u 1 * v 0).natAbs := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := ![u, v]
  have hA : A.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    exact hd
  have hi : LinearIndependent ℤ ![u, v] := Matrix.linearIndependent_rows_of_det_ne_zero hA
  have he := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin 2))
    (Submodule.span ℤ (Set.range ![u, v])) (Module.Basis.span hi)
  have hvec : ((↑) ∘ Module.Basis.span hi : Fin 2 → Plane) = ![u, v] := by
    funext i
    exact Module.Basis.coe_span_apply hi i
  rw [hvec, Pi.basisFun_det_apply, Matrix.det_fin_two] at he
  change Nat.card (Plane ⧸ Submodule.span ℤ (Set.range ![u, v])) = (det2 u v).natAbs
  exact he.symm

private theorem index_dvd_det (L : Submodule ℤ Plane) {u v : Plane}
    (hu : u ∈ L) (hv : v ∈ L) (hd : det2 u v ≠ 0) :
    (L.toAddSubgroup.index : ℤ) ∣ det2 u v := by
  have hle : Submodule.span ℤ (Set.range ![u, v]) ≤ L := by
    apply Submodule.span_le.mpr
    rintro w ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hv
  have hdvd := AddSubgroup.index_dvd_of_le (show
    (Submodule.span ℤ (Set.range ![u, v])).toAddSubgroup ≤ L.toAddSubgroup from hle)
  rw [span_pair_index u v hd] at hdvd
  exact Int.natCast_dvd.mpr hdvd

private theorem span_eq_of_det (L : Submodule ℤ Plane) {u v : Plane}
    (hu : u ∈ L) (hv : v ∈ L) (hd : det2 u v ≠ 0)
    (hi : (det2 u v).natAbs = L.toAddSubgroup.index) :
    L = Submodule.span ℤ (Set.range ![u, v]) := by
  have hle : Submodule.span ℤ (Set.range ![u, v]) ≤ L := by
    apply Submodule.span_le.mpr
    rintro w ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hv
  have hidx : L.toAddSubgroup.index ≠ 0 := by
    rw [← hi]
    exact Int.natAbs_ne_zero.mpr hd
  letI : L.toAddSubgroup.FiniteIndex := ⟨hidx⟩
  have he := AddSubgroup.eq_of_index_dvd_index
    (H := (Submodule.span ℤ (Set.range ![u, v])).toAddSubgroup)
    (K := L.toAddSubgroup) hle (by
      rw [span_pair_index u v hd]
      change (det2 u v).natAbs ∣ L.toAddSubgroup.index
      rw [hi])
  exact Submodule.toAddSubgroup_injective he.symm

private theorem positive_multiple_eq {d D N : ℤ} (hd : 0 < d) (hD : 0 < D)
    (hdiv : d ∣ D) (hupper : D ≤ N) (hlarge : N < 2 * d) : D = d := by
  obtain ⟨c, rfl⟩ := hdiv
  have hc : 0 < c := by nlinarith
  have hc' : c < 2 := by nlinarith
  have : c = 1 := by omega
  simp [this]

/-- The two adjacent-column intervals must overlap or touch. -/
private theorem adjacent_intervals {n b c : ℤ} (_hn : 0 < n)
    (_hb : 0 < b) (hc : 0 < c) (hc' : c < n)
    (h : ∀ y : ℤ, 0 ≤ y → y < n → y ≤ n - 1 - b ∨ c ≤ y) :
    b + c ≤ n := by
  by_contra hbc
  have hc0 : 0 ≤ c - 1 := by omega
  rcases h (c - 1) hc0 (by omega) with hleft | hright <;> omega

private theorem column_vector {L : Submodule ℤ Plane} {n y : ℤ}
    (hcover : RectangleCovers L n n) (hy : 0 ≤ y) (hyn : y < n) :
    ∃ p q : ℤ, 0 < p ∧ p ≤ n ∧ -(n - 1) ≤ q ∧ q ≤ n - 1 ∧
      0 ≤ y - q ∧ y - q < n ∧ ![p, q] ∈ L := by
  obtain ⟨x, z, hx, hxn, hz, hzn, hm⟩ := hcover ![n, y]
  refine ⟨n - x, y - z, by omega, by omega, by omega, by omega,
    by omega, by omega, ?_⟩
  convert hm using 1 <;> ext i <;> fin_cases i <;> rfl

private theorem rigid_vectors (L : Submodule ℤ Plane) {n δ : ℤ}
    (hn : 2 ≤ n) (hδ : 0 ≤ δ) (hδn : δ < n)
    (hindex : (L.toAddSubgroup.index : ℤ) = n ^ 2 - δ)
    (hcover : RectangleCovers L n n) :
    ∃ a b ε : ℤ, 0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧
      (ε = 1 ∨ ε = -1) ∧ a * b = δ ∧
      ![n, -ε * b] ∈ L ∧ ![-a, ε * n] ∈ L := by
  have hd : 0 < n ^ 2 - δ := by nlinarith
  have hlarge : n ^ 2 < 2 * (n ^ 2 - δ) := by nlinarith
  have hstrip : n * (n - 1) < n ^ 2 - δ := by nlinarith
  have hdiv : ∀ u v : Plane, u ∈ L → v ∈ L → det2 u v ≠ 0 →
      n ^ 2 - δ ∣ det2 u v := by
    intro u v hu hv huv
    simpa [hindex] using index_dvd_det L hu hv huv
  by_cases hh : ∃ p : ℤ, 0 < p ∧ p ≤ n ∧ ![p, 0] ∈ L
  · obtain ⟨p, hp, hpn, hu⟩ := hh
    obtain ⟨x, z, hx, hxn, hz, hzn, hm⟩ := hcover ![0, n]
    have hv : ![-x, n - z] ∈ L := by
      convert hm using 1 <;> ext i <;> fin_cases i <;> simp
    have hpos : 0 < p * (n - z) := mul_pos hp (by omega)
    have he : p * (n - z) = n ^ 2 - δ := by
      apply positive_multiple_eq (N := n ^ 2) hd hpos
      · simpa [det2] using hdiv ![p, 0] ![-x, n-z] hu hv (by simpa [det2] using ne_of_gt hpos)
      · nlinarith [mul_le_mul_of_nonneg_right hpn (show 0 ≤ n by omega),
          mul_nonneg (le_of_lt hp) hz]
      · exact hlarge
    have hp' : p = n := by
      by_contra h
      have : p ≤ n - 1 := by omega
      nlinarith [mul_le_mul_of_nonneg_right this (show 0 ≤ n by omega),
        mul_nonneg (le_of_lt hp) hz]
    have hz' : z = 0 := by
      by_contra h
      have : 1 ≤ z := by omega
      nlinarith
    have hδ' : δ = 0 := by nlinarith
    refine ⟨x, 0, 1, hx, hxn, le_rfl, by omega, Or.inl rfl, by simp [hδ'], ?_, ?_⟩
    · simpa [hp'] using hu
    · simpa [hz'] using hv
  · have hzero : ∀ p : ℤ, 0 < p → p ≤ n → ![p, 0] ∉ L := by
      intro p hp hpn hm
      exact hh ⟨p, hp, hpn, hm⟩
    let P : ℤ → Prop := fun b => 0 < b ∧ b < n ∧
      ∃ p : ℤ, 0 < p ∧ p ≤ n ∧ ![p, -b] ∈ L
    let Q : ℤ → Prop := fun c => 0 < c ∧ c < n ∧
      ∃ r : ℤ, 0 < r ∧ r ≤ n ∧ ![r, c] ∈ L
    have hP : ∃ b, P b := by
      obtain ⟨p, q, hp, hpn, hqlo, hqhi, hyq, hyqn, hm⟩ :=
        column_vector hcover (y := 0) (by omega) (by omega)
      have hq : q < 0 := by
        have : q ≠ 0 := by intro h; subst q; exact hzero p hp hpn hm
        omega
      exact ⟨-q, by dsimp [P]; exact ⟨by omega, by omega, p, hp, hpn, by simpa using hm⟩⟩
    have hQ : ∃ c, Q c := by
      obtain ⟨r, q, hr, hrn, hqlo, hqhi, hyq, hyqn, hm⟩ :=
        column_vector hcover (y := n - 1) (by omega) (by omega)
      have hq : 0 < q := by
        have : q ≠ 0 := by intro h; subst q; exact hzero r hr hrn hm
        omega
      exact ⟨q, hq, by omega, r, hr, hrn, hm⟩
    obtain ⟨b, hb, hbmin⟩ := Int.exists_least_of_bdd
      (P := P) ⟨0, fun z hz => le_of_lt hz.1⟩ hP
    obtain ⟨c, hc, hcmin⟩ := Int.exists_least_of_bdd
      (P := Q) ⟨0, fun z hz => le_of_lt hz.1⟩ hQ
    obtain ⟨hb0, hbn, p, hp0, hpn, hu⟩ := hb
    obtain ⟨hc0, hcn, r, hr0, hrn, hv⟩ := hc
    have hbc : b + c ≤ n := by
      apply adjacent_intervals (by omega) hb0 hc0 hcn
      intro y hy hyn
      obtain ⟨s, q, hs0, hsn, hqlo, hqhi, hyq, hyqn, hm⟩ := column_vector hcover hy hyn
      have hq0 : q ≠ 0 := by intro h; subst q; exact hzero s hs0 hsn hm
      rcases lt_or_gt_of_ne hq0 with hq | hq
      · have hmin := hbmin (-q) (by
          dsimp [P]
          exact ⟨by omega, by omega, s, hs0, hsn, by simpa using hm⟩)
        exact Or.inl (by omega)
      · have hmin := hcmin q ⟨hq, by omega, s, hs0, hsn, hm⟩
        exact Or.inr (by omega)
    have hpos : 0 < p * c + r * b := by positivity
    have hupper : p * c + r * b ≤ n ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hpn (le_of_lt hc0),
        mul_le_mul_of_nonneg_right hrn (le_of_lt hb0),
        mul_le_mul_of_nonneg_left hbc (show 0 ≤ n by omega)]
    have he : p * c + r * b = n ^ 2 - δ := by
      apply positive_multiple_eq hd hpos _ hupper hlarge
      simpa [det2, mul_comm] using hdiv ![p, -b] ![r, c] hu hv
        (by simpa [det2, mul_comm] using ne_of_gt hpos)
    have hbceq : b + c = n := by
      by_contra h
      have : b + c ≤ n - 1 := by omega
      nlinarith [mul_le_mul_of_nonneg_right hpn (le_of_lt hc0),
        mul_le_mul_of_nonneg_right hrn (le_of_lt hb0),
        mul_le_mul_of_nonneg_left this (show 0 ≤ n by omega)]
    have hpr : p = n ∨ r = n := by
      by_contra h
      have hp : p ≤ n - 1 := by omega
      have hr : r ≤ n - 1 := by omega
      nlinarith [mul_le_mul_of_nonneg_right hp (le_of_lt hc0),
        mul_le_mul_of_nonneg_right hr (le_of_lt hb0)]
    rcases hpr with hp | hr
    · refine ⟨n-r, b, 1, by omega, by omega, le_of_lt hb0, hbn,
        Or.inl rfl, ?_, ?_, ?_⟩
      · nlinarith
      · simpa [hp] using hu
      · convert L.sub_mem hv hu using 1 <;> ext i <;> fin_cases i <;> simp [hp] <;> omega
    · refine ⟨n-p, c, -1, by omega, by omega, le_of_lt hc0, hcn,
        Or.inr rfl, ?_, ?_, ?_⟩
      · nlinarith
      · simpa [hr] using hv
      · convert L.sub_mem hu hv using 1 <;> ext i <;> fin_cases i <;> simp [hr] <;> omega

/-- Near maximal square covers force a two-vector lattice basis, with at most one reflection. -/
theorem near_square_rigidity {n δ : ℤ} (L : Submodule ℤ Plane)
    (hn : 2 ≤ n) (hδ : 0 ≤ δ) (hδn : δ < n)
    (hindex : (L.toAddSubgroup.index : ℤ) = n ^ 2 - δ)
    (hcover : RectangleCovers L n n) :
    ∃ a b ε : ℤ, 0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧
      (ε = 1 ∨ ε = -1) ∧ a * b = δ ∧
      L = Submodule.span ℤ (Set.range ![![n, -ε * b], ![-a, ε * n]]) := by
  obtain ⟨a, b, ε, ha, han, hb, hbn, hε, hab, hu, hv⟩ :=
    rigid_vectors L hn hδ hδn hindex hcover
  refine ⟨a, b, ε, ha, han, hb, hbn, hε, hab, span_eq_of_det L hu hv ?_ ?_⟩
  · rcases hε with rfl | rfl <;> simp [det2] <;> nlinarith
  · apply Int.natCast_inj.mp
    rw [Int.natCast_natAbs, hindex]
    have hd : 0 < n ^ 2 - δ := by nlinarith
    rcases hε with rfl | rfl
    · have he : det2 ![n, -(1 : ℤ) * b] ![-a, (1 : ℤ) * n] = n ^ 2 - δ := by
        simp [det2]
        nlinarith
      rw [he, abs_of_pos hd]
    · have he : det2 ![n, -(-1 : ℤ) * b] ![-a, (-1 : ℤ) * n] = -(n ^ 2 - δ) := by
        simp [det2]
        nlinarith
      rw [he, abs_neg, abs_of_pos hd]

end D5.S3.FiniteGroups.NearSquareLatticeRigidity
