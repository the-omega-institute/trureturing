/- GID: D5/S3/FiniteGroups/BajnokBeattyShortReturnBand
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyShortReturnBand
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact signed-word return defect throughout the first even return band. -/

import D5.S3.FiniteGroups.PlaneWordEndpointCount

/-!
proof_shape: short_return_band: content.
admission_basis: escape-witness.
escape_witness: an explicit decomposition of the actual return fibers into
the common zero endpoint fiber and the two horizontal endpoint fibers, whose
cardinalities are obtained from the consumed two-subset word bijection.
The rank-one short-kernel supplier is reused from the existing growth proof.
No count or kernel classification is supplied as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.BajnokBeattyShortReturnBand

open NearSquareLatticeRigidity BajnokBeattyAsymmetricGrowth
open BajnokBeattyFirstReturnDefect

theorem short_span (p m a b : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (hmo : Odd m) (hao : Odd a) (hbo : Odd b)
    (ha : 0 < a) (ham : a < m) (hb : 0 < b) (hbm : b < m) :
    let v1 : Plane := ![p*(m-a)/2, p*(m+a)/2]
    let v2 : Plane := ![p*(m-b)/2, -(p*(m+b)/2)]
    let K := Submodule.span ℤ (Set.range ![v1, v2])
    ∀ z : Plane, z ∈ K → |z 0|+|z 1| < p*m →
      ∃ k : ℤ, z = k • (v1+v2) := by
  have hp : 0 < p := by omega
  obtain ⟨hs, hv1, hv2, hh, hmem, hne, hshort⟩ :=
    asymmetric_rank_one_actual_data p m a b hp hpo hmo hao hbo ha ham hb hbm
  dsimp only
  intro z hz hn
  exact hshort ((p*m-1)/2) le_rfl z hz (by omega)

private theorem short_kernels (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6*t-1
    let n : ℤ := p*(m-3)
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    (∀ z : Plane, z ∈ K19 → |z 0|+|z 1| < p*(m-1) → z = 0) ∧
    (∀ z : Plane, z ∈ K33 → |z 0|+|z 1| < p*(m-1) →
      z = 0 ∨ z = ![n,0] ∨ z = ![-n,0]) ∧
    (![n,0] : Plane) ∈ K33 ∧ (![-n,0] : Plane) ∈ K33 := by
  let m : ℤ := 6*t-1
  let n : ℤ := p*(m-3)
  let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
  let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
  let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
  let K19 := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 := Submodule.span ℤ (Set.range ![v133, v233])
  change (∀ z : Plane, z ∈ K19 → |z 0|+|z 1| < p*(m-1) → z = 0) ∧
    (∀ z : Plane, z ∈ K33 → |z 0|+|z 1| < p*(m-1) →
      z = 0 ∨ z = ![n,0] ∨ z = ![-n,0]) ∧
    (![n,0] : Plane) ∈ K33 ∧ (![-n,0] : Plane) ∈ K33
  have hp : 0 < p := by omega
  have hm11 : 11 ≤ m := by dsimp [m]; omega
  have hmo : Odd m := by
    exact ⟨3*t-1, by dsimp [m]; ring⟩
  have h119 : 2*(p*(m-1)/2) = p*(m-1) := by
    have hd := ((hmo.sub_odd odd_one).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h219 : 2*(p*(m+1)/2) = p*(m+1) := by
    have hd := ((hmo.add_odd odd_one).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h319 : 2*(p*(m-9)/2) = p*(m-9) := by
    have hd := ((hmo.sub_odd (by decide : Odd (9:ℤ))).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h419 : 2*(p*(m+9)/2) = p*(m+9) := by
    have hd := ((hmo.add_odd (by decide : Odd (9:ℤ))).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have h133 : 2*(p*(m-3)/2) = p*(m-3) := by
    have hd := ((hmo.sub_odd (by decide : Odd (3:ℤ))).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have hsum19 : v119+v219 = (![p*(m-5),-4*p] : Plane) := by
    ext i
    fin_cases i <;> dsimp [v119,v219] <;>
      nlinarith only [h119,h219,h319,h419]
  have hsum33 : v133+v233 = (![n,0] : Plane) := by
    ext i
    fin_cases i <;> dsimp [v133,v233,n] <;> omega
  have hn : 0 < n := by dsimp [n]; exact mul_pos hp (by omega)
  have hmin19 : 0 < p*(m-1) := mul_pos hp (by omega)
  have htwice : p*(m-1) < 2*n := by dsimp [n]; nlinarith
  have hposmem : (![n,0] : Plane) ∈ K33 := by
    rw [← hsum33]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  refine ⟨?_, ?_, hposmem, ?_⟩
  · intro z hz hnorm
    obtain ⟨k,hk⟩ := short_span p m 1 9 hp3 hpo hmo odd_one
      (by decide) (by norm_num) (by omega) (by norm_num) (by omega) z hz (by nlinarith)
    rw [hsum19] at hk
    have hzNorm : |z 0|+|z 1| = |k| * (p*(m-1)) := by
      rw [hk]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, abs_mul]
      norm_num [abs_of_pos hp, abs_of_nonneg (show 0 ≤ m-5 by omega)] <;> ring
    have hk0 : k = 0 := by
      by_contra hk0
      have hka := Int.one_le_abs hk0
      have hbound := mul_le_mul_of_nonneg_right hka (le_of_lt hmin19)
      nlinarith [hzNorm]
    simpa [hk0] using hk
  · intro z hz hnorm
    obtain ⟨k,hk⟩ := short_span p m 3 3 hp3 hpo hmo (by decide)
      (by decide) (by norm_num) (by omega) (by norm_num) (by omega) z hz (by nlinarith)
    rw [hsum33] at hk
    have hzNorm : |z 0|+|z 1| = |k| * n := by
      rw [hk]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, abs_mul, abs_of_pos hn, mul_zero, abs_zero, add_zero]
    have hka : |k| < 2 := by nlinarith
    have hkcases : k=0 ∨ k=1 ∨ k= -1 := by
      have hkb := abs_lt.mp hka
      omega
    rcases hkcases with rfl | rfl | rfl
    · left; simpa using hk
    · right; left; simpa using hk
    · right; right
      rw [hk]
      ext i
      fin_cases i <;> simp
  · have hneg := K33.neg_mem hposmem
    simpa using hneg

private theorem three_fiber_card (l : ℕ) (n : ℤ) (hn : 0 < n) :
    Nat.card {w : Fin l → Fin 4 //
      endpoint w = 0 ∨ endpoint w = ![n,0] ∨ endpoint w = ![-n,0]} =
    Nat.card {w : Fin l → Fin 4 // endpoint w = 0} +
      (Nat.card {w : Fin l → Fin 4 // endpoint w = ![n,0]} +
        Nat.card {w : Fin l → Fin 4 // endpoint w = ![-n,0]}) := by
  classical
  have hzero : Disjoint (fun w : Fin l → Fin 4 => endpoint w = 0)
      (fun w => endpoint w = ![n,0] ∨ endpoint w = ![-n,0]) := by
    apply Set.disjoint_left.mpr
    intro w hw hpm
    rcases hpm with hpm | hpm
    · have h := congrFun (hw.symm.trans hpm) 0
      simp only [Pi.zero_apply, Matrix.cons_val_zero] at h
      omega
    · have h := congrFun (hw.symm.trans hpm) 0
      simp only [Pi.zero_apply, Matrix.cons_val_zero] at h
      omega
  have hpm : Disjoint (fun w : Fin l → Fin 4 => endpoint w = ![n,0])
      (fun w => endpoint w = ![-n,0]) := by
    apply Set.disjoint_left.mpr
    intro w hw hneg
    have h := congrFun (hw.symm.trans hneg) 0
    simp only [Matrix.cons_val_zero] at h
    omega
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_or_disjoint _ _ hzero,
    Fintype.card_subtype_or_disjoint _ _ hpm]

/-- Every even word length after the first wrap and before the next lattice
relation has an exact two-binomial-square excess of returns in the `(3,3)`
quotient.  The two maps are the actual quotient maps of the displayed
lattices, and no additional kernel or counting assumptions occur. -/
theorem short_return_band (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t)
    (r : ℕ) (hr : (r : ℤ) < p) :
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let n : ℕ := (p*(m-3)).toNat
    W F33 (n+2*r) = W F19 (n+2*r) + 2 * (Nat.choose (n+2*r) r)^2 := by
  classical
  let m : ℤ := 6*t-1
  let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
  let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
  let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
  let K19 := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 := Submodule.span ℤ (Set.range ![v133, v233])
  let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
  let n : ℕ := (p*(m-3)).toNat
  let l : ℕ := n+2*r
  change W F33 l = W F19 l + 2*(Nat.choose l r)^2
  have hp : 0 < p := by omega
  have hm11 : 11 ≤ m := by dsimp [m]; omega
  have hnZ : (n : ℤ) = p*(m-3) := Int.toNat_of_nonneg (by
    exact le_of_lt (mul_pos hp (by omega)))
  have hn : (0:ℤ) < n := by rw [hnZ]; exact mul_pos hp (by omega)
  have hl : (l : ℤ) < p*(m-1) := by dsimp [l]; nlinarith
  obtain ⟨h19,h33,hpos,hneg⟩ := short_kernels p t hp3 hpo ht
  have hmem19 (w : Fin l → Fin 4) : F19 (endpoint w) = 0 ↔ endpoint w = 0 := by
    constructor
    · intro hw
      apply h19 (endpoint w) ((Submodule.Quotient.mk_eq_zero K19).mp hw)
      exact (endpoint_lee_bound w).trans_lt hl
    · intro hw
      rw [hw, map_zero]
  have hmem33 (w : Fin l → Fin 4) : F33 (endpoint w) = 0 ↔
      endpoint w = 0 ∨ endpoint w = ![(n : ℤ),0] ∨ endpoint w = ![-(n : ℤ),0] := by
    constructor
    · intro hw
      have hresult : endpoint w = 0 ∨ endpoint w = ![p*(m-3),0] ∨
          endpoint w = ![-(p*(m-3)),0] := h33 (endpoint w)
        ((Submodule.Quotient.mk_eq_zero K33).mp hw)
        ((endpoint_lee_bound w).trans_lt hl)
      simpa only [← hnZ] using hresult
    · intro hw
      apply (Submodule.Quotient.mk_eq_zero K33).mpr
      rcases hw with hw | hw | hw
      · rw [hw]; exact K33.zero_mem
      · rw [hw,hnZ]; exact hpos
      · rw [hw,hnZ]; exact hneg
  have hc19 : W F19 l = Nat.card {w : Fin l → Fin 4 // endpoint w = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight hmem19)
  have hc33 : W F33 l = Nat.card {w : Fin l → Fin 4 //
      endpoint w = 0 ∨ endpoint w = ![(n : ℤ),0] ∨
        endpoint w = ![-(n : ℤ),0]} :=
    Nat.card_congr (Equiv.subtypeEquivRight hmem33)
  have hcpos : Nat.card {w : Fin l → Fin 4 // endpoint w = ![(n : ℤ),0]} =
      (Nat.choose l r)^2 := by
    rw [PlaneWordEndpointCount.endpoint_card l r r (n : ℤ) 0
      (by dsimp [l]; ring) (by dsimp [l]; ring)]
    ring
  have hcneg : Nat.card {w : Fin l → Fin 4 // endpoint w = ![-(n : ℤ),0]} =
      (Nat.choose l r)^2 := by
    rw [PlaneWordEndpointCount.endpoint_card l (n+r) (n+r) (-(n : ℤ)) 0
      (by dsimp [l]; ring) (by dsimp [l]; ring)]
    have hchoose : Nat.choose l (n+r) = Nat.choose l r := by
      have h := Nat.choose_symm (show n+r ≤ l by dsimp [l]; omega)
      simpa only [show l-(n+r)=r by dsimp [l]; omega] using h.symm
    rw [hchoose]
    ring
  rw [hc33, three_fiber_card l (n : ℤ) hn, hcpos, hcneg, hc19]
  omega

end D5.S3.FiniteGroups.BajnokBeattyShortReturnBand
