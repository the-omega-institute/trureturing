/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapReturnCounts
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapReturnCounts
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact actual quotient return counts at the first odd wrap. -/

import D5.S3.FiniteGroups.PlaneWordEndpointCount
import D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth

/-!
proof_shape: actual_odd_wrap_counts: content.
admission_basis: escape-witness.
escape_witness: the complete closed-boundary lattice coefficient classification,
combined with endpoint parity, identifies precisely four disjoint generator
fibers at the first odd wrap. Their cardinalities consume the existing
PlaneWordEndpointCount.endpoint_card equivalence. Every private helper lies
on the actual counting proof path; no kernel classification or counting
formula is supplied as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts

open NearSquareLatticeRigidity BajnokBeattyCayleyNecessity
open BajnokBeattyAsymmetricGrowth BajnokBeattyFirstReturnDefect
open scoped Classical

private theorem boundary_coefficients {m a b : ℤ}
    (ha : 0 < a) (ham : a < m) (hb : 0 < b) (hbm : b < m)
    (q1 q2 : ℤ) (hne : q1 ≠ q2)
    (hbound : max |m*q1-b*q2| |(-a)*q1+m*q2| ≤ m) :
    (q1 = 1 ∧ q2 = 0) ∨ (q1 = -1 ∧ q2 = 0) ∨
      (q1 = 0 ∧ q2 = 1) ∨ (q1 = 0 ∧ q2 = -1) := by
  have hm : 0 < m := by omega
  have hnonneg : ∀ u v : ℤ, 0 ≤ u → 0 ≤ v → u ≠ v →
      max |m*u-b*v| |(-a)*u+m*v| ≤ m →
      (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 1) := by
    intro u v hu hv huv hmax
    have hx := (abs_le.mp ((le_max_left _ _).trans hmax)).2
    have hy := (abs_le.mp ((le_max_right _ _).trans hmax)).2
    rcases lt_or_gt_of_ne huv with huv | huv
    · have hstep : 1 ≤ v-u := by omega
      have hmain := mul_le_mul_of_nonneg_left hstep (le_of_lt hm)
      have htail := mul_le_mul_of_nonneg_right
        (show (1 : ℤ) ≤ m-a by omega) hu
      have hu0 : u = 0 := by nlinarith only [hy, hmain, htail, hu]
      have hvle : v ≤ 1 := (mul_le_mul_iff_right₀ hm).mp (by
        simpa only [hu0, mul_zero, zero_add, mul_one] using hy)
      exact Or.inr ⟨hu0, by omega⟩
    · have hstep : 1 ≤ u-v := by omega
      have hmain := mul_le_mul_of_nonneg_left hstep (le_of_lt hm)
      have htail := mul_le_mul_of_nonneg_right
        (show (1 : ℤ) ≤ m-b by omega) hv
      have hv0 : v = 0 := by nlinarith only [hx, hmain, htail, hv]
      have hule : u ≤ 1 := (mul_le_mul_iff_right₀ hm).mp (by
        simpa only [hv0, mul_zero, sub_zero, mul_one] using hx)
      exact Or.inl ⟨by omega, hv0⟩
  have hmixed : ∀ u v : ℤ, 0 ≤ u → v < 0 →
      max |m*u-b*v| |(-a)*u+m*v| ≤ m → u = 0 ∧ v = -1 := by
    intro u v hu hv hmax
    have hx := (abs_le.mp ((le_max_left _ _).trans hmax)).2
    have hy := (abs_le.mp ((le_max_right _ _).trans hmax)).1
    have hu0 : u = 0 := by
      by_contra hne0
      have hu1 : 1 ≤ u := by omega
      have hmain := mul_le_mul_of_nonneg_left hu1 (le_of_lt hm)
      have htail := mul_neg_of_pos_of_neg hb hv
      nlinarith only [hx, hmain, htail]
    have hvge : -1 ≤ v := (mul_le_mul_iff_right₀ hm).mp (by
      simpa only [hu0, mul_zero, zero_add, mul_neg_one] using hy)
    exact ⟨hu0, by omega⟩
  have hneg : ∀ u v : ℤ,
      max |m*(-u)-b*(-v)| |(-a)*(-u)+m*(-v)| =
        max |m*u-b*v| |(-a)*u+m*v| := by
    intro u v
    have hx : m*(-u)-b*(-v) = -(m*u-b*v) := by ring
    have hy : (-a)*(-u)+m*(-v) = -((-a)*u+m*v) := by ring
    rw [hx, hy, abs_neg, abs_neg]
  by_cases hq1 : 0 ≤ q1
  · by_cases hq2 : 0 ≤ q2
    · rcases hnonneg q1 q2 hq1 hq2 hne hbound with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (hmixed q1 q2 hq1 (by omega) hbound)))
  · by_cases hq2 : q2 ≤ 0
    · have hbn : max |m*(-q1)-b*(-q2)| |(-a)*(-q1)+m*(-q2)| ≤ m := by
        rw [hneg]
        exact hbound
      rcases hnonneg (-q1) (-q2) (by omega) (by omega) (by omega) hbn with h | h
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · have hbn : max |m*(-q1)-b*(-q2)| |(-a)*(-q1)+m*(-q2)| ≤ m := by
        rw [hneg]
        exact hbound
      obtain ⟨hu, _⟩ := hmixed (-q1) (-q2) (by omega) (by omega) hbn
      omega

private theorem odd_boundary_return_iff (p m a b : ℤ) (v1 v2 : Plane)
    (hp : 0 < p) (hpo : Odd p) (hmo : Odd m) (hbo : Odd b)
    (ha : 0 < a) (ham : a < m) (hb : 0 < b) (hbm : b < m)
    (hv1 : sumDiff v1 = ![p*m, -p*a])
    (hv2 : sumDiff v2 = ![-p*b, p*m]) :
    let K := Submodule.span ℤ (Set.range ![v1, v2])
    let L : ℕ := (p*m).toNat
    ∀ w : Fin L → Fin 4, K.mkQ.toAddMonoidHom (endpoint w) = 0 ↔
      endpoint w = v1 ∨ endpoint w = -v1 ∨
        endpoint w = v2 ∨ endpoint w = -v2 := by
  let K := Submodule.span ℤ (Set.range ![v1, v2])
  let L : ℕ := (p*m).toNat
  have hm : 0 < m := by omega
  have hL : (L : ℤ) = p*m := Int.toNat_of_nonneg (le_of_lt (mul_pos hp hm))
  have h1K : v1 ∈ K := by
    rw [show K = Submodule.span ℤ (Set.range ![v1, v2]) from rfl,
      Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    exact ⟨1, 0, by simp⟩
  have h2K : v2 ∈ K := by
    rw [show K = Submodule.span ℤ (Set.range ![v1, v2]) from rfl,
      Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    exact ⟨0, 1, by simp⟩
  change ∀ w : Fin L → Fin 4, K.mkQ.toAddMonoidHom (endpoint w) = 0 ↔ _
  intro w
  constructor
  · intro hw
    have hz : endpoint w ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hw
    rw [show K = Submodule.span ℤ (Set.range ![v1, v2]) from rfl,
      Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hz
    obtain ⟨q1, q2, hq⟩ := hz
    have hS : sumDiff (endpoint w) =
        ![p*(m*q1-b*q2), p*((-a)*q1+m*q2)] := by
      rw [← hq, map_add, map_smul, map_smul, hv1, hv2]
      ext i
      fin_cases i <;> simp <;> ring
    have hu := congrFun hS 0
    have hv := congrFun hS 1
    change endpoint w 0+endpoint w 1 = p*(m*q1-b*q2) at hu
    change endpoint w 0-endpoint w 1 = p*((-a)*q1+m*q2) at hv
    have hne : q1 ≠ q2 := by
      intro heq
      subst q2
      obtain ⟨d, hd⟩ := hmo.sub_odd hbo
      obtain ⟨j, hj⟩ := hpo.mul hmo
      have heven : endpoint w 0+endpoint w 1 = 2*(p*q1*d) := by
        calc
          endpoint w 0+endpoint w 1 = p*q1*(m-b) := by rw [hu]; ring
          _ = 2*(p*q1*d) := by rw [hd]; ring
      obtain ⟨hparity, _⟩ := PlaneWordEndpointCount.rotated_endpoint w
      rw [hL] at hparity
      omega
    have hnorm := endpoint_lee_bound w
    rw [hL] at hnorm
    obtain ⟨hU, hV⟩ := (LeeSquareCompression.lee_iff_square _ _ _).mp hnorm
    rw [hu, abs_mul, abs_of_pos hp] at hU
    rw [hv, abs_mul, abs_of_pos hp] at hV
    have hbound : max |m*q1-b*q2| |(-a)*q1+m*q2| ≤ m := by
      apply max_le
      · exact (mul_le_mul_iff_right₀ hp).mp hU
      · exact (mul_le_mul_iff_right₀ hp).mp hV
    rcases boundary_coefficients ha ham hb hbm q1 q2 hne hbound with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by simpa using hq.symm)
    · exact Or.inr (Or.inl (by simpa using hq.symm))
    · exact Or.inr (Or.inr (Or.inl (by simpa using hq.symm)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using hq.symm)))
  · intro hw
    apply (Submodule.Quotient.mk_eq_zero K).mpr
    rcases hw with hw | hw | hw | hw
    · rw [hw]; exact h1K
    · rw [hw]; exact K.neg_mem h1K
    · rw [hw]; exact h2K
    · rw [hw]; exact K.neg_mem h2K

private theorem four_fiber_card (L : ℕ) (p m a b : ℤ) (v1 v2 : Plane)
    (hp : 0 < p) (hb : 0 < b) (hbm : b < m)
    (hv1 : sumDiff v1 = ![p*m, -p*a])
    (hv2 : sumDiff v2 = ![-p*b, p*m]) :
    Nat.card {w : Fin L → Fin 4 // endpoint w = v1 ∨ endpoint w = -v1 ∨
      endpoint w = v2 ∨ endpoint w = -v2} =
    Nat.card {w : Fin L → Fin 4 // endpoint w = v1} +
      (Nat.card {w : Fin L → Fin 4 // endpoint w = -v1} +
        (Nat.card {w : Fin L → Fin 4 // endpoint w = v2} +
          Nat.card {w : Fin L → Fin 4 // endpoint w = -v2})) := by
  classical
  have hpb : 0 < p*b := mul_pos hp hb
  have hpbm : p*b < p*m := mul_lt_mul_of_pos_left hbm hp
  have hfirst : Disjoint (fun w : Fin L → Fin 4 => endpoint w = v1)
      (fun w => endpoint w = -v1 ∨ endpoint w = v2 ∨ endpoint w = -v2) := by
    apply Set.disjoint_left.mpr
    intro w hw hrest
    rcases hrest with hh | hh | hh
    all_goals
      have h := congrFun (congrArg sumDiff (hw.symm.trans hh)) 0
      simp only [map_neg, hv1, hv2, Pi.neg_apply, Matrix.cons_val_zero] at h
      nlinarith only [hpb, hpbm, h]
  have hsecond : Disjoint (fun w : Fin L → Fin 4 => endpoint w = -v1)
      (fun w => endpoint w = v2 ∨ endpoint w = -v2) := by
    apply Set.disjoint_left.mpr
    intro w hw hrest
    rcases hrest with hh | hh
    all_goals
      have h := congrFun (congrArg sumDiff (hw.symm.trans hh)) 0
      simp only [map_neg, hv1, hv2, Pi.neg_apply, Matrix.cons_val_zero] at h
      nlinarith only [hpb, hpbm, h]
  have hthird : Disjoint (fun w : Fin L → Fin 4 => endpoint w = v2)
      (fun w => endpoint w = -v2) := by
    apply Set.disjoint_left.mpr
    intro w hw hh
    have h := congrFun (congrArg sumDiff (hw.symm.trans hh)) 0
    simp only [map_neg, hv2, Pi.neg_apply, Matrix.cons_val_zero] at h
    nlinarith only [hpb, h]
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_or_disjoint _ _ hfirst,
    Fintype.card_subtype_or_disjoint _ _ hsecond,
    Fintype.card_subtype_or_disjoint _ _ hthird]

theorem odd_boundary_count_of_sumDiff (p m a b : ℤ) (v1 v2 : Plane)
    (hp : 0 < p) (hpo : Odd p) (hmo : Odd m) (hao : Odd a) (hbo : Odd b)
    (ha : 0 < a) (ham : a < m) (hb : 0 < b) (hbm : b < m)
    (hv1 : sumDiff v1 = ![p*m, -p*a])
    (hv2 : sumDiff v2 = ![-p*b, p*m]) :
    let K := Submodule.span ℤ (Set.range ![v1, v2])
    let F : Plane →+ (Plane ⧸ K) := K.mkQ.toAddMonoidHom
    let L : ℕ := (p*m).toNat
    W F L = 2*(Nat.choose L (p*(m+a)/2).toNat +
      Nat.choose L (p*(m+b)/2).toNat) := by
  classical
  let K := Submodule.span ℤ (Set.range ![v1, v2])
  let F : Plane →+ (Plane ⧸ K) := K.mkQ.toAddMonoidHom
  let L : ℕ := (p*m).toNat
  let A : ℕ := (p*(m+a)/2).toNat
  let B : ℕ := (p*(m+b)/2).toNat
  change W F L = 2*(Nat.choose L A+Nat.choose L B)
  have hm : 0 < m := by omega
  have hL : (L : ℤ) = p*m := Int.toNat_of_nonneg (le_of_lt (mul_pos hp hm))
  have hhalfA : 2*(p*(m+a)/2) = p*(m+a) := by
    have hd := ((hmo.add_odd hao).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have hhalfB : 2*(p*(m+b)/2) = p*(m+b) := by
    have hd := ((hmo.add_odd hbo).mul_left p).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have hA0 : 0 ≤ p*(m+a)/2 := by
    have hpos := mul_pos hp (show 0 < m+a by omega)
    nlinarith only [hhalfA, hpos]
  have hB0 : 0 ≤ p*(m+b)/2 := by
    have hpos := mul_pos hp (show 0 < m+b by omega)
    nlinarith only [hhalfB, hpos]
  have hA : (A : ℤ) = p*(m+a)/2 := Int.toNat_of_nonneg hA0
  have hB : (B : ℤ) = p*(m+b)/2 := Int.toNat_of_nonneg hB0
  have hAL : A ≤ L := by
    have htail := mul_pos hp (sub_pos.mpr ham)
    have hle : (A : ℤ) ≤ (L : ℤ) := by
      rw [hA, hL]
      nlinarith only [hhalfA, htail]
    exact_mod_cast hle
  have hBL : B ≤ L := by
    have htail := mul_pos hp (sub_pos.mpr hbm)
    have hle : (B : ℤ) ≤ (L : ℤ) := by
      rw [hB, hL]
      nlinarith only [hhalfB, htail]
    exact_mod_cast hle
  have h1sum := congrFun hv1 0
  have h1diff := congrFun hv1 1
  have h2sum := congrFun hv2 0
  have h2diff := congrFun hv2 1
  change v1 0+v1 1 = p*m at h1sum
  change v1 0-v1 1 = -p*a at h1diff
  change v2 0+v2 1 = -p*b at h2sum
  change v2 0-v2 1 = p*m at h2diff
  have heta (z : Plane) : ![z 0, z 1] = z := by
    ext i
    fin_cases i <;> rfl
  have hc1 : Nat.card {w : Fin L → Fin 4 // endpoint w = v1} =
      Nat.choose L A := by
    have hc := PlaneWordEndpointCount.endpoint_card L 0 A (v1 0) (v1 1)
      (by simpa only [Nat.cast_zero, mul_zero, sub_zero, hL] using h1sum.symm)
      (by rw [hL, hA]; nlinarith only [hhalfA, h1diff])
    simpa only [heta, Nat.choose_zero_right, one_mul] using hc
  have hcn1 : Nat.card {w : Fin L → Fin 4 // endpoint w = -v1} =
      Nat.choose L A := by
    have hc := PlaneWordEndpointCount.endpoint_card L L (L-A) ((-v1) 0) ((-v1) 1)
      (by simp only [Pi.neg_apply]; rw [hL]; nlinarith only [h1sum])
      (by
        rw [Nat.cast_sub hAL, hL, hA]
        simp only [Pi.neg_apply]
        nlinarith only [hhalfA, h1diff])
    simp only [heta, Nat.choose_self, one_mul] at hc
    rwa [Nat.choose_symm hAL] at hc
  have hc2 : Nat.card {w : Fin L → Fin 4 // endpoint w = v2} =
      Nat.choose L B := by
    have hc := PlaneWordEndpointCount.endpoint_card L B 0 (v2 0) (v2 1)
      (by rw [hL, hB]; nlinarith only [hhalfB, h2sum])
      (by simpa only [Nat.cast_zero, mul_zero, sub_zero, hL] using h2diff.symm)
    simpa only [heta, Nat.choose_zero_right, mul_one] using hc
  have hcn2 : Nat.card {w : Fin L → Fin 4 // endpoint w = -v2} =
      Nat.choose L B := by
    have hc := PlaneWordEndpointCount.endpoint_card L (L-B) L ((-v2) 0) ((-v2) 1)
      (by
        rw [Nat.cast_sub hBL, hL, hB]
        simp only [Pi.neg_apply]
        nlinarith only [hhalfB, h2sum])
      (by simp only [Pi.neg_apply]; rw [hL]; nlinarith only [h2diff])
    simp only [heta, Nat.choose_self, mul_one] at hc
    rwa [Nat.choose_symm hBL] at hc
  have hreturn := odd_boundary_return_iff p m a b v1 v2
    hp hpo hmo hbo ha ham hb hbm hv1 hv2
  have hcard : W F L = Nat.card {w : Fin L → Fin 4 //
      endpoint w = v1 ∨ endpoint w = -v1 ∨ endpoint w = v2 ∨ endpoint w = -v2} :=
    Nat.card_congr (Equiv.subtypeEquivRight hreturn)
  rw [hcard, four_fiber_card L p m a b v1 v2 hp hb hbm hv1 hv2,
    hc1, hcn1, hc2, hcn2]
  omega

/-- Exact return counts at length `p*m` in both original lattice quotients.
The domain is all signed coordinate words and the kernel is the complete
span of the displayed generators.  No finite endpoint classification or
counting premise is supplied by the caller. -/
theorem actual_odd_wrap_counts (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let L : ℕ := (p*m).toNat
    W F19 L = 2*(Nat.choose L (p*(m+1)/2).toNat +
      Nat.choose L (p*(m+9)/2).toNat) ∧
    W F33 L = 4*Nat.choose L (p*(m+3)/2).toNat := by
  let m : ℤ := 6*t-1
  let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
  let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
  let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
  let K19 := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 := Submodule.span ℤ (Set.range ![v133, v233])
  let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
  let L : ℕ := (p*m).toNat
  change W F19 L = 2*(Nat.choose L (p*(m+1)/2).toNat +
      Nat.choose L (p*(m+9)/2).toNat) ∧
    W F33 L = 4*Nat.choose L (p*(m+3)/2).toNat
  have hp : 0 < p := by omega
  have hm11 : 11 ≤ m := by dsimp [m]; omega
  have hmo : Odd m := ⟨3*t-1, by dsimp [m]; ring⟩
  obtain ⟨_, hv119, hv219, _⟩ := asymmetric_rank_one_actual_data p m 1 9
    hp hpo hmo odd_one (by decide) (by norm_num) (by omega) (by norm_num) (by omega)
  obtain ⟨_, hv133, hv233, _⟩ := asymmetric_rank_one_actual_data p m 3 3
    hp hpo hmo (by decide) (by decide) (by norm_num) (by omega) (by norm_num) (by omega)
  constructor
  · exact odd_boundary_count_of_sumDiff p m 1 9 v119 v219
      hp hpo hmo odd_one (by decide) (by norm_num) (by omega)
      (by norm_num) (by omega) hv119 hv219
  · have hc := odd_boundary_count_of_sumDiff p m 3 3 v133 v233
      hp hpo hmo (by decide) (by decide) (by norm_num) (by omega)
      (by norm_num) (by omega) hv133 hv233
    change W F33 L = 2*(Nat.choose L (p*(m+3)/2).toNat +
      Nat.choose L (p*(m+3)/2).toNat) at hc
    omega

end D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
