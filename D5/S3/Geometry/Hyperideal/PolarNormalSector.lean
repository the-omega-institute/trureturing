/- GID: D5/S3/Geometry/Hyperideal/PolarNormalSector
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/PolarNormalSector
   mirror-E: none(waiver:local-lorentz-geometry)
   anchors: []
   utility: none
   digest: The actual forward geodesic sector of a polar edge in an algebraic Lorentz frame. -/

import D5.S3.Geometry.Hyperideal.PolarModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Module
namespace D5.S3.Geometry.Hyperideal.PolarNormalSector

local instance : AddCommGroup Space :=
  (inferInstance : NormedAddCommGroup Space).toAddCommGroup
local instance : Module ℝ Space :=
  (inferInstance : NormedSpace ℝ Space).toModule
local instance : TopologicalSpace Space :=
  (inferInstance : PseudoMetricSpace Space).toUniformSpace.toTopologicalSpace

set_option maxHeartbeats 1000000 in
/-- The actual local sector and its compatible Lorentz angle. -/
theorem polar_edge_forward_sector (F : GramFrame) (e : Equiv.Perm (Fin 4))
    (s : ℝ) (hs : 0 < s ∧ s < Real.arcosh (F.lengths (e 0) (e 1))) :
    edgePoint F e s ∈ polarSet F ∧
    lorentz (edgeVelocity F e s) (edgeVelocity F e s)=1 ∧
    lorentz (edgePoint F e s) (edgeVelocity F e s)=0 ∧
    (∀ u : Space, u ∈ normalSpace F e s ↔
      ∃ α β : ℝ, u=α • dualVertex F (e 2)+β • dualVertex F (e 3)) ∧
    Module.finrank ℝ (normalSpace F e s)=2 ∧
    (∀ u : Space, u ∈ forwardNormalSet F e s ↔
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
        u=α • inwardRay F e false+β • inwardRay F e true) ∧
    lorentz (inwardRay F e false) (inwardRay F e false)=1 ∧
    lorentz (inwardRay F e true) (inwardRay F e true)=1 ∧
    0 < 1-(normalCosine F e)^2 ∧
    (let D := -(gramMatrix F e).det
     let A := FourCycleEnvelopes.rad (F.lengths (e 0) (e 1))
       (F.lengths (e 0) (e 2)) (F.lengths (e 1) (e 2))
     let B := FourCycleEnvelopes.rad (F.lengths (e 0) (e 1))
       (F.lengths (e 0) (e 3)) (F.lengths (e 1) (e 3))
     let P := FourCycleEnvelopes.numerator (F.lengths (e 0) (e 1))
       (F.lengths (e 0) (e 2)) (F.lengths (e 0) (e 3))
       (F.lengths (e 2) (e 3)) (F.lengths (e 1) (e 3)) (F.lengths (e 1) (e 2))
     0 < D ∧ D=((frameMatrix F e).det)^2 ∧
       lorentz (dualVertex F (e 2)) (dualVertex F (e 2))=B/D ∧
       lorentz (dualVertex F (e 3)) (dualVertex F (e 3))=A/D ∧
       lorentz (dualVertex F (e 2)) (dualVertex F (e 3))= -P/D ∧
       A*B-P^2=((F.lengths (e 0) (e 1))^2-1)*D) ∧
    (∀ q u : Space, lorentz q q = -1 → lorentz q u = 0 →
      inner ℝ u.2 u.2 ≤ q.1^2 * lorentz u u ∧
      (lorentz u u = 0 ↔ u = 0)) ∧
    HasDerivAt (edgePoint F e) (edgeVelocity F e s) s ∧
    ((∀ i : Fin 4, lorentz (edgePoint F e s) (dualVertex F (e i)) =
        (Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))))⁻¹ *
        (Real.cosh (Real.arcosh (F.lengths (e 0) (e 1))-s) * (if i=0 then 1 else 0) +
         Real.cosh s * (if i=1 then 1 else 0))) ∧
      lorentz (edgePoint F e s) (vertex F (e 0)) = -Real.sinh s ∧
      lorentz (edgePoint F e s) (vertex F (e 1)) =
        -Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))-s) ∧
      (∀ i : Fin 4, lorentz (edgePoint F e s) (vertex F (e i)) < 0) ∧
      (∀ i : Fin 4, i=2 ∨ i=3 →
        lorentz (edgePoint F e s) (vertex F (e i)) =
        -(F.lengths (e 0) (e i)*Real.cosh (Real.arcosh (F.lengths (e 0) (e 1))-s) +
          F.lengths (e 1) (e i)*Real.cosh s) /
          Real.sinh (Real.arcosh (F.lengths (e 0) (e 1))))) ∧
    (∀ u : Space, u ∈ forwardNormalSet F e s ↔
      u ∈ normalSpace F e s ∧ lorentz u (outwardNormal F (e 2)) ≤ 0 ∧
        lorentz u (outwardNormal F (e 3)) ≤ 0) ∧
    lorentz (inwardRay F e false) (inwardRay F e true) =
      FourCycleEnvelopes.cosine (F.lengths (e 0) (e 1))
        (F.lengths (e 0) (e 2)) (F.lengths (e 0) (e 3))
        (F.lengths (e 2) (e 3)) (F.lengths (e 1) (e 3)) (F.lengths (e 1) (e 2)) ∧
    ∃ (hp : lorentz (edgePoint F e s) (edgePoint F e s) = -1)
      (h₂ : lorentz (edgePoint F e s) (inwardRay F e false) = 0)
      (h₃ : lorentz (edgePoint F e s) (inwardRay F e true) = 0),
      tangentAngle (edgePoint F e s) hp ⟨inwardRay F e false,h₂⟩
        ⟨inwardRay F e true,h₃⟩ = Real.arccos (FourCycleEnvelopes.cosine (F.lengths (e 0) (e 1))
        (F.lengths (e 0) (e 2)) (F.lengths (e 0) (e 3))
        (F.lengths (e 2) (e 3)) (F.lengths (e 1) (e 3)) (F.lengths (e 1) (e 2))) := by
  have sym (u v : Space) : lorentz u v = lorentz v u := by
    change -u.1*v.1 + inner ℝ u.2 v.2 = -v.1*u.1 + inner ℝ v.2 u.2
    rw [real_inner_comm]; ring
  have iso (u v : Space) :
      lorentz (timeOrientation F u) (timeOrientation F v) = lorentz u v := by
    unfold timeOrientation
    split_ifs
    · rfl
    · change -(-u.1)*(-v.1) + inner ℝ u.2 v.2 =
        -u.1*v.1 + inner ℝ u.2 v.2
      ring
  have gram (i j : Fin 4) : lorentz (vertex F i) (vertex F j) =
      if i = j then 1 else -F.lengths i j := by
    rw [vertex, vertex, iso, F.gram]
  have dual (i j : Fin 4) : lorentz (vertex F i) (dualVertex F j) =
      if i = j then 1 else 0 := by
    rw [vertex, dualVertex, iso, F.duality]
  let z : Space := ∑ i, F.vertices i
  have hz : lorentz z z < -8 := by
    dsimp [z]
    simp only [map_sum, LinearMap.sum_apply, Fin.sum_univ_four]
    norm_num [F.gram, Fin.ext_iff]
    linarith [(F.box 0 1 (by decide)).1, (F.box 0 2 (by decide)).1,
      (F.box 0 3 (by decide)).1, (F.box 1 0 (by decide)).1,
      (F.box 1 2 (by decide)).1, (F.box 1 3 (by decide)).1,
      (F.box 2 0 (by decide)).1, (F.box 2 1 (by decide)).1,
      (F.box 2 3 (by decide)).1, (F.box 3 0 (by decide)).1,
      (F.box 3 1 (by decide)).1, (F.box 3 2 (by decide)).1]
  have hzne : z.1 ≠ 0 := by
    intro h
    have hsp := (real_inner_self_nonneg (x := z.2))
    change -z.1*z.1 + inner ℝ z.2 z.2 < -8 at hz
    rw [h] at hz
    linarith
  let Z : Space := timeOrientation F z
  have hZ : lorentz Z Z < -8 := by simpa [Z, iso] using hz
  have hZtime : 0 < Z.1 := by
    dsimp [Z, timeOrientation]
    split_ifs with h
    · exact lt_of_le_of_ne h (Ne.symm hzne)
    · change 0 < -z.1
      exact neg_pos.mpr (lt_of_not_ge h)
  have future (q : Space) (hq : lorentz q q = -1) (hqZ : lorentz q Z < 0) :
      0 < q.1 := by
    have hqsp : inner ℝ q.2 q.2 < q.1 ^ 2 := by
      change -q.1*q.1 + inner ℝ q.2 q.2 = -1 at hq
      nlinarith
    have hZsp : inner ℝ Z.2 Z.2 < Z.1 ^ 2 := by
      change -Z.1*Z.1 + inner ℝ Z.2 Z.2 < -8 at hZ
      nlinarith
    have hqt : 0 < q.1 ^ 2 := lt_of_le_of_lt (real_inner_self_nonneg) hqsp
    have hprod : inner ℝ q.2 q.2 * inner ℝ Z.2 Z.2 < q.1 ^ 2 * Z.1 ^ 2 :=
      (mul_le_mul_of_nonneg_right hqsp.le (real_inner_self_nonneg)).trans_lt
        (mul_lt_mul_of_pos_left hZsp hqt)
    have hcs := real_inner_mul_inner_self_le q.2 Z.2
    change -q.1*Z.1 + inner ℝ q.2 Z.2 < 0 at hqZ
    by_contra h
    have hqt' : q.1 ≤ 0 := le_of_not_gt h
    have hmul : q.1 * Z.1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hqt' hZtime.le
    have hneg : inner ℝ q.2 Z.2 < 0 := by linarith
    have hsq : (q.1 * Z.1)^2 < (inner ℝ q.2 Z.2)^2 := by
      nlinarith
    nlinarith
  let a := F.lengths (e 0) (e 1)
  let L := Real.arcosh a
  let d := Real.sinh L
  let A := Real.cosh (L-s)
  let C := Real.cosh s
  let S := Real.sinh s
  let T := Real.sinh (L-s)
  have he01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have ha : 1 < a := (F.box _ _ he01).1
  have hd : 0 < d := Real.sinh_pos_iff.mpr (Real.arcosh_pos ha)
  have hcoshL : Real.cosh L = a := Real.cosh_arcosh ha.le
  have hd2 : a^2 - d^2 = 1 := by
    simpa only [hcoshL, d] using Real.cosh_sq_sub_sinh_sq L
  have hAC : A = a*C-d*S := by
    dsimp [A, C, S, d]
    rw [Real.cosh_sub, hcoshL]
  have hTC : T = d*C-a*S := by
    dsimp [T, C, S, d]
    rw [Real.sinh_sub, hcoshL]
  have hCS : C^2-S^2=1 := Real.cosh_sq_sub_sinh_sq s
  have hAT : A^2-T^2=1 := Real.cosh_sq_sub_sinh_sq (L-s)
  have hSC : 0 < S := Real.sinh_pos_iff.mpr hs.1
  have hTCpos : 0 < T := Real.sinh_pos_iff.mpr (sub_pos.mpr hs.2)
  have hApos : 0 < A := Real.cosh_pos _
  have hCpos : 0 < C := Real.cosh_pos _
  have hb12 : lorentz (vertex F (e 1)) (vertex F (e 0)) = -a := by
    rw [sym, gram]; simp [he01, a]
  have gg00 : lorentz (vertex F (e 0)) (vertex F (e 0))=1 := by simp only [gram,ite_true]
  have gg11 : lorentz (vertex F (e 1)) (vertex F (e 1))=1 := by simp only [gram,ite_true]
  have gg01 : lorentz (vertex F (e 0)) (vertex F (e 1))= -a := by
    rw [gram];simp only [if_neg he01];rfl
  let p := edgePoint F e s
  have hpformula : p = d⁻¹ • (A • vertex F (e 0) + C • vertex F (e 1)) := rfl
  have hpunit : lorentz p p = -1 := by
    rw [hpformula]
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, gg00, gg01, hb12, gg11, one_mul, mul_one]
    have hpoly : A^2 + C^2 - 2*a*A*C = -d^2 := by
      rw [hAC]
      linear_combination -(C^2) * hd2 - d^2 * hCS
    field_simp [hd.ne']
    nlinarith [hpoly]
  have hlat (i : Fin 4) : lorentz p (dualVertex F (e i)) =
      d⁻¹ * (A * (if i = 0 then 1 else 0) + C * (if i = 1 then 1 else 0)) := by
    rw [hpformula]
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, dual, Equiv.apply_eq_iff_eq]
    congr 2
    · simp [eq_comm]
    · simp [eq_comm]
  have htr0 : lorentz p (vertex F (e 0)) = -S := by
    rw [hpformula]
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, gg00, gg01, hb12, gg11, one_mul, mul_one]
    change d⁻¹ * (A + C * -a) = -S
    rw [hAC]
    field_simp [hd.ne']
    ring
  have htr1 : lorentz p (vertex F (e 1)) = -T := by
    rw [hpformula]
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, gg00, gg01, hb12, gg11, one_mul, mul_one]
    change d⁻¹ * (A * -a + C) = -T
    rw [hAC, hTC]
    field_simp [hd.ne']
    linear_combination -C * hd2
  have htr (i : Fin 4) : lorentz p (vertex F (e i)) < 0 := by
    by_cases hi0 : i = 0
    · subst i; rw [htr0]; exact neg_neg_of_pos hSC
    by_cases hi1 : i = 1
    · subst i; rw [htr1]; exact neg_neg_of_pos hTCpos
    rw [hpformula]
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, gram, Equiv.apply_eq_iff_eq, if_neg (Ne.symm hi0), if_neg (Ne.symm hi1)]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hd)
      (add_neg (mul_neg_of_pos_of_neg hApos (by linarith [(F.box _ _ (e.injective.ne (Ne.symm hi0))).1]))
        (mul_neg_of_pos_of_neg hCpos (by linarith [(F.box _ _ (e.injective.ne (Ne.symm hi1))).1])))
  have hpZ : lorentz p Z < 0 := by
    have hsum : Z = ∑ i : Fin 4, vertex F (e i) := by
      dsimp [Z, z, vertex]
      rw [map_sum]
      exact (Equiv.sum_comp e (fun i => timeOrientation F (F.vertices i))).symm
    rw [hsum, map_sum]
    exact Finset.sum_neg (fun i _ => htr i) (by simp)
  have hpfuture : 0 < p.1 := future p hpunit hpZ
  have hpK : p ∈ polarSet F := by
    refine ⟨hpunit, hpfuture, ?_, ?_⟩
    · intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      rw [hlat]
      positivity
    · intro i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact (htr j).le
  have hvunit : lorentz (edgeVelocity F e s) (edgeVelocity F e s) = 1 := by
    change lorentz (d⁻¹ • (-T • vertex F (e 0) + S • vertex F (e 1)))
      (d⁻¹ • (-T • vertex F (e 0) + S • vertex F (e 1))) = 1
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, gg00, gg01, hb12, gg11, one_mul, mul_one]
    have hpoly : T^2+S^2+2*a*T*S=d^2 := by
      rw [hTC]
      linear_combination d^2*hCS-S^2*hd2
    field_simp [hd.ne']
    nlinarith only [hpoly]
  have hpv : lorentz p (edgeVelocity F e s) = 0 := by
    rw [hpformula]
    change lorentz (d⁻¹ • (A • vertex F (e 0) + C • vertex F (e 1)))
      (d⁻¹ • (-T • vertex F (e 0) + S • vertex F (e 1))) = 0
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, gg00, gg01, hb12, gg11, one_mul, mul_one]
    field_simp [hd.ne']
    rw [hAC,hTC]
    linear_combination -(C*S)*hd2
  generalize hWbase : (F.dual.reindex e.symm).map (timeOrientation F) = W
  have hW (i : Fin 4) : W i = dualVertex F (e i) := by
    rw [← hWbase]
    simp [dualVertex, Basis.map_apply, Basis.reindex_apply]
  have wcoord (u : Space) (i : Fin 4) :
      lorentz (vertex F (e i)) u = W.repr u i := by
    conv_lhs => rw [← W.sum_repr u]
    simp only [map_sum, map_smul, hW, dual, Equiv.apply_eq_iff_eq, smul_eq_mul]
    simp [Finset.sum_ite_eq', eq_comm]
  have hvformula : edgeVelocity F e s =
      d⁻¹ • (-T • vertex F (e 0) + S • vertex F (e 1)) := rfl
  have hASCT : A*S+C*T=d := by
    rw [hAC, hTC]
    linear_combination d * hCS
  have endpoint_zero (u : Space) (hu : u ∈ normalSpace F e s) :
      W.repr u 0 = 0 ∧ W.repr u 1 = 0 := by
    change lorentz p u = 0 ∧ lorentz (edgeVelocity F e s) u = 0 at hu
    have hpu := hu.1
    have hvu := hu.2
    rw [hpformula] at hpu
    rw [hvformula] at hvu
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, wcoord] at hpu hvu
    have h1 : A * W.repr u 0 + C * W.repr u 1 = 0 :=
      (mul_eq_zero.mp hpu).resolve_left (inv_ne_zero hd.ne')
    have h2 : -T * W.repr u 0 + S * W.repr u 1 = 0 :=
      (mul_eq_zero.mp hvu).resolve_left (inv_ne_zero hd.ne')
    have h0 : d * W.repr u 0 = 0 := by
      linear_combination S*h1-C*h2-W.repr u 0*hASCT
    have h3 : d * W.repr u 1 = 0 := by
      linear_combination T*h1+A*h2-W.repr u 1*hASCT
    exact ⟨(mul_eq_zero.mp h0).resolve_left hd.ne',
      (mul_eq_zero.mp h3).resolve_left hd.ne'⟩
  have normal_w (j : Fin 4) (hj : j = 2 ∨ j = 3) :
      W j ∈ normalSpace F e s := by
    change lorentz p (W j) = 0 ∧ lorentz (edgeVelocity F e s) (W j) = 0
    rw [hpformula, hvformula]
    simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul, hW, dual, Equiv.apply_eq_iff_eq]
    rcases hj with rfl | rfl <;> norm_num [Fin.ext_iff]
  have normal_decompose (u : Space) : u ∈ normalSpace F e s ↔
      ∃ α β : ℝ, u = α • W 2 + β • W 3 := by
    constructor
    · intro hu
      obtain ⟨h0,h1⟩ := endpoint_zero u hu
      refine ⟨W.repr u 2, W.repr u 3, ?_⟩
      have h := W.sum_repr u
      simp only [Fin.sum_univ_four, h0, h1, zero_smul, zero_add] at h
      exact h.symm
    · rintro ⟨α,β,rfl⟩
      exact (normalSpace F e s).add_mem
        ((normalSpace F e s).smul_mem α (normal_w 2 (Or.inl rfl)))
        ((normalSpace F e s).smul_mem β (normal_w 3 (Or.inr rfl)))
  let normalEquiv : (normalSpace F e s) ≃ₗ[ℝ] (ℝ × ℝ) := {
    toFun := fun u => (W.repr u.val 2,W.repr u.val 3)
    invFun := fun f => ⟨f.1 • W 2 + f.2 • W 3,
      (normalSpace F e s).add_mem
        ((normalSpace F e s).smul_mem f.1 (normal_w 2 (Or.inl rfl)))
        ((normalSpace F e s).smul_mem f.2 (normal_w 3 (Or.inr rfl)))⟩
    left_inv := by
      intro u
      apply Subtype.ext
      obtain ⟨h0,h1⟩ := endpoint_zero u.val u.property
      have he := W.sum_repr u.val
      simpa only [Fin.sum_univ_four,h0,h1,zero_smul,zero_add] using he
    right_inv := by
      intro f
      apply Prod.ext <;>
        simp [map_add,map_smul,Basis.repr_self_apply,Finsupp.smul_apply,
          smul_eq_mul,Fin.ext_iff]
    map_add' := by
      intro u v
      apply Prod.ext <;> simp
    map_smul' := by
      intro r u
      apply Prod.ext <;> simp }
  have hnormalrank : Module.finrank ℝ (normalSpace F e s)=2 := by
    rw [normalEquiv.finrank_eq]
    simp
  have hwwpos (j : Fin 4) (hj : j = 2 ∨ j = 3) : 0 < lorentz (W j) (W j) := by
    have hjp := (normal_w j hj).1
    let wt : Tangent p := ⟨W j,hjp⟩
    let core := tangentCore p hpunit
    have hn := core.re_inner_nonneg wt
    change 0 ≤ lorentz (W j) (W j) at hn
    refine lt_of_le_of_ne hn ?_
    intro hz
    have he := core.definite wt hz.symm
    exact W.ne_zero j (congrArg Subtype.val he)
  let q₂ := Real.sqrt (lorentz (W 2) (W 2))
  let q₃ := Real.sqrt (lorentz (W 3) (W 3))
  have hq₂ : 0 < q₂ := Real.sqrt_pos.mpr (hwwpos 2 (Or.inl rfl))
  have hq₃ : 0 < q₃ := Real.sqrt_pos.mpr (hwwpos 3 (Or.inr rfl))
  have hq₂sq : q₂^2=lorentz (W 2) (W 2) := Real.sq_sqrt (hwwpos 2 (Or.inl rfl)).le
  have hq₃sq : q₃^2=lorentz (W 3) (W 3) := Real.sq_sqrt (hwwpos 3 (Or.inr rfl)).le
  let n₂ := outwardNormal F (e 2)
  let n₃ := outwardNormal F (e 3)
  have hn₂ : n₂ = -q₂⁻¹ • W 2 := by simp [n₂,outwardNormal,hW,q₂]
  have hn₃ : n₃ = -q₃⁻¹ • W 3 := by simp [n₃,outwardNormal,hW,q₃]
  have hn₂N : n₂ ∈ normalSpace F e s := by
    rw [hn₂];exact (normalSpace F e s).smul_mem _ (normal_w 2 (Or.inl rfl))
  have hn₃N : n₃ ∈ normalSpace F e s := by
    rw [hn₃];exact (normalSpace F e s).smul_mem _ (normal_w 3 (Or.inr rfl))
  have hn₂unit : lorentz n₂ n₂ = 1 := by
    rw [hn₂]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [← hq₂sq]
    field_simp [hq₂.ne']
  have hn₃unit : lorentz n₃ n₃ = 1 := by
    rw [hn₃]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [← hq₃sq]
    field_simp [hq₃.ne']
  let c := normalCosine F e
  have hc : lorentz n₂ n₃=c := rfl
  have independent (a b : ℝ) (h : a • n₂ + b • n₃=0) : a=0 ∧ b=0 := by
    rw [hn₂,hn₃] at h
    have h₂ := congrArg (fun u => W.repr u 2) h
    have h₃ := congrArg (fun u => W.repr u 3) h
    simp [map_add,map_smul,Basis.repr_self_apply,Finsupp.smul_apply,smul_eq_mul] at h₂ h₃
    exact ⟨h₂.resolve_right hq₂.ne', h₃.resolve_right hq₃.ne'⟩
  have hresN : n₃-c • n₂ ∈ normalSpace F e s :=
    (normalSpace F e s).sub_mem hn₃N ((normalSpace F e s).smul_mem c hn₂N)
  have hresne : n₃-c • n₂ ≠ 0 := by
    intro h
    have he : (-c) • n₂ + (1:ℝ) • n₃=0 := by simpa [sub_eq_add_neg,neg_smul,add_comm] using h
    have hi := (independent (-c) 1 he).2
    norm_num at hi
  have hcpos : 0 < 1-c^2 := by
    let r : Tangent p := ⟨n₃-c • n₂,hresN.1⟩
    let core := tangentCore p hpunit
    have hrn := core.re_inner_nonneg r
    have hre : core.inner r r ≠ 0 := by
      intro h
      exact hresne (congrArg Subtype.val (core.definite r h))
    have hrp := lt_of_le_of_ne hrn (Ne.symm hre)
    change 0 < lorentz (n₃-c • n₂) (n₃-c • n₂) at hrp
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,
      smul_eq_mul,hn₂unit,hn₃unit,sym n₃ n₂,hc] at hrp
    nlinarith only [hrp]
  let η := Real.sqrt (1-c^2)
  have hη : 0 < η := Real.sqrt_pos.mpr hcpos
  have hηsq : η^2=1-c^2 := Real.sq_sqrt hcpos.le
  let r₂ := inwardRay F e false
  let r₃ := inwardRay F e true
  have hr₂ : r₂=η⁻¹ • (-n₃+c • n₂) := rfl
  have hr₃ : r₃=η⁻¹ • (-n₂+c • n₃) := rfl
  have hr₂N : r₂ ∈ normalSpace F e s := by
    rw [hr₂];exact (normalSpace F e s).smul_mem _
      ((normalSpace F e s).add_mem ((normalSpace F e s).neg_mem hn₃N)
        ((normalSpace F e s).smul_mem c hn₂N))
  have hr₃N : r₃ ∈ normalSpace F e s := by
    rw [hr₃];exact (normalSpace F e s).smul_mem _
      ((normalSpace F e s).add_mem ((normalSpace F e s).neg_mem hn₂N)
        ((normalSpace F e s).smul_mem c hn₃N))
  have hr₂n₂ : lorentz r₂ n₂=0 := by
    rw [hr₂];simp only [map_smul,map_add,map_neg,LinearMap.smul_apply,
      LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,sym n₃ n₂,hc,hn₂unit];ring
  have hr₂n₃ : lorentz r₂ n₃ = -η := by
    rw [hr₂];simp only [map_smul,map_add,map_neg,LinearMap.smul_apply,
      LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,hc,hn₃unit]
    field_simp [hη.ne'];nlinarith only [hηsq]
  have hr₃n₃ : lorentz r₃ n₃=0 := by
    rw [hr₃];simp only [map_smul,map_add,map_neg,LinearMap.smul_apply,
      LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,hc,hn₃unit];ring
  have hr₃n₂ : lorentz r₃ n₂ = -η := by
    rw [hr₃];simp only [map_smul,map_add,map_neg,LinearMap.smul_apply,
      LinearMap.add_apply,LinearMap.neg_apply,smul_eq_mul,sym n₃ n₂,hc,hn₂unit]
    field_simp [hη.ne'];nlinarith only [hηsq]
  have normal_dual_zero (v : Space) (hvN : v ∈ normalSpace F e s)
      (hv₂ : lorentz v n₂=0) (hv₃ : lorentz v n₃=0) : v=0 := by
    have hw₂ : lorentz v (W 2)=0 := by
      rw [hn₂] at hv₂
      simp only [map_smul,smul_eq_mul] at hv₂
      exact (mul_eq_zero.mp hv₂).resolve_left (neg_ne_zero.mpr (inv_ne_zero hq₂.ne'))
    have hw₃ : lorentz v (W 3)=0 := by
      rw [hn₃] at hv₃
      simp only [map_smul,smul_eq_mul] at hv₃
      exact (mul_eq_zero.mp hv₃).resolve_left (neg_ne_zero.mpr (inv_ne_zero hq₃.ne'))
    obtain ⟨α,β,hv⟩ := (normal_decompose v).mp hvN
    have hvv : lorentz v v=0 := by
      conv_lhs => rhs;rw [hv]
      simp only [map_add,map_smul,smul_eq_mul,hw₂,hw₃,mul_zero,zero_add]
    let vt : Tangent p := ⟨v,hvN.1⟩
    exact congrArg Subtype.val ((tangentCore p hpunit).definite vt hvv)
  have rays_span (u : Space) :
      (u ∈ normalSpace F e s ∧ lorentz u n₂ ≤ 0 ∧ lorentz u n₃ ≤ 0) ↔
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ u = α • r₂ + β • r₃ := by
    constructor
    · rintro ⟨huN,hu₂,hu₃⟩
      let α := -lorentz u n₃/η
      let β := -lorentz u n₂/η
      refine ⟨α,β,div_nonneg (neg_nonneg.mpr hu₃) hη.le,
        div_nonneg (neg_nonneg.mpr hu₂) hη.le, ?_⟩
      let v := u-(α • r₂+β • r₃)
      have hvN : v ∈ normalSpace F e s :=
        (normalSpace F e s).sub_mem huN ((normalSpace F e s).add_mem
          ((normalSpace F e s).smul_mem α hr₂N)
          ((normalSpace F e s).smul_mem β hr₃N))
      have hv₂ : lorentz v n₂=0 := by
        dsimp [v,β]
        simp only [map_sub,map_add,map_smul,LinearMap.sub_apply,LinearMap.add_apply,
          LinearMap.smul_apply,smul_eq_mul,hr₂n₂,hr₃n₂,mul_zero,zero_add]
        field_simp [hη.ne']
        ring
      have hv₃ : lorentz v n₃=0 := by
        dsimp [v,α]
        simp only [map_sub,map_add,map_smul,LinearMap.sub_apply,LinearMap.add_apply,
          LinearMap.smul_apply,smul_eq_mul,hr₂n₃,hr₃n₃,mul_zero,add_zero]
        field_simp [hη.ne']
        ring
      exact sub_eq_zero.mp (normal_dual_zero v hvN hv₂ hv₃)
    · rintro ⟨α,β,hα,hβ,rfl⟩
      refine ⟨(normalSpace F e s).add_mem
        ((normalSpace F e s).smul_mem α hr₂N)
        ((normalSpace F e s).smul_mem β hr₃N), ?_, ?_⟩
      · simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
          smul_eq_mul,hr₂n₂,hr₃n₂,mul_zero,zero_add]
        exact mul_nonpos_of_nonneg_of_nonpos hβ (neg_nonpos.mpr hη.le)
      · simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
          smul_eq_mul,hr₂n₃,hr₃n₃,mul_zero,add_zero]
        exact mul_nonpos_of_nonneg_of_nonpos hα (neg_nonpos.mpr hη.le)
  have hr₂unit : lorentz r₂ r₂=1 := by
    rw [hr₂]
    simp only [map_smul,map_add,map_neg,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.neg_apply,smul_eq_mul,hn₂unit,hn₃unit,sym n₃ n₂,hc]
    field_simp [hη.ne']
    nlinarith only [hηsq]
  have hr₃unit : lorentz r₃ r₃=1 := by
    rw [hr₃]
    simp only [map_smul,map_add,map_neg,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.neg_apply,smul_eq_mul,hn₂unit,hn₃unit,sym n₃ n₂,hc]
    field_simp [hη.ne']
    nlinarith only [hηsq]
  have hr₂₃ : lorentz r₂ r₃ = -c := by
    rw [hr₂,hr₃]
    simp only [map_smul,map_add,map_neg,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.neg_apply,smul_eq_mul,hn₂unit,hn₃unit,sym n₃ n₂,hc]
    field_simp [hη.ne']
    linear_combination c*hηsq
  have forward_halfspaces : ∀ u : Space, u ∈ forwardNormalSet F e s ↔
      u ∈ normalSpace F e s ∧
        0 ≤ lorentz u (dualVertex F (e 2)) ∧
        0 ≤ lorentz u (dualVertex F (e 3)) := by
    intro u
    change (lorentz p u = 0 ∧ lorentz (edgeVelocity F e s) u = 0 ∧ _) ↔ _

    by_cases hu0 : u = 0
    · subst u
      constructor
      · intro _
        refine ⟨?_, by simp, by simp⟩
        change lorentz p 0 = 0 ∧ lorentz (edgeVelocity F e s) 0 = 0
        simp
      · intro _
        refine ⟨by simp, by simp, 1, by norm_num, ?_⟩
        intro t _
        simpa [normalGeodesic] using hpK
    let μ := Real.sqrt (lorentz u u)
    have geodesic (hpu : lorentz p u = 0) :
        0 < μ ∧ Continuous (normalGeodesic p u) ∧ normalGeodesic p u 0 = p ∧
        ∀ t : ℝ, lorentz (normalGeodesic p u t) (normalGeodesic p u t) = -1 := by
      let ut : Tangent p := ⟨u, hpu⟩
      let core := tangentCore p hpunit
      have hn : 0 ≤ lorentz u u := by
        have h := core.re_inner_nonneg ut
        change 0 ≤ lorentz u u at h
        exact h
      have he : lorentz u u ≠ 0 := by
        intro h
        have hz := core.definite ut h
        exact hu0 (congrArg Subtype.val hz)
      have hμ : 0 < μ := Real.sqrt_pos.mpr (lt_of_le_of_ne hn (Ne.symm he))
      have hμ2 : μ^2 = lorentz u u := Real.sq_sqrt hn
      refine ⟨hμ, ?_, ?_, ?_⟩
      · unfold normalGeodesic
        simp only [if_neg hu0]
        fun_prop
      · simp [normalGeodesic, hu0]
      · intro t
        unfold normalGeodesic
        simp only [if_neg hu0, map_add, map_smul, LinearMap.add_apply,
          LinearMap.smul_apply, smul_eq_mul, hpunit, sym u p, hpu,
          mul_zero, zero_mul, add_zero, zero_add]
        change Real.cosh (t*μ) * (Real.cosh (t*μ) * -1) +
          (Real.sinh (t*μ)/μ)*((Real.sinh (t*μ)/μ)*lorentz u u) = -1
        rw [← hμ2]
        field_simp [hμ.ne']
        nlinarith only [Real.cosh_sq_sub_sinh_sq (t*μ)]
    have active (i : Fin 4) (hi : i = 2 ∨ i = 3) (t : ℝ) :
        lorentz (normalGeodesic p u t) (dualVertex F (e i)) =
          (Real.sinh (t*μ)/μ) * lorentz u (dualVertex F (e i)) := by
      unfold normalGeodesic
      simp only [if_neg hu0, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rcases hi with rfl | rfl <;> rw [hlat] <;> norm_num [Fin.ext_iff, μ]
    constructor
    · rintro ⟨hpu, hvu, ε, hε, hforward⟩
      have hμ := (geodesic hpu).1
      let t := ε/2
      have ht : t ∈ Set.Ioo 0 ε := by dsimp [t]; constructor <;> linarith
      have hCoeff : 0 < Real.sinh (t*μ)/μ :=
        div_pos (Real.sinh_pos_iff.mpr (mul_pos ht.1 hμ)) hμ
      have hk := (hforward t ht).2.2.1
      refine ⟨?_, ?_, ?_⟩
      · exact ⟨hpu, hvu⟩
      · have h := hk (e 2)
        rw [active 2 (Or.inl rfl)] at h
        exact nonneg_of_mul_nonneg_right h hCoeff
      · have h := hk (e 3)
        rw [active 3 (Or.inr rfl)] at h
        exact nonneg_of_mul_nonneg_right h hCoeff
    · rintro ⟨huN, hu2, hu3⟩
      change lorentz p u = 0 ∧ lorentz (edgeVelocity F e s) u = 0 at huN
      have hg := geodesic huN.1
      have hc := hg.2.1
      have hγ0 := hg.2.2.1
      have hγunit := hg.2.2.2
      have htime : ∀ᶠ t in nhds (0:ℝ), 0 < (normalGeodesic p u t).1 := by
        have h := ((continuous_fst.comp hc).continuousAt (x := (0:ℝ))).tendsto
        exact h.eventually_const_lt (by simpa only [Function.comp_apply,hγ0] using hpfuture)
      have htrunc : ∀ᶠ t in nhds (0:ℝ),
          ∀ i : Fin 4, lorentz (normalGeodesic p u t) (vertex F (e i)) < 0 := by
        apply Filter.eventually_all.mpr
        intro i
        have hf : Continuous (fun t => lorentz (normalGeodesic p u t) (vertex F (e i))) := by
          unfold normalGeodesic
          simp only [if_neg hu0]
          dsimp [lorentz]
          fun_prop
        exact (hf.continuousAt (x := (0:ℝ))).tendsto.eventually_lt_const (by rw [hγ0]; exact htr i)
      have hlateral (i : Fin 4) (hi : i = 0 ∨ i = 1) :
          ∀ᶠ t in nhds (0:ℝ), 0 < lorentz (normalGeodesic p u t) (dualVertex F (e i)) := by
        have hf : Continuous (fun t => lorentz (normalGeodesic p u t) (dualVertex F (e i))) := by
          unfold normalGeodesic
          simp only [if_neg hu0]
          dsimp [lorentz]
          fun_prop
        apply (hf.continuousAt (x := (0:ℝ))).tendsto.eventually_const_lt
        rw [hγ0, hlat]
        rcases hi with rfl | rfl <;> norm_num [Fin.ext_iff]
        · exact mul_pos (inv_pos.mpr hd) hApos
        · exact mul_pos (inv_pos.mpr hd) hCpos
      have hnear := htime.and (htrunc.and
        ((hlateral 0 (Or.inl rfl)).and (hlateral 1 (Or.inr rfl))))
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
      refine ⟨huN.1, huN.2, ε, hε, ?_⟩
      intro t ht
      have hdist : dist t (0:ℝ) < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact ht.2
      have h := hball hdist
      refine ⟨hγunit t, h.1, ?_, ?_⟩
      · intro i
        obtain ⟨j, rfl⟩ := e.surjective i
        have hCoeff : 0 < Real.sinh (t*μ)/μ :=
          div_pos (Real.sinh_pos_iff.mpr (mul_pos ht.1 hg.1)) hg.1
        fin_cases j
        · exact h.2.2.1.le
        · exact h.2.2.2.le
        · change 0 ≤ lorentz (normalGeodesic p u t) (dualVertex F (e 2))
          rw [active 2 (Or.inl rfl)]
          exact mul_nonneg hCoeff.le hu2
        · change 0 ≤ lorentz (normalGeodesic p u t) (dualVertex F (e 3))
          rw [active 3 (Or.inr rfl)]
          exact mul_nonneg hCoeff.le hu3
      · intro i
        obtain ⟨j, rfl⟩ := e.surjective i
        exact (h.2.1 j).le
  have signs₂ (u : Space) : 0 ≤ lorentz u (W 2) ↔ lorentz u n₂ ≤ 0 := by
    rw [hn₂]
    simp only [map_smul,smul_eq_mul]
    have hq := inv_pos.mpr hq₂
    constructor
    · intro h;exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) h
    · intro h
      by_contra hn
      have hx := lt_of_not_ge hn
      exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg (neg_neg_of_pos hq) hx)
  have signs₃ (u : Space) : 0 ≤ lorentz u (W 3) ↔ lorentz u n₃ ≤ 0 := by
    rw [hn₃]
    simp only [map_smul,smul_eq_mul]
    have hq := inv_pos.mpr hq₃
    constructor
    · intro h;exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) h
    · intro h
      by_contra hn
      have hx := lt_of_not_ge hn
      exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg (neg_neg_of_pos hq) hx)
  have forward_rays (u : Space) : u ∈ forwardNormalSet F e s ↔
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ u=α • r₂+β • r₃ := by
    rw [forward_halfspaces]
    simpa only [← hW,signs₂,signs₃] using rays_span u
  let G : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
    lorentz (vertex F (e i)) (vertex F (e j))
  let M : Matrix (Fin 4) (Fin 4) ℝ := fun i j => lorentz (W i) (W j)
  have hGM : G*M=1 := by
    ext i j
    rw [Matrix.mul_apply]
    change (∑ k : Fin 4, lorentz (vertex F (e i)) (vertex F (e k)) *
      lorentz (W k) (W j)) = if i=j then 1 else 0
    calc
      _ = lorentz (∑ k : Fin 4, W.repr (vertex F (e i)) k • W k) (W j) := by
        simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [← wcoord, sym (vertex F (e k)) (vertex F (e i))]
      _ = _ := by rw [W.sum_repr,hW,dual];simp only [Equiv.apply_eq_iff_eq]
  have hdetne : G.det ≠ 0 := by
    have h := congrArg Matrix.det hGM
    rw [Matrix.det_mul,Matrix.det_one] at h
    intro he
    rw [he,zero_mul] at h
    norm_num at h
  let C : Matrix (Fin 4) (Fin 4) ℝ := fun i =>
    ![(vertex F (e i)).1,(vertex F (e i)).2 0,
      (vertex F (e i)).2 1,(vertex F (e i)).2 2]
  let J : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1,1,1,1]
  have hgramFactor : G=C*J*C.transpose := by
    ext i j
    change lorentz (vertex F (e i)) (vertex F (e j)) = ((C*J)*C.transpose) i j
    rw [Matrix.mul_apply]
    dsimp [J]
    simp only [Matrix.mul_diagonal,Matrix.transpose_apply,Fin.sum_univ_four]
    change -(vertex F (e i)).1*(vertex F (e j)).1 +
      inner ℝ (vertex F (e i)).2 (vertex F (e j)).2 =
      ((vertex F (e i)).1 * (-1))*(vertex F (e j)).1 +
      ((vertex F (e i)).2 0 * 1)*(vertex F (e j)).2 0 +
      ((vertex F (e i)).2 1 * 1)*(vertex F (e j)).2 1 +
      ((vertex F (e i)).2 2 * 1)*(vertex F (e j)).2 2
    rw [PiLp.inner_apply,Fin.sum_univ_three]
    simp only [Real.inner_apply]
    ring
  have hdetJ : J.det= -1 := by
    dsimp [J]
    rw [Matrix.det_diagonal,Fin.prod_univ_four]
    change (-1:ℝ)*1*1*1= -1
    norm_num
  have hdetFactor : G.det= -(C.det)^2 := by
    rw [hgramFactor,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hdetJ]
    ring
  let D := -G.det
  have hD : 0 < D := by
    have hCne : C.det ≠ 0 := by
      intro h
      apply hdetne
      simp only [hdetFactor,h,pow_two,mul_zero,neg_zero]
    dsimp [D]
    rw [hdetFactor,neg_neg]
    exact sq_pos_of_ne_zero hCne
  have hadj : G.adjugate=G.det • M := by
    calc
      G.adjugate = G.adjugate*(G*M) := by rw [hGM,Matrix.mul_one]
      _ = (G.adjugate*G)*M := (Matrix.mul_assoc _ _ _).symm
      _ = (G.det • (1:Matrix (Fin 4) (Fin 4) ℝ))*M := by rw [Matrix.adjugate_mul]
      _ = _ := by rw [Matrix.smul_mul,Matrix.one_mul]
  let x := F.lengths (e 0) (e 1)
  let y := F.lengths (e 0) (e 2)
  let z := F.lengths (e 0) (e 3)
  let o := F.lengths (e 2) (e 3)
  let v := F.lengths (e 1) (e 3)
  let w := F.lengths (e 1) (e 2)
  have lsym (i j : Fin 4) : F.lengths i j=F.lengths j i := by
    by_cases hij : i=j
    · subst j;rfl
    have he : -F.lengths i j = -F.lengths j i := by
      have he := sym (vertex F i) (vertex F j)
      simpa only [gram,if_neg hij,if_neg (Ne.symm hij)] using he
    linarith only [he]
  have hG : G= !![1,-x,-y,-z; -x,1,-w,-v; -y,-w,1,-o; -z,-v,-o,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [G,gram,Equiv.apply_eq_iff_eq,Fin.ext_iff,x,y,z,o,v,w,
        lsym (e 1) (e 0),lsym (e 2) (e 0),lsym (e 3) (e 0),
        lsym (e 2) (e 1),lsym (e 3) (e 1),lsym (e 3) (e 2)]
  let A₀ := FourCycleEnvelopes.rad x y w
  let B₀ := FourCycleEnvelopes.rad x z v
  let P₀ := FourCycleEnvelopes.numerator x y z o v w
  have hco₂ : G.adjugate 2 2= -B₀ := by
    rw [hG,Matrix.adjugate_fin_succ_eq_det_submatrix,Matrix.det_fin_three]
    change (-1:ℝ)^4*(1*1*1-1*(-v)*(-v)-(-x)*(-x)*1+(-x)*(-v)*(-z)+(-z)*(-x)*(-v)-(-z)*1*(-z))= -B₀
    dsimp [B₀,FourCycleEnvelopes.rad]
    ring
  have hco₃ : G.adjugate 3 3= -A₀ := by
    rw [hG,Matrix.adjugate_fin_succ_eq_det_submatrix,Matrix.det_fin_three]
    change (-1:ℝ)^6*(1*1*1-1*(-w)*(-w)-(-x)*(-x)*1+(-x)*(-w)*(-y)+(-y)*(-x)*(-w)-(-y)*1*(-y))= -A₀
    dsimp [A₀,FourCycleEnvelopes.rad]
    ring
  have hco₂₃ : G.adjugate 2 3=P₀ := by
    rw [hG,Matrix.adjugate_fin_succ_eq_det_submatrix,Matrix.det_fin_three]
    change (-1:ℝ)^5*(1*1*(-o)-1*(-v)*(-w)-(-x)*(-x)*(-o)+(-x)*(-v)*(-y)+(-z)*(-x)*(-w)-(-z)*1*(-y))=P₀
    dsimp [P₀,FourCycleEnvelopes.numerator]
    ring
  have hpolynomial : A₀*B₀-P₀^2=(x^2-1)*D := by
    dsimp [D]
    rw [hG,Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four,Matrix.det_fin_three]
    change A₀*B₀-P₀^2=(x^2-1)*(-((-1:ℝ)^0*1*(1*1*1-1*(-o)*(-o)-(-w)*(-w)*1+(-w)*(-o)*(-v)+(-v)*(-w)*(-o)-(-v)*1*(-v)) + (-1:ℝ)^1*(-x)*((-x)*1*1-(-x)*(-o)*(-o)-(-w)*(-y)*1+(-w)*(-o)*(-z)+(-v)*(-y)*(-o)-(-v)*1*(-z)) + (-1:ℝ)^2*(-y)*((-x)*(-w)*1-(-x)*(-o)*(-v)-1*(-y)*1+1*(-o)*(-z)+(-v)*(-y)*(-v)-(-v)*(-w)*(-z)) + (-1:ℝ)^3*(-z)*((-x)*(-w)*(-o)-(-x)*1*(-v)-1*(-y)*(-o)+1*1*(-z)+(-w)*(-y)*(-v)-(-w)*(-w)*(-z))))
    dsimp [A₀,B₀,P₀,FourCycleEnvelopes.rad,FourCycleEnvelopes.numerator]
    ring
  have hw₂ : lorentz (W 2) (W 2)=B₀/D := by
    have he := congrArg (fun Q : Matrix (Fin 4) (Fin 4) ℝ => Q 2 2) hadj
    simp only [hco₂,Pi.smul_apply,smul_eq_mul] at he
    apply (eq_div_iff hD.ne').mpr
    change -B₀=G.det*lorentz (W 2) (W 2) at he
    dsimp only [D]
    nlinarith only [he]
  have hw₃ : lorentz (W 3) (W 3)=A₀/D := by
    have he := congrArg (fun Q : Matrix (Fin 4) (Fin 4) ℝ => Q 3 3) hadj
    simp only [hco₃,Pi.smul_apply,smul_eq_mul] at he
    apply (eq_div_iff hD.ne').mpr
    change -A₀=G.det*lorentz (W 3) (W 3) at he
    dsimp only [D]
    nlinarith only [he]
  have hw₂₃ : lorentz (W 2) (W 3)= -P₀/D := by
    have he := congrArg (fun Q : Matrix (Fin 4) (Fin 4) ℝ => Q 2 3) hadj
    simp only [hco₂₃,Pi.smul_apply,smul_eq_mul] at he
    apply (eq_div_iff hD.ne').mpr
    change P₀=G.det*lorentz (W 2) (W 3) at he
    dsimp only [D]
    nlinarith only [he]
  have hA₀ : 0 < A₀ := by
    have he := hw₃
    have hp := hwwpos 3 (Or.inr rfl)
    rw [he] at hp
    exact (div_pos_iff.mp hp).resolve_right (by intro h;linarith [h.2]) |>.1
  have hB₀ : 0 < B₀ := by
    have he := hw₂
    have hp := hwwpos 2 (Or.inl rfl)
    rw [he] at hp
    exact (div_pos_iff.mp hp).resolve_right (by intro h;linarith [h.2]) |>.1
  have hqproduct : q₂*q₃=Real.sqrt B₀*Real.sqrt A₀/D := by
    dsimp [q₂,q₃]
    rw [hw₂,hw₃,Real.sqrt_div hB₀.le,Real.sqrt_div hA₀.le]
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hD.le]
  have hnormalproduct : lorentz n₂ n₃ = lorentz (W 2) (W 3)/(q₂*q₃) := by
    rw [hn₂,hn₃]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hcosine : -c=FourCycleEnvelopes.cosine x y z o v w := by
    change -lorentz n₂ n₃ = _
    rw [hnormalproduct,hw₂₃,hqproduct]
    unfold FourCycleEnvelopes.cosine
    change -((-P₀/D)/(Real.sqrt B₀*Real.sqrt A₀/D)) =
      P₀/Real.sqrt A₀/Real.sqrt B₀
    field_simp [hD.ne',(Real.sqrt_pos.mpr hA₀).ne',(Real.sqrt_pos.mpr hB₀).ne'] <;> ring
  have hangle : tangentAngle p hpunit ⟨r₂,hr₂N.1⟩ ⟨r₃,hr₃N.1⟩ = Real.arccos (-c) := by
    letI : InnerProductSpace.Core ℝ (Tangent p) := tangentCore p hpunit
    letI : NormedAddCommGroup (Tangent p) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
    letI : InnerProductSpace ℝ (Tangent p) :=
      InnerProductSpace.ofCore (tangentCore p hpunit).toCore
    let u₂ : Tangent p := ⟨r₂,hr₂N.1⟩
    let u₃ : Tangent p := ⟨r₃,hr₃N.1⟩
    have hn₂ : ‖u₂‖=1 := by
      change Real.sqrt (lorentz r₂ r₂)=1
      rw [hr₂unit]
      norm_num
    have hn₃ : ‖u₃‖=1 := by
      change Real.sqrt (lorentz r₃ r₃)=1
      rw [hr₃unit]
      norm_num
    change InnerProductGeometry.angle u₂ u₃ = _
    unfold InnerProductGeometry.angle
    rw [hn₂,hn₃,one_mul,div_one]
    exact congrArg Real.arccos hr₂₃
  have hangleSource : tangentAngle p hpunit ⟨r₂,hr₂N.1⟩ ⟨r₃,hr₃N.1⟩ =
      Real.arccos (FourCycleEnvelopes.cosine x y z o v w) := by
    rw [hcosine] at hangle
    exact hangle
  have hcofactorBundle : 0 < D ∧ D=C.det^2 ∧
      lorentz (dualVertex F (e 2)) (dualVertex F (e 2))=B₀/D ∧
      lorentz (dualVertex F (e 3)) (dualVertex F (e 3))=A₀/D ∧
      lorentz (dualVertex F (e 2)) (dualVertex F (e 3))= -P₀/D ∧
      A₀*B₀-P₀^2=(x^2-1)*D := by
    refine ⟨hD,?_,?_,?_,?_,hpolynomial⟩
    · dsimp [D];rw [hdetFactor,neg_neg]
    · simpa only [hW] using hw₂
    · simpa only [hW] using hw₃
    · simpa only [hW] using hw₂₃
  have hmetric (q u : Space) (hqq : lorentz q q = -1) (hqu : lorentz q u = 0) :
      inner ℝ u.2 u.2 ≤ q.1^2 * lorentz u u ∧ (lorentz u u=0 ↔ u=0) := by
    have hcs := real_inner_mul_inner_self_le q.2 u.2
    change -q.1*q.1+inner ℝ q.2 q.2 = -1 at hqq
    change -q.1*u.1+inner ℝ q.2 u.2 = 0 at hqu
    have heq : inner ℝ q.2 u.2=q.1*u.1 := by linarith only [hqu]
    have hpEq : inner ℝ q.2 q.2=q.1^2-1 := by nlinarith only [hqq]
    rw [heq,hpEq] at hcs
    constructor
    · change inner ℝ u.2 u.2 ≤ q.1^2 * (-u.1*u.1+inner ℝ u.2 u.2)
      nlinarith only [hcs]
    · constructor
      · intro h
        exact congrArg Subtype.val ((tangentCore q (by exact hqq)).definite
          (⟨u,by change -q.1*u.1+inner ℝ q.2 u.2=0;exact hqu⟩ : Tangent q) h)
      · rintro rfl;simp
  have hderivative : HasDerivAt (edgePoint F e) (edgeVelocity F e s) s := by
    have h := (((Real.hasDerivAt_cosh (L-s)).comp s
      ((hasDerivAt_const s L).sub (hasDerivAt_id s))).smul_const (vertex F (e 0))).add
      ((Real.hasDerivAt_cosh s).smul_const (vertex F (e 1)))
    have h := h.const_smul d⁻¹
    change HasDerivAt (fun t => d⁻¹ •
      (Real.cosh (L-t) • vertex F (e 0)+Real.cosh t • vertex F (e 1)))
      (d⁻¹ • (-Real.sinh (L-s) • vertex F (e 0)+Real.sinh s • vertex F (e 1))) s
    convert h using 1 <;> (try simp only [zero_sub,mul_neg,mul_one,Function.comp_def]) <;>
      first | rfl | (funext t; rfl)
  have htrComplement (i : Fin 4) (hi : i=2 ∨ i=3) :
      lorentz p (vertex F (e i)) =
        -(F.lengths (e 0) (e i)*A+F.lengths (e 1) (e i)*Real.cosh s)/d := by
    have hi0 : i≠0 := by rcases hi with rfl|rfl <;> decide
    have hi1 : i≠1 := by rcases hi with rfl|rfl <;> decide
    rw [hpformula]
    simp only [map_smul,map_add,LinearMap.smul_apply,LinearMap.add_apply,
      smul_eq_mul,gram,Equiv.apply_eq_iff_eq,if_neg (Ne.symm hi0),if_neg (Ne.symm hi1)]
    ring
  have hhalfspaceNormals (u : Space) : u ∈ forwardNormalSet F e s ↔
      u ∈ normalSpace F e s ∧ lorentz u n₂ ≤ 0 ∧ lorentz u n₃ ≤ 0 := by
    rw [forward_halfspaces,← hW 2,← hW 3,signs₂,signs₃]
  have hraysSource : lorentz r₂ r₃ = FourCycleEnvelopes.cosine x y z o v w := by
    rw [hr₂₃,hcosine]
  exact ⟨hpK,hvunit,hpv,by simpa only [hW] using normal_decompose,
    hnormalrank,forward_rays,hr₂unit,hr₃unit,hcpos,hcofactorBundle,
    hmetric,hderivative,⟨hlat,htr0,htr1,htr,htrComplement⟩,hhalfspaceNormals,hraysSource,
    hpunit,hr₂N.1,hr₃N.1,hangleSource⟩

#print axioms polar_edge_forward_sector

end D5.S3.Geometry.Hyperideal.PolarNormalSector
