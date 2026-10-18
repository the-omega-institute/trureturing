import D5.S3.Geometry.Hyperideal.CFMPNativeCapMetricTransient
import D5.S3.Geometry.HyperbolicPlaneRealization
import Batteries.Tactic.OpenPrivate

/-! UNCOMPILED transient source-only incremental extension of inverse.lean.
Zero canonical Lean retention. No compilation, kernel proof or benchmark result.
Original suffix statements and mathematical proof obligations are preserved.
Cumulative-file comments refer to the supplied packet; inherited declarations
are supplied by imports here. Any original retention commentary is superseded
by this attempt's zero-retention constraint. -/

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

namespace NativeCornerExtractionSource
open private B_apply B_symm lift_ne_zero cap_zero_iff cap_strict side_strict
  from D5.S3.Geometry.Hyperideal.CFMPNativeCapMetricTransient

/-! Source-only application bridge. This anonymous, bind-only consumer and all
of its local bindings are transient: zero new named API is proposed for
retention. The inherited carrier and this extension are UNCOMPILED.
The cap vectors are rows; coefficients range over all of `Fin 4 → ℝ`.
No claim about the sign of the cap determinant is made. -/

private theorem temporary_dual_support_conclusion (d : NativeSupportCorners) :
    (lengthGram (actualLengths d)).det < 0 ∧
    (∀ i, B (d.cap i) (d.side i) < 0) ∧
    ∀ a : Fin 4 → ℝ,
      (∀ i, B (d.cap i) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) =
        ((lengthGram (actualLengths d)) *ᵥ a) i) ∧
      (∀ i, B (d.side i) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) =
        B (d.cap i) (d.side i) * a i) ∧
      (((∀ i, B (d.cap i) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) ≤ 0) ∧
        (∀ i, B (d.side i) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) ≤ 0)) ↔
       ((∀ i, 0 ≤ a i) ∧
        (∀ i, ((lengthGram (actualLengths d)) *ᵥ a) i ≤ 0))) := by
  -- Bind-only determinant reuse: det G = -(det C)^2, with det C nonzero.
  have hdet : (lengthGram (actualLengths d)).det < 0 := by
    have hJ : J.det = -1 := by
      norm_num [J, Matrix.det_diagonal, Fin.prod_univ_succ]
    have hC := actual_corner_cap_det_ne_zero d
    have hsq : 0 < (Matrix.of d.cap).det ^ 2 :=
      sq_pos_of_ne_zero hC
    rw [← actual_corner_cap_matrix d, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, hJ]
    nlinarith only [hsq]
  -- Bind-only inversion and strict support evaluation at an original corner.
  have hbeta (i : Fin 4) : B (d.cap i) (d.side i) < 0 := by
    let j : Fin 4 := if i = 0 then 1 else 0
    have hij : i ≠ j := by
      dsimp [j]
      split_ifs with hi
      · subst i; decide
      · exact hi
    let X := lift (d.corner i j)
    let Y := lift (d.corner j i)
    let c := Real.cosh (dist (d.corner i j) (d.corner j i))
    let s := Real.sqrt (c ^ 2 - 1)
    obtain ⟨hc, hs, hi, hj⟩ := actual_corner_oriented_caps d i j hij
    change 1 < c at hc
    change 0 < s at hs
    change d.cap i = (c / s) • X - (1 / s) • Y at hi
    change d.cap j = (c / s) • Y - (1 / s) • X at hj
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hz : 0 < c ^ 2 - 1 := by nlinarith only [hc]
    have hs2 : s ^ 2 = c ^ 2 - 1 := Real.sq_sqrt hz.le
    have hquot : (c ^ 2 - 1) / s = s := by
      apply (div_eq_iff hs0).mpr
      nlinarith only [hs2]
    have hinv : s • Y = d.cap i + c • d.cap j := by
      rw [hi, hj]
      funext k
      change s * Y k =
        ((c / s) * X k - (1 / s) * Y k) +
          c * ((c / s) * Y k - (1 / s) * X k)
      calc
        s * Y k = ((c ^ 2 - 1) / s) * Y k := by rw [hquot]
        _ = _ := by ring
    have horth : B (d.side i) (d.cap j) = 0 :=
      (B_symm _ _).trans (d.orthogonal_incidence j i hij.symm)
    have hpair : s * B (d.side i) Y = B (d.cap i) (d.side i) := by
      calc
        s * B (d.side i) Y = B (d.side i) (s • Y) := by
          simp [B_apply, lorentz, Fin.sum_univ_succ]
          <;> ring
        _ = B (d.side i) (d.cap i) + c * B (d.side i) (d.cap j) := by
          rw [hinv]
          simp [B_apply, lorentz, Fin.sum_univ_succ]
          <;> ring
        _ = B (d.cap i) (d.side i) := by
          rw [horth, B_symm (d.side i) (d.cap i)]
          ring
    have hquotient : B (d.side i) Y = B (d.cap i) (d.side i) / s := by
      apply (eq_div_iff hs0).mpr
      nlinarith only [hpair]
    have hstrict : B (d.side i) Y < 0 :=
      side_strict d j i i hij.symm (by simp)
    rw [hquotient] at hstrict
    simpa only [zero_mul] using (div_lt_iff₀ hs).mp hstrict
  -- Bind-only finite bilinear expansion, with no sum-map API assumptions.
  have hexpand (u : V) (a : Fin 4 → ℝ) :
      B u (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) =
        ∑ j, a j * B u (d.cap j) := by
    simp [B_apply, lorentz, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    <;> ring
  have hcap (a : Fin 4 → ℝ) (i : Fin 4) :
      B (d.cap i) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) =
        ((lengthGram (actualLengths d)) *ᵥ a) i := by
    have hentry (j : Fin 4) :
        B (d.cap i) (d.cap j) = lengthGram (actualLengths d) i j :=
      congrFun (congrFun (actual_corner_cap_gram_entries d) i) j
    rw [hexpand]
    simp only [hentry, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hside (a : Fin 4 → ℝ) (i : Fin 4) :
      B (d.side i) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) =
        B (d.cap i) (d.side i) * a i := by
    have hrow (j : Fin 4) : B (d.side i) (d.cap j) =
        if j = i then B (d.cap i) (d.side i) else 0 := by
      by_cases hji : j = i
      · subst j
        simpa only [if_pos rfl, ite_true] using B_symm (d.side i) (d.cap i)
      · rw [if_neg hji, B_symm, d.orthogonal_incidence j i hji]
    rw [hexpand]
    simp [hrow, mul_comm]
  refine ⟨hdet, hbeta, ?_⟩
  intro a
  refine ⟨hcap a, hside a, ?_⟩
  constructor
  · rintro ⟨hcap_le, hside_le⟩
    constructor
    · intro i
      have hle := hside_le i
      rw [hside a i] at hle
      by_contra hn
      have ha : a i < 0 := lt_of_not_ge hn
      have hp := mul_pos_of_neg_of_neg (hbeta i) ha
      linarith only [hle, hp]
    · intro i
      rw [← hcap a i]
      exact hcap_le i
  · rintro ⟨ha, hGa⟩
    constructor
    · intro i
      rw [hcap a i]
      exact hGa i
    · intro i
      rw [hside a i]
      exact mul_nonpos_of_nonpos_of_nonneg (hbeta i).le (ha i)

/-! Transient source-only future-sheet bridge. All new declarations, including
bind-only local helpers, have zero retention. The inherited carrier and this
extension are uncompiled; no validity or full-geometry claim is made. -/
namespace NativeFutureSheet

/-- Temporary exact binding of the native cap rows to the shared radial unit
identity and the public future-pair criterion, using the actual corner 01. -/
private theorem actual_radial_norm_pair_future (d : NativeSupportCorners)
    (v : Fin 4 → ℝ) (hv : v ∈ cutBody (actualLengths d)) :
    let l := actualLengths d
    let C : Matrix (Fin 4) (Fin 4) ℝ := d.cap
    let Y := (radial l v) ᵥ* C
    lorentz Y Y = -1 ∧
      B (lift (d.corner 0 1)) Y < 0 ∧ 0 < Y 3 := by
  classical
  let l := actualLengths d
  let C : Matrix (Fin 4) (Fin 4) ℝ := d.cap
  let Y := (radial l v) ᵥ* C
  change lorentz Y Y = -1 ∧
    B (lift (d.corner 0 1)) Y < 0 ∧ 0 < Y 3
  obtain ⟨_, _, _, hnegative, _, _, _, _, hnormalized, _⟩ :=
    shared_radial_body l (actualLengths_positive d)
  have hq : gramQuadratic l v < 0 := hnegative v hv
  have hunit : gramQuadratic l (radial l v) = -1 := hnormalized v hv
  have hentry (i j : Fin 4) : B (d.cap i) (d.cap j) = lengthGram l i j :=
    congrFun (congrFun (actual_corner_cap_gram_entries d) i) j
  have hnorm : lorentz Y Y = -1 := by
    calc
      lorentz Y Y =
          ∑ i, radial l v i * ∑ j, B (d.cap i) (d.cap j) * radial l v j := by
        -- Only the finite row-congruence normalization for these actual rows.
        simp [Y, C, B_apply, lorentz, Matrix.vecMul, dotProduct,
          Fin.sum_univ_succ] <;> ring
      _ = gramQuadratic l (radial l v) := by
        simp only [hentry]
        rfl
      _ = -1 := hunit
  have hsqrt : 0 < Real.sqrt (-gramQuadratic l v) :=
    Real.sqrt_pos.mpr (neg_pos.mpr hq)
  have hrnonneg (i : Fin 4) : 0 ≤ radial l v i :=
    div_nonneg (hv.1.1 i) hsqrt.le
  have hpositive : ∃ r : Fin 4, r ≠ 0 ∧ 0 < v r := by
    by_contra hn
    push_neg at hn
    have hzero (r : Fin 4) (hr : r ≠ 0) : v r = 0 :=
      le_antisymm (hn r hr) (hv.1.1 r)
    have hqzero : gramQuadratic l v = v 0 * v 0 := by
      simp [gramQuadratic, lengthGram, Fin.sum_univ_succ,
        hzero 1 (by decide), hzero 2 (by decide), hzero 3 (by decide)]
    have hnonneg : 0 ≤ gramQuadratic l v := by
      rw [hqzero]
      exact mul_self_nonneg (v 0)
    exact (not_lt_of_ge hnonneg) hq
  have hcapzero : B (d.cap 0) (lift (d.corner 0 1)) = 0 :=
    (cap_zero_iff d 0 1 0 (by decide)).mpr rfl
  have hcapnonpos (i : Fin 4) : B (d.cap i) (lift (d.corner 0 1)) ≤ 0 := by
    by_cases hi : i = 0
    · subst i
      exact le_of_eq hcapzero
    · exact (cap_strict d 0 1 i (by decide) hi).le
  have hpair : B (lift (d.corner 0 1)) Y < 0 := by
    have hexpand : B (lift (d.corner 0 1)) Y =
        ∑ i, radial l v i * B (d.cap i) (lift (d.corner 0 1)) := by
      rw [B_symm (lift (d.corner 0 1)) Y]
      simp [Y, C, B_apply, lorentz, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ] <;> ring
    have hsum :
        (∑ i, radial l v i * B (d.cap i) (lift (d.corner 0 1))) <
          ∑ _i : Fin 4, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact mul_nonpos_of_nonneg_of_nonpos (hrnonneg i) (hcapnonpos i)
      · obtain ⟨r, hr, hvr⟩ := hpositive
        have hradial : 0 < radial l v r := div_pos hvr hsqrt
        exact ⟨r, Finset.mem_univ r,
          mul_neg_of_pos_of_neg hradial (cap_strict d 0 1 r (by decide) hr)⟩
    rw [hexpand]
    simpa only [Finset.sum_const_zero] using hsum
  have hfuture : 0 < Y 3 :=
    D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair
      (lift (d.corner 0 1)) Y (lift_unit (d.corner 0 1)) hnorm
      (lift_time (d.corner 0 1)) (by simpa only [B_apply] using hpair)
  exact ⟨hnorm, hpair, hfuture⟩

end NativeFutureSheet


/-! Transient same-object consumer. The only input is the original native
support/corner data. All bindings below have zero repository retention.
No determinant orientation, changed cap frame, or geometric premise is added.
This entire assembled file is source-only and UNCOMPILED. -/
namespace NativeFutureSheet

/-- Exact native radial range, injectivity, and the coefficient-sum inverse.
The final inverse identities use the original set `d.P`, not a replacement body. -/
theorem native_body_exact_inverse (d : NativeSupportCorners) :
    let l := actualLengths d
    let C : Matrix (Fin 4) (Fin 4) ℝ := d.cap
    ∃ F : cutBody l → HyperbolicThreeSpace,
      (∀ v, lift (F v) = (radial l v.val) ᵥ* C) ∧
      Set.range F = d.P ∧ Function.Injective F ∧
      ∃ I : d.P → cutBody l,
        (∀ p, let a := (lift p.val) ᵥ* C⁻¹
          let s := ∑ i, a i
          0 < s ∧ (I p).val = (fun i => a i / s) ∧
            gramQuadratic l a = -1 ∧
            gramQuadratic l (I p).val = -1 / s ^ 2 ∧
            Real.sqrt (-gramQuadratic l (I p).val) = 1 / s ∧
            radial l (I p).val = a) ∧
        (∀ p, F (I p) = p.val) ∧
        (∀ v (hp : F v ∈ d.P), I ⟨F v, hp⟩ = v) := by
  classical
  -- Introduce the statement's exact let bindings without repeating its telescope.
  intro l C
  -- Consume exactly the supplied dual conclusion. Its strict Gram determinant
  -- conclusion is not an orientation assumption on the native row matrix C.
  obtain ⟨_, _, hsupport⟩ := temporary_dual_support_conclusion d
  have hdet : C.det ≠ 0 := actual_corner_cap_det_ne_zero d
  have hdetUnit : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet
  have hCunit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hdetUnit
  let Cinv : Matrix (Fin 4) (Fin 4) ℝ := C⁻¹
  let coeff : HyperbolicThreeSpace → V := fun p => (lift p) ᵥ* Cinv
  have hundo (X : V) : (X ᵥ* Cinv) ᵥ* C = X := by
    change (X ᵥ* C⁻¹) ᵥ* C = X
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul C hdetUnit,
      Matrix.vecMul_one]
  have hrows_div (a : V) (s : ℝ) (i : Fin 4) :
      (∑ j, lengthGram l i j * (a j / s)) =
        (∑ j, lengthGram l i j * a j) / s := by
    simp only [mul_div_assoc, Finset.sum_div]
  -- This is the native row-Gram pullback, using the supplied exact cap pairing.
  have hpull (a : V) : lorentz (a ᵥ* C) (a ᵥ* C) = gramQuadratic l a := by
    calc
      lorentz (a ᵥ* C) (a ᵥ* C) =
          ∑ i, a i * B (d.cap i) (a ᵥ* C) := by
        simp [C, B_apply, lorentz, Matrix.vecMul, dotProduct,
          Fin.sum_univ_succ] <;> ring
      _ = ∑ i, a i * ((lengthGram l) *ᵥ a) i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(hsupport a).1 i]
      _ = gramQuadratic l a := rfl
  let F : cutBody l → HyperbolicThreeSpace := fun v =>
    project ((radial l v.val) ᵥ* C)
      (actual_radial_norm_pair_future d v.val v.property).1
      (actual_radial_norm_pair_future d v.val v.property).2.2
  have hlift (v : cutBody l) : lift (F v) = (radial l v.val) ᵥ* C :=
    lift_of_coordinates _ _
      (actual_radial_norm_pair_future d v.val v.property).1
      (actual_radial_norm_pair_future d v.val v.property).2.2 rfl
  have hmem (v : cutBody l) : F v ∈ d.P := by
    rw [d.body_halfspaces]
    change (∀ i, B (d.cap i) (lift (F v)) ≤ 0) ∧
      (∀ i, B (d.side i) (lift (F v)) ≤ 0)
    rw [hlift]
    apply ((hsupport (radial l v.val)).2.2).mpr
    constructor
    · intro i
      exact div_nonneg (v.property.1.1 i) (Real.sqrt_nonneg _)
    · intro i
      change (∑ j, lengthGram l i j *
        (v.val j / Real.sqrt (-gramQuadratic l v.val))) ≤ 0
      rw [hrows_div]
      exact div_nonpos_of_nonpos_of_nonneg (v.property.2 i) (Real.sqrt_nonneg _)
  have hfinj : Function.Injective F := by
    intro v w heq
    have hY : (radial l v.val) ᵥ* C = (radial l w.val) ᵥ* C := by
      rw [← hlift, ← hlift, heq]
    have hr := Matrix.vecMul_injective_of_isUnit hCunit hY
    obtain ⟨_, _, _, _, _, hinj, _, _, _, _⟩ :=
      shared_radial_body l (actualLengths_positive d)
    apply Subtype.ext
    exact hinj v.property w.property hr
  -- Inverse preparation is pointwise in the SAME original eight-halfspace body.
  have hdata (p : HyperbolicThreeSpace) (hp : p ∈ d.P) :
      let a : V := coeff p
      let s : ℝ := ∑ i, a i
      0 < s ∧ (fun i => a i / s) ∈ cutBody l ∧
        gramQuadratic l a = -1 ∧
        gramQuadratic l (fun i => a i / s) = -1 / s ^ 2 ∧
        Real.sqrt (-gramQuadratic l (fun i => a i / s)) = 1 / s ∧
        radial l (fun i => a i / s) = a := by
    intro a s
    have haC : a ᵥ* C = lift p := hundo (lift p)
    have ha : (∀ i, 0 ≤ a i) ∧ (∀ i, ((lengthGram l) *ᵥ a) i ≤ 0) := by
      apply ((hsupport a).2.2).mp
      change (∀ i, B (d.cap i) (a ᵥ* C) ≤ 0) ∧
        (∀ i, B (d.side i) (a ᵥ* C) ≤ 0)
      rw [haC]
      simpa only [d.body_halfspaces, Set.mem_setOf_eq] using hp
    have hane : a ≠ 0 := by
      intro hz
      apply lift_ne_zero p
      rw [← haC, hz]
      simp [Matrix.vecMul, dotProduct]
    have hapos : ∃ i, 0 < a i := by
      by_contra hn
      push_neg at hn
      apply hane
      funext i
      exact le_antisymm (hn i) (ha.1 i)
    have hs : 0 < s := by
      obtain ⟨i, hi⟩ := hapos
      exact lt_of_lt_of_le hi
        (Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i))
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hv : (fun i => a i / s) ∈ cutBody l := by
      refine ⟨⟨fun i => div_nonneg (ha.1 i) hs.le, ?_⟩, ?_⟩
      · rw [← Finset.sum_div]
        change s / s = 1
        exact div_self hs0
      · intro i
        rw [hrows_div]
        exact div_nonpos_of_nonpos_of_nonneg (ha.2 i) hs.le
    have hqa : gramQuadratic l a = -1 := by
      rw [← hpull, haC]
      exact lift_unit p
    have hqv : gramQuadratic l (fun i => a i / s) = -1 / s ^ 2 := by
      calc
        gramQuadratic l (fun i => a i / s) = gramQuadratic l a / s ^ 2 := by
          change (∑ i, (a i / s) * ∑ j, lengthGram l i j * (a j / s)) =
            (∑ i, a i * ∑ j, lengthGram l i j * a j) / s ^ 2
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          rw [hrows_div]
          ring
        _ = -1 / s ^ 2 := by rw [hqa]
    have hroot : Real.sqrt (-gramQuadratic l (fun i => a i / s)) = 1 / s := by
      have harg : -gramQuadratic l (fun i => a i / s) = (1 / s) ^ 2 := by
        rw [hqv]
        ring
      rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hs)]
    have hradial : radial l (fun i => a i / s) = a := by
      funext i
      change (a i / s) / Real.sqrt (-gramQuadratic l (fun j => a j / s)) = a i
      rw [hroot]
      field_simp [hs0]
    exact ⟨hs, hv, hqa, hqv, hroot, hradial⟩
  let I : d.P → cutBody l := fun p =>
    ⟨(fun i => coeff p.val i / ∑ j, coeff p.val j),
      (hdata p.val p.property).2.1⟩
  have hright (p : d.P) : F (I p) = p.val := by
    apply lift_injective
    rw [hlift]
    change (radial l (fun i => coeff p.val i /
      ∑ j, coeff p.val j)) ᵥ* C = lift p.val
    rw [(hdata p.val p.property).2.2.2.2.2]
    exact hundo (lift p.val)
  have hrange : Set.range F = d.P := by
    apply Set.ext
    intro p
    constructor
    · rintro ⟨v, rfl⟩
      exact hmem v
    · intro hp
      exact ⟨I ⟨p, hp⟩, hright ⟨p, hp⟩⟩
  refine ⟨F, hlift, hrange, hfinj, I, ?_, hright, ?_⟩
  · intro p
    have hd := hdata p.val p.property
    exact ⟨hd.1, rfl, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1,
      hd.2.2.2.2.2⟩
  · intro v hp
    apply hfinj
    exact hright ⟨F v, hp⟩

end NativeFutureSheet
end NativeCornerExtractionSource

#check NativeCornerExtractionSource.NativeFutureSheet.native_body_exact_inverse
#print axioms NativeCornerExtractionSource.NativeFutureSheet.native_body_exact_inverse
