/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-floor-selection)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact floor budget for the uniform last-U physical mask selection. -/
import Mathlib.Data.Int.DivMod
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source

/-! The floor is chosen by the actual remaining old mass and the actual X coefficient. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open private seed eta vcoef wcoef xcoef
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source

private def budgetPoly (R D : ℤ) : ℤ :=
  D * (seed R - 1 - 4 * xcoef R D - 2) * xcoef R D -
    D * eta R * (D * R * R * R - 1 - vcoef R D) +
    (D * R - 2 * R) * (eta R * wcoef R D - (R + 1) * xcoef R D)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private theorem budget_positive (R D : ℤ) (hR : D * D ≤ R)
    (hbig : 8 ≤ D ∨ D = 4 ∧ 64 ≤ R) : 0 ≤ budgetPoly R D := by
  rcases hbig with hD | ⟨rfl, h64⟩
  · let e := D - 8
    let t := R - D * D
    have he : 0 ≤ e := by dsimp [e]; omega
    have ht : 0 ≤ t := by dsimp [t]; omega
    have hp : 0 ≤
      1 * e ^ 12 +
      91 * e ^ 11 +
      5 * e ^ 10 * t +
      3778 * e ^ 10 +
      379 * e ^ 9 * t +
      10 * e ^ 8 * t ^ 2 +
      94556 * e ^ 9 +
      12864 * e ^ 8 * t +
      606 * e ^ 7 * t ^ 2 +
      10 * e ^ 6 * t ^ 3 +
      1587547 * e ^ 8 +
      257264 * e ^ 7 * t +
      15980 * e ^ 6 * t ^ 2 +
      454 * e ^ 5 * t ^ 3 +
      5 * e ^ 4 * t ^ 4 +
      18815673 * e ^ 7 +
      3353713 * e ^ 6 * t +
      239272 * e ^ 5 * t ^ 2 +
      8536 * e ^ 4 * t ^ 3 +
      151 * e ^ 3 * t ^ 4 +
      1 * e ^ 2 * t ^ 5 +
      161184626 * e ^ 6 +
      29739291 * e ^ 5 * t +
      2222385 * e ^ 4 * t ^ 2 +
      84976 * e ^ 3 * t ^ 3 +
      1698 * e ^ 2 * t ^ 4 +
      15 * e * t ^ 5 +
      1003629076 * e ^ 5 +
      181363820 * e ^ 4 * t +
      13091339 * e ^ 3 * t ^ 2 +
      471675 * e ^ 2 * t ^ 3 +
      8412 * e * t ^ 4 +
      56 * t ^ 5 +
      4496039330 * e ^ 4 +
      749367784 * e ^ 3 * t +
      47662978 * e ^ 2 * t ^ 2 +
      1381289 * e * t ^ 3 +
      15456 * t ^ 4 +
      14078419513 * e ^ 3 +
      2001221570 * e ^ 2 * t +
      97777620 * e * t ^ 2 +
      1662600 * t ^ 3 +
      29083300441 * e ^ 2 +
      3104570905 * e * t +
      86172704 * t ^ 2 +
      35268217548 * e +
      2109247560 * t +
      18689954336 := by positivity
    convert hp using 1 <;> dsimp [budgetPoly, seed, eta, vcoef, wcoef, xcoef, e, t] <;> ring
  · let t := R - 64
    have ht : 0 ≤ t := by dsimp [t]; omega
    have hp : 0 ≤
      12 * t ^ 5 +
      3472 * t ^ 4 +
      397204 * t ^ 3 +
      22392432 * t ^ 2 +
      619411460 * t +
      6681985280 := by positivity
    convert hp using 1 <;> dsimp [budgetPoly, seed, eta, vcoef, wcoef, xcoef, t] <;> ring

private theorem rounding (X C U Q0 L : ℤ) (hX : 0 < X) (hC : 0 ≤ C)
    (hU : 0 ≤ U) (hQ : 1 ≤ Q0)
    (hbudget : 0 ≤ (L - 2 * X - Q0) * X - C * U) :
    let x := U / X
    let S := U - x * X
    0 ≤ x ∧ 0 ≤ S ∧ S < X ∧
      1 ≤ 2 * S + Q0 + C * x ∧ 2 * S + Q0 + C * x ≤ L := by
  dsimp only
  let x := U / X
  let S := U - x * X
  change 0 ≤ x ∧ 0 ≤ S ∧ S < X ∧
    1 ≤ 2 * S + Q0 + C * x ∧ 2 * S + Q0 + C * x ≤ L
  have hx : 0 ≤ x := Int.ediv_nonneg hU hX.le
  have he := Int.emod_add_mul_ediv U X
  have hr0 := Int.emod_nonneg U (by omega : X ≠ 0)
  have hr1 := Int.emod_lt_of_pos U hX
  change U % X + X * x = U at he
  have hs0 : 0 ≤ S := by dsimp [S]; nlinarith only [he, hr0]
  have hs1 : S < X := by dsimp [S]; nlinarith only [he, hr1]
  have hxU : x * X ≤ U := by dsimp [S] at hs0; omega
  have hcU : C * (x * X) ≤ C * U := mul_le_mul_of_nonneg_left hxU hC
  have hSX : 2 * S * X < 2 * X * X := by nlinarith only [mul_lt_mul_of_pos_right hs1 hX]
  have htop : 2 * S + Q0 + C * x ≤ L := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_right (show L + 1 ≤ 2 * S + Q0 + C * x by omega) hX.le
    nlinarith only [hbudget, hcU, hSX, hmul, hX]
  refine ⟨hx, hs0, hs1, ?_, htop⟩
  have hcx : 0 ≤ C * x := mul_nonneg hC hx
  omega

set_option maxHeartbeats 1600000 in
private theorem uniform_floor_bound (R D HU w L : ℤ)
    (hD : 4 ≤ D) (hR : D * D ≤ R)
    (hbig : 8 ≤ D ∨ D = 4 ∧ 64 ≤ R)
    (hHU : 2 * HU = D * R * R * R - 1 - vcoef R D)
    (hw : 2 * D * w = D * R - 2 * R)
    (hL : 2 * L = seed R - 1) :
    let U := HU - w * wcoef R D
    let x := U / xcoef R D
    let S := U - x * xcoef R D
    let Q := 1 + (R + 1) * w + eta R * x
    0 ≤ w ∧ 0 < U ∧ 0 ≤ x ∧ 2 * x < R ∧
      0 ≤ S ∧ 1 ≤ 2 * S + Q ∧ 2 * S + Q ≤ L := by
  dsimp only
  let A := seed R
  let C := eta R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let N := D * R * R * R - 1
  let U := HU - w * W
  let Q0 := 1 + (R + 1) * w
  let x := U / X
  let S := U - x * X
  have hR4 : 4 ≤ R := by nlinarith
  have hRD : 0 < R - D := by nlinarith
  have hD0 : 0 < D := by omega
  have hR0 : 0 < R := by omega
  have hA0 : 0 < A := by dsimp [A, seed]; positivity
  have hC0 : 0 ≤ C := by dsimp [C, eta]; positivity
  have hV0 : 0 < V := by dsimp [V, vcoef]; positivity
  have hW0 : 0 ≤ W := by dsimp [W, wcoef]; positivity
  have hX0 : 0 < X := by dsimp [X, xcoef]; positivity
  have hw0 : 0 ≤ w := by
    by_contra h
    have hneg := mul_nonpos_of_nonneg_of_nonpos hD0.le (show w ≤ 0 by omega)
    have hpos : 0 < (D - 2) * R := mul_pos (by omega) hR0
    nlinarith only [hw, hneg, hpos]
  have hUeq : 2 * D * U =
      (R - D) * (2 * D * R * R + (D + 2) * (R + 1)) := by
    dsimp only [U, W]
    dsimp [vcoef, wcoef] at hHU ⊢
    linear_combination D * hHU - (D * R * R + (D + 1) * R + 1) * hw
  have hU0 : 0 < U := by
    have hb : 0 < (R - D) * (2 * D * R * R + (D + 2) * (R + 1)) := by positivity
    have hDU : 0 < D * U := by nlinarith only [hUeq, hb]
    exact ((mul_pos_iff_of_pos_left hD0).mp hDU)
  have hQ0 : 1 ≤ Q0 := by dsimp [Q0]; have := mul_nonneg (by omega : 0 ≤ R + 1) hw0; omega
  have hid : 2 * D * ((L - 2 * X - Q0) * X - C * U) = budgetPoly R D := by
    calc
      _ = D * (A - 1 - 4 * X - 2) * X - D * C * (N - V) +
          (2 * D * w) * (C * W - (R + 1) * X) := by
            dsimp only [U, Q0]
            change 2 * HU = N - V at hHU
            change 2 * L = A - 1 at hL
            linear_combination D * X * hL - D * C * hHU
      _ = budgetPoly R D := by rw [hw]; rfl
  have hbudget : 0 ≤ (L - 2 * X - Q0) * X - C * U := by
    have hp := budget_positive R D hR hbig
    by_contra h
    have hn := mul_neg_of_pos_of_neg (show 0 < 2 * D by omega)
      (show (L - 2 * X - Q0) * X - C * U < 0 by omega)
    omega
  have hround := rounding X C U Q0 L hX0 hC0 hU0.le hQ0 hbudget
  change 0 ≤ x ∧ 0 ≤ S ∧ S < X ∧ 1 ≤ 2 * S + Q0 + C * x ∧
    2 * S + Q0 + C * x ≤ L at hround
  have hUle : U ≤ HU := by dsimp [U]; have := mul_nonneg hw0 hW0; omega
  have hxU : x * X ≤ U := by
    have hh := hround.2.1
    change 0 ≤ U - x * X at hh
    omega
  have hcycle : R * X = N + A := by dsimp [X, N, A, xcoef, seed]; ring
  have hxcap : 2 * x < R := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (show R ≤ 2 * x by omega) hX0.le
    change 2 * HU = N - V at hHU
    nlinarith only [hm, hxU, hUle, hcycle, hHU, hV0, hA0]
  refine ⟨hw0, hU0, hround.1, hxcap, hround.2.1, ?_, ?_⟩
  · simpa only [Q0, add_assoc] using hround.2.2.2.1
  · simpa only [Q0, add_assoc] using hround.2.2.2.2

open private pow_ge_four
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

set_option maxHeartbeats 1600000 in
private theorem hard_floor (s d : ℕ) (hd : 2 ≤ d) (hhard : 2*d ≤ s) :
    let R : ℤ := 2 ^ s
    let D : ℤ := 2 ^ d
    let H : ℤ := 2 ^ (s-d)
    let N := D * R * R * R - 1
    let HU := (N - vcoef R D) / 2
    let w := (2 : ℤ) ^ (s-1) - H
    let U := HU - w * wcoef R D
    let x := U / xcoef R D
    let S := U - x * xcoef R D
    let Q := 1 + (R+1) * w + eta R * x
    0 ≤ x ∧ x < (2 : ℤ) ^ (s-1) ∧ 0 ≤ S ∧
      1 ≤ 2*S+Q ∧ 2*S+Q ≤ (seed R-1)/2 := by
  dsimp only
  by_cases hd3 : 3 ≤ d
  · let R : ℤ := 2 ^ s
    let D : ℤ := 2 ^ d
    let H : ℤ := 2 ^ (s-d)
    let r : ℤ := 2 ^ (s-1)
    let e : ℤ := 2 ^ (d-1)
    let N := D*R*R*R-1
    let HU := (N-vcoef R D)/2
    let w := r-H
    let L := (seed R-1)/2
    have hD := pow_ge_four d hd
    have hD8 : (8 : ℤ) ≤ D := by
      simpa [D] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd3
    have hR : D*D ≤ R := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hhard
      simpa only [show 2*d=d+d by omega,pow_add] using h
    have hRH : D*H=R := by
      dsimp [R,D,H]; rw [←pow_add,show d+(s-d)=s by omega]
    have hr : 2*r=R := by
      dsimp [r,R]; conv_rhs => rw [show s=s-1+1 by omega,pow_succ]
      ring
    have he : 2*e=D := by
      dsimp [e,D]; conv_rhs => rw [show d=d-1+1 by omega,pow_succ]
      ring
    have hHU : 2*HU=N-vcoef R D := by
      have hp : N-vcoef R D=2*(e*(R*R*R-R*R-R-1)-1) := by
        dsimp [N,vcoef]; rw [←he]; ring
      dsimp [HU]; omega
    have hw : 2*D*w=D*R-2*R := by
      dsimp only [w]
      linear_combination D*hr-2*hRH
    have hL : 2*L=seed R-1 := by
      have hp : seed R-1=2*(r*eta R) := by
        dsimp [seed,eta]; rw [←hr]; ring
      dsimp [L]; omega
    have h := uniform_floor_bound R D HU w L hD hR (Or.inl hD8) hHU hw hL
    dsimp only [R,D,H,r,e,N,HU,w,L] at h
    dsimp only [r,R] at hr
    refine ⟨h.2.2.1,?_,h.2.2.2.2.1,h.2.2.2.2.2.1,?_⟩
    · change _ < r
      dsimp only [r]
      omega
    · exact h.2.2.2.2.2.2
  · have hd2 : d=2 := by omega
    subst d
    by_cases hs6 : 6 ≤ s
    · let R : ℤ := 2 ^ s
      let r : ℤ := 2 ^ (s-1)
      let H : ℤ := 2 ^ (s-2)
      let HU := (4*R*R*R-1-vcoef R 4)/2
      let w := r-H
      let L := (seed R-1)/2
      have hR64 : (64 : ℤ) ≤ R := by
        simpa [R] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hs6
      have hr : 2*r=R := by
        dsimp [r,R]; conv_rhs => rw [show s=s-1+1 by omega,pow_succ]
        ring
      have hH : 4*H=R := by
        dsimp [H,R]
        conv_rhs => rw [show s=(s-2)+2 by omega,pow_add]
        norm_num; ring
      have hHU : 2*HU=4*R*R*R-1-vcoef R 4 := by
        have hp : 4*R*R*R-1-vcoef R 4=2*(2*(R*R*R-R*R-R-1)-1) := by dsimp [vcoef]; ring
        dsimp [HU]; omega
      have hw : 2*4*w=4*R-2*R := by dsimp only [w]; linear_combination 4*hr-2*hH
      have hL : 2*L=seed R-1 := by
        have hp : seed R-1=2*(r*eta R) := by dsimp [seed,eta]; rw [←hr]; ring
        dsimp [L]; omega
      have h := uniform_floor_bound R 4 HU w L (by omega) (by nlinarith) (Or.inr ⟨rfl,hR64⟩) hHU hw hL
      norm_num only [show (2 : ℤ)^2=4 by norm_num] at *
      dsimp only [R,r,H,HU,w,L] at h
      dsimp only [r,R] at hr
      refine ⟨h.2.2.1,?_,h.2.2.2.2.1,h.2.2.2.2.2.1,?_⟩
      · change _ < r
        dsimp only [r]
        omega
      · exact h.2.2.2.2.2.2
    · have cases : s=4 ∨ s=5 := by omega
      rcases cases with rfl | rfl <;> norm_num [seed,eta,vcoef,wcoef,xcoef]

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
