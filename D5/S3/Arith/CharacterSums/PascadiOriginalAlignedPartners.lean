/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalAlignedPartners
   mirror-E: none(waiver:open-total-original-count)
   anchors: []
   utility: none
   digest: Aligned original baselines force modular-zero partners into the zero-pencil stratum. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalExceptionalPartners
import D5.S3.Arith.CharacterSums.PascadiOriginalModularPartners

/-! A modular-zero partner of an exactly aligned retained baseline is aligned
over the integers and has identically zero integer pencil. This includes
horizontal and vertical directions; the original word supplies the full p³ root. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem linear_square_homogeneous {K : Type*} [Field K]
    (q x y : K × K) (c : K)
    (hpoly : PrimeCube.linear x.1 x.2 * PrimeCube.linear y.1 y.2 =
      C c*(PrimeCube.linear q.1 q.2)^2) :
    ∀ s t : K, (s*x.1+t*x.2)*(s*y.1+t*y.2) = c*(s*q.1+t*q.2)^2 := by
  have hn : C (x.1*y.1)+C (x.1*y.2+x.2*y.1)*X+C (x.2*y.2)*X^2 =
      C (c*q.1^2)+C (c*(q.1*q.2+q.2*q.1))*X+C (c*q.2^2)*X^2 := by
    convert hpoly using 1 <;>
      simp only [PrimeCube.linear, Polynomial.C_mul, Polynomial.C_add,
        Polynomial.C_pow] <;> ring
  have h₀ := congrArg (fun P : K[X] => P.coeff 0) hn
  have h₁ := congrArg (fun P : K[X] => P.coeff 1) hn
  have h₂ := congrArg (fun P : K[X] => P.coeff 2) hn
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at h₀ h₁ h₂
  norm_num at h₀ h₁ h₂
  intro s t
  linear_combination s^2*h₀+s*t*h₁+t^2*h₂

private theorem square_linear_second_alignment {K : Type*} [Field K]
    (q x y : K × K) (c : K) (hc : c ≠ 0) (hq : q.1 ≠ 0 ∨ q.2 ≠ 0)
    (hx : fieldDet q x = 0)
    (hpoly : ∀ s t : K, (s*x.1+t*x.2)*(s*y.1+t*y.2) = c*(s*q.1+t*q.2)^2) :
    fieldDet q y = 0 := by
  obtain ⟨a, ha₁, ha₂⟩ := fieldDet_zero_scalar q x hq hx
  obtain ⟨s, t, hst⟩ : ∃ s t : K, s*q.1+t*q.2 = 1 := by
    rcases hq with hq | hq
    · exact ⟨q.1⁻¹, 0, by simp [hq]⟩
    · exact ⟨0, q.2⁻¹, by simp [hq]⟩
  have hst' : (s+q.2)*q.1+(t-q.1)*q.2 = 1 := by linear_combination hst
  have hax : s*x.1+t*x.2 = a := by rw [ha₁, ha₂]; linear_combination a*hst
  have hax' : (s+q.2)*x.1+(t-q.1)*x.2 = a := by
    rw [ha₁, ha₂]
    linear_combination a*hst'
  have h₀ := hpoly s t
  rw [hax, hst] at h₀
  norm_num at h₀
  have h₁ := hpoly (s+q.2) (t-q.1)
  rw [hax', hst'] at h₁
  norm_num at h₁
  have ha : a ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h₀
    exact hc h₀.symm
  apply (mul_eq_zero.mp (show a*fieldDet q y = 0 by
    dsimp only [fieldDet]
    linear_combination h₀-h₁)).resolve_left ha

private theorem square_linear_product_alignment {K : Type*} [Field K]
    (q x y : K × K) (c : K) (hc : c ≠ 0) (hq : q.1 ≠ 0 ∨ q.2 ≠ 0)
    (hpoly : ∀ s t : K, (s*x.1+t*x.2)*(s*y.1+t*y.2) = c*(s*q.1+t*q.2)^2) :
    fieldDet q x = 0 ∧ fieldDet q y = 0 := by
  have hzero : fieldDet q x*fieldDet q y = 0 := by
    have hh := hpoly q.2 (-q.1)
    dsimp only [fieldDet]
    linear_combination hh
  rcases mul_eq_zero.mp hzero with hx | hy
  · exact ⟨hx, square_linear_second_alignment q x y c hc hq hx hpoly⟩
  · refine ⟨square_linear_second_alignment q y x c hc hq hy ?_, hy⟩
    intro s t
    calc
      _ = (s*x.1+t*x.2)*(s*y.1+t*y.2) := mul_comm _ _
      _ = _ := hpoly s t

private theorem aligned_field_pencil_partners {K : Type*} [Field K]
    (q a b x y : K × K) (β : K) (hq : q.1 ≠ 0 ∨ q.2 ≠ 0)
    (ha : fieldDet q a = 0) (hb : fieldDet q b = 0)
    (hL : (a.1+b.1-q.1)+β*(a.2+b.2-q.2) ≠ 0)
    (hQ : (a.1+β*a.2)*(b.1+β*b.2) ≠ 0)
    (hD : (a.1+β*a.2)*(b.1+β*b.2)-
      ((a.1+b.1-q.1)+β*(a.2+b.2-q.2))*(q.1+β*q.2) ≠ 0)
    (hpoly : PrimeCube.linear (a.1+b.1-q.1) (a.2+b.2-q.2)*
        PrimeCube.linear x.1 x.2*PrimeCube.linear y.1 y.2 =
      (PrimeCube.linear x.1 x.2+PrimeCube.linear y.1 y.2-PrimeCube.linear q.1 q.2)*
        (PrimeCube.linear a.1 a.2*PrimeCube.linear b.1 b.2)) :
    fieldDet q x = 0 ∧ fieldDet q y = 0 := by
  obtain ⟨u, ha₁, ha₂⟩ := fieldDet_zero_scalar q a hq ha
  obtain ⟨v, hb₁, hb₂⟩ := fieldDet_zero_scalar q b hq hb
  let k := u+v-1
  let B := u*v
  let s := q.1+β*q.2
  have hLe : (a.1+b.1-q.1)+β*(a.2+b.2-q.2) = k*s := by
    dsimp only [k, s]
    rw [ha₁, ha₂, hb₁, hb₂]
    ring
  have hQe : (a.1+β*a.2)*(b.1+β*b.2) = B*s^2 := by
    dsimp only [B, s]
    rw [ha₁, ha₂, hb₁, hb₂]
    ring
  have hDe : (a.1+β*a.2)*(b.1+β*b.2)-
      ((a.1+b.1-q.1)+β*(a.2+b.2-q.2))*(q.1+β*q.2) = (B-k)*s^2 := by
    rw [hLe, hQe]
    dsimp only [s]
    ring
  have hk : k ≠ 0 := by intro hz; apply hL; rw [hLe, hz, zero_mul]
  have hB : B ≠ 0 := by intro hz; apply hQ; rw [hQe, hz, zero_mul]
  have hBk : B-k ≠ 0 := by intro hz; apply hD; rw [hDe, hz, zero_mul]
  let h := -B/k
  have hhk : h*k = -B := by dsimp only [h]; field_simp [hk]
  have hh : h ≠ 0 := by
    intro hz
    apply hB
    linear_combination hhk-k*hz
  have hh1 : h+1 ≠ 0 := by
    intro hz
    apply hBk
    linear_combination hhk-k*hz
  let G := PrimeCube.linear q.1 q.2
  let X := PrimeCube.linear x.1 x.2
  let Y := PrimeCube.linear y.1 y.2
  have hG : G ≠ 0 := by
    intro hz
    have h₀ := congrArg (fun P : K[X] => P.coeff 0) hz
    have h₁ := congrArg (fun P : K[X] => P.coeff 1) hz
    simp [G, PrimeCube.linear] at h₀ h₁
    exact hq.elim (fun h => h h₀) (fun h => h h₁)
  have hLb : PrimeCube.linear (a.1+b.1-q.1) (a.2+b.2-q.2) = C k*G := by
    dsimp only [k, G, PrimeCube.linear]
    rw [ha₁, ha₂, hb₁, hb₂]
    simp only [map_add, map_sub, map_mul, map_one]
    ring
  have hQb : PrimeCube.linear a.1 a.2*PrimeCube.linear b.1 b.2 = C B*G^2 := by
    dsimp only [B, G, PrimeCube.linear]
    rw [ha₁, ha₂, hb₁, hb₂]
    simp only [map_mul]
    ring
  rw [hLb, hQb] at hpoly
  have hinner : C k*X*Y-C B*G*(X+Y-G) = 0 := by
    apply (mul_eq_zero.mp (show G*(C k*X*Y-C B*G*(X+Y-G)) = 0 by
      linear_combination hpoly)).resolve_left hG
  have hcast : C h*C k = -C B := by rw [← map_mul, hhk, map_neg]
  have hsquare : (X+C h*G)*(Y+C h*G) = C (h*(h+1))*G^2 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show C k*((X+C h*G)*(Y+C h*G)-C (h*(h+1))*G^2) = 0 by
      simp only [map_mul, map_add, map_one]
      linear_combination hinner+G*(X+Y-G)*hcast)).resolve_left (C_ne_zero.mpr hk)
  have hlin (z : K × K) : PrimeCube.linear z.1 z.2+C h*G =
      PrimeCube.linear (z.1+h*q.1) (z.2+h*q.2) := by
    dsimp only [G, PrimeCube.linear]
    simp only [map_add, map_mul]
    ring
  dsimp only [X, Y] at hsquare
  rw [hlin x, hlin y] at hsquare
  obtain ⟨hx, hy⟩ := square_linear_product_alignment q
    (x.1+h*q.1, x.2+h*q.2) (y.1+h*q.1, y.2+h*q.2)
    (h*(h+1)) (mul_ne_zero hh hh1) hq
    (linear_square_homogeneous q _ _ _ hsquare)
  constructor
  · dsimp only [fieldDet] at hx ⊢
    linear_combination hx
  · dsimp only [fieldDet] at hy ⊢
    linear_combination hy

private theorem primitive_direction_scalar (v z : Coordinate)
    (hv : Int.gcd v.1 v.2 = 1) (hz : coordinateDet v z = 0) :
    ∃ m : ℤ, z = (m*v.1, m*v.2) := by
  have hbez : v.1*Int.gcdA v.1 v.2+v.2*Int.gcdB v.1 v.2 = 1 := by
    simpa only [hv, Nat.cast_one] using (Int.gcd_eq_gcd_ab v.1 v.2).symm
  refine ⟨Int.gcdA v.1 v.2*z.1+Int.gcdB v.1 v.2*z.2, ?_⟩
  apply Prod.ext
  · dsimp only [coordinateDet] at hz
    linear_combination -z.1*hbez-Int.gcdB v.1 v.2*hz
  · dsimp only [coordinateDet] at hz
    linear_combination -z.2*hbez+Int.gcdA v.1 v.2*hz

private theorem primitive_scalar_height {J₁ J₂ : ℝ} (h₁₂ : J₂ ≤ J₁)
    (v : Coordinate) (hv : Int.gcd v.1 v.2 = 1) (m : ℤ)
    (hz : CoordinateBound J₁ J₂ (m*v.1, m*v.2)) : |(m : ℝ)| ≤ J₁ := by
  have hv0 : v.1 ≠ 0 ∨ v.2 ≠ 0 := Int.ne_zero_of_gcd (by omega)
  rcases hv0 with hv0 | hv0
  · have hmin : (1 : ℝ) ≤ |(v.1 : ℝ)| := by exact_mod_cast Int.one_le_abs hv0
    have hh := hz.1
    simp only [Int.cast_mul, abs_mul] at hh
    nlinarith [abs_nonneg (m : ℝ)]
  · have hmin : (1 : ℝ) ≤ |(v.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hv0
    have hh := hz.2.trans h₁₂
    simp only [Int.cast_mul, abs_mul] at hh
    nlinarith [abs_nonneg (m : ℝ)]

private theorem original_small_determinants (p : ℕ) (hp : p.Prime) (J₁ J₂ M : ℝ)
    (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂)
    (hcap : (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3)
    (hlarge : (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ)) :
    8*J₁*J₂ < (p : ℝ) ∧ 6*J₁^3 < (p : ℝ)^3 := by
  let A : ℝ := (24*(8*(18 : ℝ))^4)^5
  have hA : (8 : ℝ)^40 ≤ A := by norm_num [A]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hJ₁ : 0 ≤ J₁ := by linarith
  have hJ₂ : 0 ≤ J₂ := by linarith
  have h40 : (J₁*J₂)^40 ≤ M^40*(p : ℝ)^24 := by
    convert pow_le_pow_left₀ (by positivity : 0 ≤ (J₁*J₂)^5) hcap 8 using 1 <;> ring
  have hbound : A*(J₁*J₂)^40 < (p : ℝ)^25 := by
    calc
      _ ≤ A*(M^40*(p : ℝ)^24) := mul_le_mul_of_nonneg_left h40 (by norm_num [A])
      _ = (A*M^40)*(p : ℝ)^24 := by ring
      _ < (p : ℝ)*(p : ℝ)^24 := mul_lt_mul_of_pos_right hlarge (by positivity)
      _ = _ := by ring
  have h8 : 8*(J₁*J₂) < (p : ℝ) := by
    apply (pow_lt_pow_iff_left₀ (by positivity : 0 ≤ 8*(J₁*J₂)) hp0.le
      (by decide : 40 ≠ 0)).mp
    calc
      _ = (8 : ℝ)^40*(J₁*J₂)^40 := by ring
      _ ≤ A*(J₁*J₂)^40 := mul_le_mul_of_nonneg_right hA (by positivity)
      _ < (p : ℝ)^25 := hbound
      _ ≤ (p : ℝ)^40 := pow_le_pow_right₀ hp1 (by decide : 25 ≤ 40)
  have h8J : 8*J₁ < (p : ℝ) :=
    (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hJ₁ h₂)
      (by norm_num : (0 : ℝ) ≤ 8)).trans_lt h8
  have hcubed := pow_lt_pow_left₀ h8J (by positivity : 0 ≤ 8*J₁) (by decide : 3 ≠ 0)
  exact ⟨by simpa only [mul_assoc] using h8, by nlinarith [pow_nonneg hJ₁ 3]⟩

private theorem det_zero_of_modular_box {p : ℕ} {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) (hsmall : 2*J₁*J₂ < (p : ℝ))
    (q z : Coordinate) (hq : CoordinateBound J₁ J₂ q) (hz : CoordinateBound J₁ J₂ z)
    (hzero : ((coordinateDet q z : ℤ) : ZMod p) = 0) : coordinateDet q z = 0 := by
  have hb : |((coordinateDet q z : ℤ) : ℝ)| ≤ 2*J₁*J₂ := by
    simp only [coordinateDet, Int.cast_sub, Int.cast_mul]
    calc
      _ ≤ |(q.1 : ℝ)| * |(z.2 : ℝ)|+|(q.2 : ℝ)| * |(z.1 : ℝ)| := by
        simpa only [abs_mul] using abs_sub ((q.1 : ℝ)*z.2) ((q.2 : ℝ)*z.1)
      _ ≤ J₁*J₂+J₂*J₁ := add_le_add
        (mul_le_mul hq.1 hz.2 (abs_nonneg _) hJ₁)
        (mul_le_mul hq.2 hz.1 (abs_nonneg _) hJ₂)
      _ = _ := by ring
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  by_contra hn
  have hle := Int.le_abs_of_dvd hn hd
  have hleR : (p : ℝ) ≤ |((coordinateDet q z : ℤ) : ℝ)| := by exact_mod_cast hle
  exact (not_le_of_gt (hb.trans_lt hsmall)) hleR

private theorem primitive_line_pencil_zero {c : ℕ} [NeZero c] (J : ℝ) (hJ : 0 ≤ J)
    (hsmall : 6*J^3 < c) (v : Coordinate) (d a b m n : ℤ)
    (hd : |(d : ℝ)| ≤ J) (ha : |(a : ℝ)| ≤ J) (hb : |(b : ℝ)| ≤ J)
    (hm : |(m : ℝ)| ≤ J) (hn : |(n : ℝ)| ≤ J) (β : ZMod c)
    (hL : IsUnit ((endpointL (d*v.1, d*v.2)
      ((a*v.1, a*v.2), (b*v.1, b*v.2))).eval₂ (Int.castRingHom (ZMod c)) β))
    (hroot : (pencil (d*v.1, d*v.2) ((a*v.1, a*v.2), (b*v.1, b*v.2))
      ((m*v.1, m*v.2), (n*v.1, n*v.2))).eval₂ (Int.castRingHom (ZMod c)) β = 0) :
    pencil (d*v.1, d*v.2) ((a*v.1, a*v.2), (b*v.1, b*v.2))
      ((m*v.1, m*v.2), (n*v.1, n*v.2)) = 0 := by
  let k := a+b-d
  let B := a*b
  let E := k*m*n-B*(m+n-d)
  have hLform : endpointL (d*v.1, d*v.2) ((a*v.1, a*v.2), (b*v.1, b*v.2)) =
      C k*coordinateLinear v := by
    simp only [endpointL, coeffL, coeffM, coordinateLinear, PrimeCube.linear, k]
    simp only [map_add, map_sub, map_mul]
    ring
  have hPform : pencil (d*v.1, d*v.2) ((a*v.1, a*v.2), (b*v.1, b*v.2))
      ((m*v.1, m*v.2), (n*v.1, n*v.2)) = C E*(coordinateLinear v)^3 := by
    simp only [pencil, endpointL, endpointQ, coeffL, coeffM, coeffQ, coeffR, coeffS,
      coordinateLinear, PrimeCube.linear, PrimeCube.quadratic, E, k, B]
    simp only [map_add, map_sub, map_mul]
    ring
  have hk : |(k : ℝ)| ≤ 3*J := by
    dsimp only [k]
    push_cast
    exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans (by linarith))
  have hB : |(B : ℝ)| ≤ J^2 := by
    dsimp only [B]
    rw [Int.cast_mul, abs_mul]
    simpa only [pow_two] using mul_le_mul ha hb (abs_nonneg _) hJ
  have hsum : |((m+n-d : ℤ) : ℝ)| ≤ 3*J := by
    push_cast
    exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans (by linarith))
  have hE : |(E : ℝ)| ≤ 6*J^3 := by
    dsimp only [E]
    push_cast
    calc
      _ ≤ |(k : ℝ)| * |(m : ℝ)| * |(n : ℝ)|+|(B : ℝ)| * |((m+n-d : ℤ) : ℝ)| := by
        simpa only [abs_mul, Int.cast_sub, Int.cast_add] using
          abs_sub ((k : ℝ)*m*n) ((B : ℝ)*(m+n-d))
      _ ≤ (3*J*J)*J+J^2*(3*J) := add_le_add
        (mul_le_mul (mul_le_mul hk hm (abs_nonneg _) (by positivity)) hn
          (abs_nonneg _) (by positivity))
        (mul_le_mul hB hsum (abs_nonneg _) (by positivity))
      _ = _ := by ring
  rw [hLform, eval₂_mul, eval₂_C] at hL
  have hv : IsUnit ((coordinateLinear v).eval₂ (Int.castRingHom (ZMod c)) β) :=
    (IsUnit.mul_iff.mp hL).2
  rw [hPform, eval₂_mul, eval₂_C, eval₂_pow] at hroot
  have hEmod : (E : ZMod c) = 0 := by
    apply (hv.pow 3).mul_right_cancel
    simpa only [Int.coe_castRingHom, zero_mul] using hroot
  have hEdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hEmod
  have hEzero : E = 0 := by
    by_contra hn
    have hle := Int.le_abs_of_dvd hn hEdvd
    have hleR : (c : ℝ) ≤ |(E : ℝ)| := by exact_mod_cast hle
    exact (not_le_of_gt (hE.trans_lt hsmall)) hleR
  rw [hPform, hEzero, map_zero, zero_mul]

private theorem actual_aligned_modular_zero_pencil (p : ℕ) (hp : p.Prime)
    (J₁ J₂ M : ℝ) (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base e : Endpoint)
    (hr : IsUnit (R.1 : ZMod (p^3))) (ht : IsUnit (-(physical R V q).2 : ZMod (p^3)))
    (hanchor : IsUnit ((physical R V q).1 : ZMod (p^3)))
    (hbase : WordSolution (p^3) a₁ a₂ R V q base)
    (hx : IsUnit ((physical R V base.1).1 : ZMod (p^3)))
    (hy : IsUnit ((physical R V base.2).1 : ZMod (p^3)))
    (hk : IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical R V q).1 : ZMod (p^3))))
    (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂) (haligned : Aligned q base)
    (hq : CoordinateBound J₁ J₂ q) (hb₁ : CoordinateBound J₁ J₂ base.1)
    (hb₂ : CoordinateBound J₁ J₂ base.2)
    (he₁ : CoordinateBound J₁ J₂ e.1) (he₂ : CoordinateBound J₁ J₂ e.2)
    (hword : WordSolution (p^3) a₁ a₂ R V q e)
    (hred : (pencil q base e).map (Int.castRingHom (ZMod p)) = 0)
    (hcap : (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3)
    (hlarge : (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ)) : pencil q base e = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let reduction : ZMod (p^3) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  let βc := (V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let β := reduction βc
  let fc (z : Coordinate) : ZMod p × ZMod p := (z.1, z.2)
  have hq0 : (fc q).1 ≠ 0 ∨ (fc q).2 ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : ((physical R V q).1 : ZMod p) = 0 := by
      simp only [physical, Int.cast_add, Int.cast_mul]
      change (fc q).1*(R.1 : ZMod p)+(fc q).2*(V.1 : ZMod p) = 0
      rw [hn.1, hn.2, zero_mul, zero_add, zero_mul]
    exact (hanchor.map reduction).ne_zero (by simpa only [map_intCast] using hz)
  have hu := original_singular_unit_observations a₁ a₂ ha₁ ha₂ R V q base
    hr ht hbase hx hy hk
  have hL : (endpointL q base).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 := by
    simpa only [Polynomial.ringHom_eval₂_intCastRingHom] using (hu.1.map reduction).ne_zero
  have hQ : (endpointQ base).eval₂ (Int.castRingHom (ZMod p)) β ≠ 0 := by
    simpa only [Polynomial.ringHom_eval₂_intCastRingHom] using (hu.2.1.map reduction).ne_zero
  have hD : (endpointQ base-endpointL q base*coordinateLinear q).eval₂
      (Int.castRingHom (ZMod p)) β ≠ 0 := by
    simpa only [Polynomial.ringHom_eval₂_intCastRingHom] using (hu.2.2.map reduction).ne_zero
  have hLe : (endpointL q base).eval₂ (Int.castRingHom (ZMod p)) β =
      ((base.1.1 : ZMod p)+base.2.1-q.1)+β*((base.1.2 : ZMod p)+base.2.2-q.2) := by
    simp only [endpointL, PrimeCube.linear, coeffL, coeffM, eval₂_add, eval₂_mul,
      eval₂_C, eval₂_X, Int.coe_castRingHom, Int.cast_add, Int.cast_sub]
    ring
  have hQe : (endpointQ base).eval₂ (Int.castRingHom (ZMod p)) β =
      ((base.1.1 : ZMod p)+β*base.1.2)*((base.2.1 : ZMod p)+β*base.2.2) := by
    simp only [endpointQ, PrimeCube.quadratic, coeffQ, coeffR, coeffS,
      eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, Int.coe_castRingHom,
      Int.cast_add, Int.cast_mul]
    ring
  have hZe : (coordinateLinear q).eval₂ (Int.castRingHom (ZMod p)) β =
      (q.1 : ZMod p)+β*q.2 := by
    simp only [coordinateLinear, PrimeCube.linear, eval₂_add, eval₂_mul,
      eval₂_C, eval₂_X, Int.coe_castRingHom]
    ring
  rw [hLe] at hL
  rw [hQe] at hQ
  simp only [eval₂_sub, eval₂_mul, hLe, hQe, hZe] at hD
  have ha : fieldDet (fc q) (fc base.1) = 0 := by
    have hh := congrArg (Int.castRingHom (ZMod p)) haligned.1
    simpa only [fieldDet, fc, coordinateDet, Int.coe_castRingHom,
      Int.cast_sub, Int.cast_mul, Int.cast_zero] using hh
  have hb : fieldDet (fc q) (fc base.2) = 0 := by
    have hh := congrArg (Int.castRingHom (ZMod p)) haligned.2
    simpa only [fieldDet, fc, coordinateDet, Int.coe_castRingHom,
      Int.cast_sub, Int.cast_mul, Int.cast_zero] using hh
  have hpoly :
      PrimeCube.linear ((fc base.1).1+(fc base.2).1-(fc q).1)
          ((fc base.1).2+(fc base.2).2-(fc q).2)*
        PrimeCube.linear (fc e.1).1 (fc e.1).2*PrimeCube.linear (fc e.2).1 (fc e.2).2 =
      (PrimeCube.linear (fc e.1).1 (fc e.1).2+
        PrimeCube.linear (fc e.2).1 (fc e.2).2-PrimeCube.linear (fc q).1 (fc q).2)*
          (PrimeCube.linear (fc base.1).1 (fc base.1).2*
            PrimeCube.linear (fc base.2).1 (fc base.2).2) := by
    dsimp only [fc]
    simp only [pencil, endpointL, endpointQ, PrimeCube.linear, PrimeCube.quadratic,
      coeffL, coeffM, coeffQ, coeffR, coeffS, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Int.coe_castRingHom, Int.cast_add, Int.cast_sub, Int.cast_mul,
      map_add, map_sub, map_mul] at hred
    simp only [PrimeCube.linear, map_add, map_sub]
    linear_combination hred
  obtain ⟨hdet₁, hdet₂⟩ := aligned_field_pencil_partners
    (fc q) (fc base.1) (fc base.2) (fc e.1) (fc e.2) β hq0 ha hb hL hQ hD hpoly
  obtain ⟨h8, hcube⟩ := original_small_determinants p hp J₁ J₂ M h₁₂ h₂ hcap hlarge
  have hJ₁ : 0 ≤ J₁ := by linarith
  have hJ₂ : 0 ≤ J₂ := by linarith
  have hsmall : 2*J₁*J₂ < (p : ℝ) := by nlinarith [mul_nonneg hJ₁ hJ₂]
  have he₁aligned : coordinateDet q e.1 = 0 := det_zero_of_modular_box hJ₁ hJ₂ hsmall
    q e.1 hq he₁ (by simpa only [coordinateDet, fieldDet, fc, Int.cast_sub, Int.cast_mul] using hdet₁)
  have he₂aligned : coordinateDet q e.2 = 0 := det_zero_of_modular_box hJ₁ hJ₂ hsmall
    q e.2 hq he₂ (by simpa only [coordinateDet, fieldDet, fc, Int.cast_sub, Int.cast_mul] using hdet₂)
  have hqnot : q.1 ≠ 0 ∨ q.2 ≠ 0 := by
    rcases hq0 with hq0 | hq0
    · exact Or.inl (fun hz => hq0 (by simp only [fc, hz, Int.cast_zero]))
    · exact Or.inr (fun hz => hq0 (by simp only [fc, hz, Int.cast_zero]))
  obtain ⟨d, v₁, v₂, hd, hv, hq₁, hq₂⟩ := Int.exists_gcd_one' (Int.gcd_pos_iff.mpr hqnot)
  let v : Coordinate := (v₁, v₂)
  have hqform : q = ((d : ℤ)*v.1, (d : ℤ)*v.2) :=
    Prod.ext (hq₁.trans (mul_comm _ _)) (hq₂.trans (mul_comm _ _))
  have hdir (z : Coordinate) (hz : coordinateDet q z = 0) :
      ∃ m : ℤ, z = (m*v.1, m*v.2) := by
    apply primitive_direction_scalar v z hv
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    apply (mul_eq_zero.mp (show (d : ℤ)*coordinateDet v z = 0 by
      rw [hqform] at hz
      dsimp only [coordinateDet] at hz ⊢
      linear_combination hz)).resolve_left hd0
  obtain ⟨a, hba⟩ := hdir base.1 haligned.1
  obtain ⟨b, hbb⟩ := hdir base.2 haligned.2
  obtain ⟨m, hem⟩ := hdir e.1 he₁aligned
  obtain ⟨n, hen⟩ := hdir e.2 he₂aligned
  have hbaseform : base = ((a*v.1, a*v.2), (b*v.1, b*v.2)) := Prod.ext hba hbb
  have heform : e = ((m*v.1, m*v.2), (n*v.1, n*v.2)) := Prod.ext hem hen
  have hLoriginal := hu.1
  have hroot := original_pencil_root a₁ a₂ ha₁ ha₂ R V q base e hr ht hbase hword
  rw [hqform, hbaseform] at hLoriginal
  rw [hqform, hbaseform, heform] at hroot ⊢
  apply primitive_line_pencil_zero J₁ hJ₁ (by exact_mod_cast hcube) v (d : ℤ) a b m n
    (primitive_scalar_height h₁₂ v hv (d : ℤ) (by simpa only [hqform] using hq))
    (primitive_scalar_height h₁₂ v hv a (by simpa only [hba] using hb₁))
    (primitive_scalar_height h₁₂ v hv b (by simpa only [hbb] using hb₂))
    (primitive_scalar_height h₁₂ v hv m (by simpa only [hem] using he₁))
    (primitive_scalar_height h₁₂ v hv n (by simpa only [hen] using he₂))
    βc hLoriginal hroot

/-- For an exactly aligned retained original baseline, the entire zero-reduction
stratum consists of identically zero integer pencils. Its actual ordered
partners have a uniform subpower count without a rational-fiber weight. -/
theorem actual_aligned_zero_reduction_partners_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ M X Y : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)))
      (hw : IsUnit (w : ZMod (p^3))),
      physical B.R B.V q = (-w, -t) →
      2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) → J₂ ≤ J₁ → 1 ≤ J₂ →
      WordSolution (p^3) a₁ a₂ B.R B.V q base →
      IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      Aligned q base → CoordinateBound J₁ J₂ q →
      CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ S, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (∀ e ∈ S, (pencil q base e).map (Int.castRingHom (ZMod p)) = 0) →
      (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε := by
  obtain ⟨C, hC, hzero⟩ := actual_zero_polynomial_partners_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ M X Y t w B a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hanchor hXsmall hYsmall h₁₂ h₂ hbase hx hy hk haligned hq hb₁ hb₂
    hS hword hbox hred hcap hlarge
  have hanchorunit : IsUnit ((physical B.R B.V q).1 : ZMod (p^3)) := by
    simpa only [hanchor, Int.cast_neg] using hw.neg
  apply hzero p hp J₁ J₂ M X Y t w B a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hXsmall hYsmall h₁₂ h₂ hbase hx hy hk hq hb₁ hb₂ hbox ?_ hcap hlarge
  intro e he
  exact actual_aligned_modular_zero_pencil p hp J₁ J₂ M a₁ a₂ ha₁ ha₂ B.R B.V q base e
    hr ht hanchorunit hbase hx hy hk h₁₂ h₂ haligned hq hb₁ hb₂
    (hS e he).1 (hS e he).2 (hword e he) (hred e he) hcap hlarge

/-- All actual original zero-reduction partners have a uniform subpower count.
This includes both identically zero pencils and nonzero content-p pencils,
with no nonalignment premise on the retained original baseline. -/
theorem actual_zero_reduction_partners_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ M X Y : ℝ) (t w : ℤ)
      (B : MiddleBasis (p^3) t w)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (B.R.1 : ZMod (p^3)))
      (ht : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)))
      (hw : IsUnit (w : ZMod (p^3))),
      physical B.R B.V q = (-w, -t) →
      2*X < (p^3 : ℕ) → 2*Y < (p^3 : ℕ) → J₂ ≤ J₁ → 1 ≤ J₂ →
      WordSolution (p^3) a₁ a₂ B.R B.V q base →
      IsUnit ((physical B.R B.V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical B.R B.V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical B.R B.V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q → CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ S, WordSolution (p^3) a₁ a₂ B.R B.V q e) →
      (∀ e ∈ S, physical B.R B.V e.1 ∈ literalBox X Y ∧
        physical B.R B.V e.2 ∈ literalBox X Y) →
      (∀ e ∈ S, (pencil q base e).map (Int.castRingHom (ZMod p)) = 0) →
      (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      (S.card : ℝ) ≤ C*(p : ℝ)^ε := by
  classical
  obtain ⟨C₁, hC₁, haligned⟩ := actual_aligned_zero_reduction_partners_subpower ε hε
  obtain ⟨C₂, hC₂, hnonaligned⟩ := original_modular_zero_partner_subpower ε hε
  refine ⟨C₁+C₂, by positivity, ?_⟩
  intro p hp J₁ J₂ M X Y t w B a₁ a₂ ha₁ ha₂ q base S hr ht hw
    hanchor hXsmall hYsmall h₁₂ h₂ hbase hx hy hk hq hb₁ hb₂
    hS hword hbox hred hcap hlarge
  have hpow : 0 ≤ (p : ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases ha : Aligned q base
  · exact (haligned p hp J₁ J₂ M X Y t w B a₁ a₂ ha₁ ha₂ q base S hr ht hw
      hanchor hXsmall hYsmall h₁₂ h₂ hbase hx hy hk ha hq hb₁ hb₂
      hS hword hbox hred hcap hlarge).trans
        (mul_le_mul_of_nonneg_right (by linarith : C₁ ≤ C₁+C₂) hpow)
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let E := (S.image Prod.fst ∪ S.image Prod.snd) ∪ {base.1, base.2}
  have hE (z : Coordinate) (hz : z ∈ E) : CoordinateBound J₁ J₂ z := by
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        exact (hS e he).1
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        exact (hS e he).2
    · rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hb₁
      · simpa only [Finset.mem_singleton.mp hz] using hb₂
  have hfirst (e : Endpoint) (he : e ∈ S) : e.1 ∈ E :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨e, he, rfl⟩))))
  have hsecond (e : Endpoint) (he : e ∈ S) : e.2 ∈ E :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨e, he, rfl⟩))))
  have hsmall := (original_small_determinants p hp J₁ J₂ M h₁₂ h₂ hcap hlarge).1
  have hcount := hnonaligned p hp (p^3) (pow_ne_zero _ hp.ne_zero)
    (dvd_pow_self p (by decide : 3 ≠ 0)) J₁ J₂ E a₁ a₂ ha₁ ha₂ B.R B.V
    q base.1 base.2 hr ht (h₂.trans h₁₂) h₂ (by simp [E]) (by simp [E])
    hbase hx hy hk ha hq hE hsmall
  let reduction : ZMod (p^3) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  let βc := (B.V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let αc : ZMod (p^3) := -(↑((ha₁.unit*ha₂.unit*ht.unit*hr.unit)⁻¹) : ZMod (p^3))
  let α := reduction αc
  let β := reduction βc
  have hactual (e : Endpoint) (he : e ∈ S) : ActualPair E α β q e := by
    refine ⟨hfirst e he, hsecond e he, ?_⟩
    have hid := original_endpoint_identity a₁ a₂ ha₁ ha₂ B.R B.V q e hr ht (hword e he)
    have hidp := congrArg reduction hid
    simp only [map_add, map_mul, map_zero, Polynomial.ringHom_eval₂_intCastRingHom] at hidp
    simp only [← map_mul reduction] at hidp
    change α*(endpointL q e).eval₂ (Int.castRingHom (ZMod p)) β+
      (endpointQ e).eval₂ (Int.castRingHom (ZMod p)) β = 0 at hidp
    simp only [endpointL, endpointQ, PrimeCube.linear, PrimeCube.quadratic,
      coeffL, coeffM, coeffQ, coeffR, coeffS, eval₂_add, eval₂_mul, eval₂_pow,
      eval₂_C, eval₂_X, Int.coe_castRingHom, Int.cast_add, Int.cast_sub, Int.cast_mul] at hidp
    dsimp only [actualValue]
    linear_combination hidp
  have hsubset : S ⊆ modularZeroPartners E α β q base := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hfirst e he, hsecond e he⟩,
      hactual e he, hred e he⟩
  have hSbound : (S.card : ℝ) ≤ C₂*(p : ℝ)^ε := by
    exact (show (S.card : ℝ) ≤ (modularZeroPartners E α β q base).card by
      exact_mod_cast Finset.card_le_card hsubset).trans hcount
  exact hSbound.trans (mul_le_mul_of_nonneg_right (by linarith : C₂ ≤ C₁+C₂) hpow)

end
end D5.S3.Arith.CharacterSums.Original
