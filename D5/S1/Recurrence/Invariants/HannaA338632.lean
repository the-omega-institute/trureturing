/- GID: D5/S1/Recurrence/Invariants/HannaA338632
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA338632
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's continued-fraction coefficients are 2 modulo 4 above degree one. -/

/-
proof_shape: result: content
escape_witness: ft_stable (finite-tail depth stabilization on the construction path to result)
admission_basis: open-problem-resolution (#18983; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19167 (result).
Direct owner dependencies (owner frozen on the protected baseline; declaration statement_id from the scoped Lean report): D5/S1/Recurrence/Residue/ContinuedFractionOddSquare + D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.Agree + sha256:0cfab65b024a4c7d2f5bc7d6e6be07138094ddfd564eb763453963e9a8086943; D5/S1/Recurrence/Residue/ContinuedFractionOddSquare + D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.agree_inv + sha256:de19fffc8f3d74728f66568fc7247763986c9362a7f4436c196537010031ee4d; D5/S1/Recurrence/Residue/ContinuedFractionOddSquare + D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.agree_shift + sha256:040592024b1ac8963c332701aedb81aacbd6f1368fb796796da87d31381d9c90; D5/S1/Recurrence/Residue/ContinuedFractionOddSquare + D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.map_inverse + sha256:514cac370bcaca2ab772ee68d2f70f9768dcdff53acb4e2a4df3e5420df06e90; D5/S1/Recurrence/Residue/ContinuedFractionOddSquare + D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.inverse_one + sha256:8ca570fd0828804ac28c81ca1d9d398e6ba7713278e53cc37fc6ceef601ca498
The public surface consists of the source definitions tail, IsGF, claim and the settling result; all auxiliary declarations are private and consumed by the result proof.
The claim keeps the preregistered finite-tail convention literally inlined; the proof uses the existing generic agreement owner through a compiled correspondence.
-/

import D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaA338632

open PowerSeries

/-- The finite tails of the continued fraction of OEIS A338632:
`tail A j 0 = A` and `tail A j (r + 1) = A − (2j + 1)·x / tail A (j + 1) r`. -/
noncomputable def tail (A : PowerSeries ℚ) : ℕ → ℕ → PowerSeries ℚ
  | _, 0 => A
  | j, r + 1 => A - ((2 * j + 1 : ℚ) • X) * (tail A (j + 1) r)⁻¹

/-- OEIS A338632: "G.f. A(x) satisfies: 1 = A(x) - x/(A(x) - 3*x/(A(x) - 5*x/(A(x) - 7*x/(A(x) -
9*x/(A(x) - ...))))), a continued fraction relation." The continued fraction is the coefficientwise
limit of its finite truncations: every coefficient of `tail A 0 r` equals that of `1` for all large `r`. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → coeff n (tail A 0 r) = coeff n (1 : PowerSeries ℚ)

/-- OEIS A338632 (P. D. Hanna), conjecture: "a(n) = 2 (mod 4) for n > 1", where a(n) = [x^n] A(x)
(offset 0). The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧ ∀ A, IsGF A → ∀ n : ℕ, 2 ≤ n → ∃ m : ℤ, coeff n A = m ∧ m % 4 = 2

end D5.S1.Recurrence.Invariants.HannaA338632

namespace D5.S1.Recurrence.Invariants.HannaA338632

open D5.S1.Recurrence.Residue.ContinuedFractionOddSquare

open PowerSeries
variable {R : Type*} [CommRing R]

private noncomputable def ft (A : PowerSeries R) : ℕ → ℕ → PowerSeries R
  | _, 0 => A
  | j, d+1 => A - C ((2*j+1 : ℕ) : R) * X * invOfUnit (ft A (j+1) d) 1

private theorem ft_const (A : PowerSeries R) (j d : ℕ) :
    constantCoeff (ft A j d) = constantCoeff A := by
    cases d <;> simp [ft]

private theorem ft_agree {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) (j d : ℕ) : Agree n (ft A j d) (ft B j d) := by
    induction d generalizing j with
    | zero => exact h
    | succ d ih =>
      have hi := agree_shift (agree_inv
        ((ft_const _ _ _).trans hA) ((ft_const _ _ _).trans hB)
        (ih (j+1))) ((2*j+1 : ℕ) : R)
      intro k hk
      simp only [ft, map_sub]
      rw [h k hk, hi k (by omega)]

private theorem ft_stable (A : PowerSeries R) (hA : constantCoeff A = 1)
    {d e : ℕ} (hde : d ≤ e) (j : ℕ) : Agree (d+1) (ft A j d) (ft A j e) := by
    induction d generalizing j e with
    | zero =>
      intro k hk
      have : k = 0 := Nat.lt_one_iff.mp hk
      subst k
      simp [coeff_zero_eq_constantCoeff, ft_const]
    | succ d ih =>
      cases e with
      | zero => omega
      | succ e =>
        have hi := agree_shift (agree_inv
          ((ft_const _ _ _).trans hA) ((ft_const _ _ _).trans hA)
          (ih (e := e) (j := j+1) (by omega))) ((2*j+1 : ℕ) : R)
        intro k hk
        simp only [ft, map_sub]
        rw [hi k hk]

private noncomputable def lt (A : PowerSeries R) (j : ℕ) : PowerSeries R :=
  mk fun n => coeff n (ft A j n)

private theorem lt_agree (A : PowerSeries R) (hA : constantCoeff A = 1) (j d : ℕ) :
    Agree (d+1) (lt A j) (ft A j d) := by
    intro n hn
    simp only [lt, coeff_mk]
    exact ft_stable A hA (by omega : n ≤ d) j n (by omega)

private theorem lt_const (A : PowerSeries R) (j : ℕ) :
    constantCoeff (lt A j) = constantCoeff A := by
    simp [lt, ← coeff_zero_eq_constantCoeff, ft]

private theorem lt_congr {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) (j : ℕ) : Agree n (lt A j) (lt B j) := by
    intro k hk
    simp only [lt, coeff_mk]
    exact ft_agree hA hB h j k k hk

private theorem lt_eq (A : PowerSeries R) (hA : constantCoeff A = 1) (j : ℕ) :
    lt A j = A - C ((2*j+1 : ℕ) : R) * X * invOfUnit (lt A (j+1)) 1 := by
    ext n
    have hi := agree_shift (agree_inv
      ((lt_const _ _).trans hA) ((ft_const _ _ _).trans hA)
      (lt_agree A hA (j+1) n)) ((2*j+1 : ℕ) : R)
    have he := lt_agree A hA j (n+1) n (by omega)
    simp only [ft, map_sub] at he ⊢
    rw [hi n (by omega)]
    exact he

private noncomputable def phi (A : PowerSeries R) : PowerSeries R :=
  1 + X * invOfUnit (lt A 1) 1

private theorem phi_const (A : PowerSeries R) : constantCoeff (phi A) = 1 := by
    simp [phi]

private theorem phi_agree {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) : Agree (n+1) (phi A) (phi B) := by
    have hi := agree_shift (agree_inv
      ((lt_const _ _).trans hA) ((lt_const _ _).trans hB)
      (lt_congr hA hB h 1)) 1
    intro k hk
    simpa only [phi, map_add, map_one, one_mul] using
      congrArg (coeff k (1 : PowerSeries R) + ·) (hi k hk)

private noncomputable def approx : ℕ → PowerSeries R
  | 0 => 1
  | n+1 => phi (approx n)

private theorem approx_const (n : ℕ) : constantCoeff (approx (R := R) n) = 1 := by
    cases n
    · simp [approx]
    · exact phi_const _

private theorem approx_stable {d e : ℕ} (hde : d ≤ e) :
    Agree (d+1) (approx (R := R) d) (approx e) := by
    induction d generalizing e with
    | zero =>
      intro k hk
      have : k = 0 := Nat.lt_one_iff.mp hk
      subst k
      simp [coeff_zero_eq_constantCoeff, approx_const]
    | succ d ih =>
      cases e with
      | zero => omega
      | succ e => exact phi_agree (approx_const d) (approx_const e) (ih (e := e) (by omega))

private noncomputable def sol : PowerSeries R := mk fun n => coeff n (approx n)

private theorem sol_agree (d : ℕ) : Agree (d+1) (sol (R := R)) (approx d) := by
    intro k hk
    simpa only [sol, coeff_mk] using
      approx_stable (R := R) (by omega : k ≤ d) k (by omega)

private theorem sol_const : constantCoeff (sol (R := R)) = 1 := by
    simpa only [coeff_zero_eq_constantCoeff, approx_const] using
      sol_agree (R := R) 0 0 (by omega)

private theorem sol_fixed : sol (R := R) = phi sol := by
    ext k
    exact (sol_agree (k+1) k (by omega)).trans
      (phi_agree sol_const (approx_const k) (sol_agree k) k (by omega)).symm

private theorem fixed_unique {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (fA : A = phi A) (fB : B = phi B) : A = B := by
    have h : ∀ n, Agree n A B := by
      intro n
      induction n with
      | zero => intro k hk; omega
      | succ n ih => simpa only [← fA, ← fB] using phi_agree hA hB ih
    ext n
    exact h (n+1) n (by omega)

private theorem map_ft {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) (j d : ℕ) :
    (ft A j d).map hom = ft (A.map hom) j d := by
    induction d generalizing j with
    | zero => rfl
    | succ d ih =>
      simp only [ft, map_sub, map_mul, map_X, map_natCast]
      rw [map_inverse hom _ ((ft_const _ _ _).trans hA), ih]

private theorem map_lt {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) (j : ℕ) :
    (lt A j).map hom = lt (A.map hom) j := by
    ext n
    simp only [coeff_map, lt, coeff_mk]
    rw [← coeff_map, map_ft hom A hA]

private theorem map_phi {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) :
    (phi A).map hom = phi (A.map hom) := by
    simp only [phi, map_add, map_one, map_mul, map_X]
    rw [map_inverse hom _ ((lt_const _ _).trans hA), map_lt hom A hA]

private theorem map_sol {S : Type*} [CommRing S] (hom : R →+* S) :
    (sol (R := R)).map hom = sol (R := S) := by
    apply fixed_unique
      (by rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
              sol_const, map_one]) sol_const
    · rw [← map_phi hom sol sol_const, ← sol_fixed]
    · exact sol_fixed

private theorem rat_tail_const (A : PowerSeries ℚ) (j d : ℕ) :
    constantCoeff (tail A j d) = constantCoeff A := by
    cases d <;> simp [tail]

private theorem gf_const (A : PowerSeries ℚ) (h : IsGF A) : constantCoeff A = 1 := by
    obtain ⟨r, hr⟩ := h 0
    have he := hr r (le_refl r)
    simpa [coeff_zero_eq_constantCoeff, rat_tail_const] using he

private theorem ft_rat (A : PowerSeries ℚ) (hA : constantCoeff A = 1) (j d : ℕ) :
    ft A j d = tail A j d := by
    induction d generalizing j with
    | zero => rfl
    | succ d ih =>
      rw [ft, tail, ← ih (j+1),
        invOfUnit_eq' _ 1 ((ft_const _ _ _).trans hA), smul_eq_C_mul]
      push_cast <;> rfl

private theorem gf_iff_limit (A : PowerSeries ℚ) (hA : constantCoeff A = 1) :
    IsGF A ↔ lt A 0 = 1 := by
    constructor
    · intro h
      ext n
      obtain ⟨r, hr⟩ := h n
      have he := lt_agree A hA 0 (max r n) n (by omega)
      rw [ft_rat A hA] at he
      exact he.trans (hr _ (by omega))
    · intro h n
      refine ⟨n, fun r hr => ?_⟩
      have he := lt_agree A hA 0 r n (by omega)
      rw [h, ft_rat A hA] at he
      exact he.symm

private theorem limit_iff_fixed (A : PowerSeries R) (hA : constantCoeff A = 1) :
    lt A 0 = 1 ↔ A = phi A := by
    have he := lt_eq A hA 0
    simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, map_one, one_mul] at he
    dsimp [phi]
    constructor
    · intro h
      linear_combination -he + h
    · intro h
      linear_combination he + h

private theorem gf_sol : IsGF (sol (R := ℚ)) := by
    rw [gf_iff_limit _ sol_const, limit_iff_fixed _ sol_const]
    exact sol_fixed

private theorem gf_unique (A : PowerSeries ℚ) (h : IsGF A) : A = sol (R := ℚ) := by
    have hA := gf_const A h
    have hf := (limit_iff_fixed A hA).mp ((gf_iff_limit A hA).mp h)
    exact fixed_unique hA sol_const hf sol_fixed

private theorem ft_period (A : PowerSeries (ZMod 4)) (j d : ℕ) :
    ft A (j+2) d = ft A j d := by
    induction d generalizing j with
    | zero => rfl
    | succ d ih =>
      rw [ft, ft, show j+2+1 = (j+1)+2 by omega, ih]
      have hc : (((2*(j+2)+1 : ℕ) : ZMod 4)) = ((2*j+1 : ℕ) : ZMod 4) := by
        push_cast
        have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
        linear_combination h4
      rw [hc]

private theorem lt_period (A : PowerSeries (ZMod 4)) (j : ℕ) : lt A (j+2) = lt A j := by
    ext n
    simp only [lt, coeff_mk, ft_period]

private theorem reduced_quad :
    (sol (R := ZMod 4)) ^ 2 - (1+3*X) * sol + 2*X = 0 := by
    let A := sol (R := ZMod 4)
    have hA : constantCoeff A = 1 := sol_const
    have h0 : lt A 0 = 1 := (limit_iff_fixed A hA).mpr sol_fixed
    have he0 := lt_eq A hA 0
    have he1 := lt_eq A hA 1
    have h2 : lt A 2 = 1 := (lt_period A 0).trans h0
    have hv : lt A 1 = A - 3*X := by
      norm_num [h2, inverse_one] at he1
      exact he1
    have he : (A-1) * (lt A 1) = X := by
      have hh : A-1 = X * invOfUnit (lt A 1) 1 := by
        simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, map_one, one_mul, h0] at he0
        linear_combination -he0
      rw [hh, mul_assoc,
        invOfUnit_mul _ 1 ((lt_const A 1).trans hA), mul_one]
    rw [hv] at he
    change A ^ 2 - (1+3*X)*A + 2*X = 0
    linear_combination he

private noncomputable def closed : PowerSeries (ZMod 4) :=
  (1 + X^2) * (mk 1 : PowerSeries (ZMod 4))

private theorem closed_const : constantCoeff closed = 1 := by
    simp [closed]

private theorem closed_quad : closed ^ 2 - (1+3*X) * closed + 2*X = 0 := by
    have hb : closed * (1-X) = 1+X^2 := by
      dsimp [closed]
      rw [mul_assoc, mk_one_mul_one_sub_eq_one (ZMod 4), mul_one]
    have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
      rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 from ZMod.natCast_self 4, map_zero]
    have hu : IsUnit ((1-X : PowerSeries (ZMod 4)) ^ 2) := by
      apply IsUnit.pow
      apply isUnit_iff_constantCoeff.mpr
      simp
    apply hu.mul_right_cancel
    simp only [zero_mul]
    linear_combination
      (closed*(1-X)+(1+X^2)-(1+3*X)*(1-X)) * hb + X^4*h4

private theorem reduced_closed : sol (R := ZMod 4) = closed := by
    have hu : IsUnit (sol (R := ZMod 4) + closed - 1 - 3*X) := by
      apply isUnit_iff_constantCoeff.mpr
      simp [sol_const, closed_const]
    have he : (sol (R := ZMod 4)-closed) * (sol + closed - 1 - 3*X) = 0 := by
      linear_combination reduced_quad - closed_quad
    apply sub_eq_zero.mp
    apply hu.mul_right_cancel
    simpa only [zero_mul] using he

private theorem closed_coeff (n : ℕ) (hn : 2 ≤ n) : coeff n closed = 2 := by
    simp only [closed, add_mul, one_mul, map_add, coeff_X_pow_mul', ite_eq_left hn, coeff_mk, Pi.one_apply] <;> norm_num

theorem result : claim := by
    refine ⟨⟨sol (R := ℚ), gf_sol⟩, ?_⟩
    intro A hA n hn
    refine ⟨coeff n (sol (R := ℤ)), ?_, ?_⟩
    · rw [gf_unique A hA, ← map_sol (Int.castRingHom ℚ), coeff_map]
      all_goals rfl
    · have he := congrArg (coeff n) (map_sol (Int.castRingHom (ZMod 4)))
      rw [reduced_closed, closed_coeff n hn, coeff_map] at he
      exact (ZMod.intCast_eq_intCast_iff' (coeff n (sol (R := ℤ))) 2 4).mp he


end D5.S1.Recurrence.Invariants.HannaA338632
