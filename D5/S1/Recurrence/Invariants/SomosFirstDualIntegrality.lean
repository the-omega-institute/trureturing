/- GID: D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SomosFirstDualIntegrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: First dual Somos orbit shadows are integral exactly when p equals one. -/

import Mathlib.Algebra.DualNumber
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

/-! Integer shadows of the first non-homogeneous dual Somos recurrence.

The source is Corollary 5.2(i) and its following conjecture in
Ovsienko–Tabachnikov, arXiv:1705.01623v1, §5.4.
The arbitrary leading shadows are indexed from zero.
The proof uses an elementary quotient-ring divisibility criterion. -/

/-
admission_basis: escape-witness
escape_witness: integral_orbit_of_zero_obstruction
proof_shape: result: content
The zero-obstruction theorem constructs integer representatives for every
index by strong induction. Each step uses the local quotient criterion and
only previously constructed integer terms; real coprimality is propagated
from the earlier exchange equations. The full result consumes this witness.
All other declarations are definitions or consumed proof helpers; none is
an independent finite-instance or enumeration deliverable.

The p=1 sufficient direction is published prior work. No exact frozen D5 or
pinned Mathlib recurrence theorem supplies the full assertion. The inspected
external ClusterAlgebras Laurent supplier retains four unproved proposition
arguments and is not imported. Mathlib's dual-number algebra, ideal quotient,
Bezout coprimality and Nat.mul_le_pow are reused directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality

open TrivSqZeroExt

private theorem exchange_unit_identity {R : Type*} [CommRing R]
    (b c d f g h t : Rˣ) (p q : ℕ)
    (hf : b * f = t * d ^ q)
    (hg : c * g = (f * d) ^ p)
    (hh : d * h = t * f ^ q) :
    t ^ (2 * p) * (t * g ^ q) =
      t * (b * d) ^ p * (c ^ q)⁻¹ * (h * f) ^ p := by
  have hf' : f = b⁻¹ * (t * d ^ q) := by rw [← hf]; simp
  have hg' : g = c⁻¹ * (f * d) ^ p := by rw [← hg]; simp
  have hh' : h = d⁻¹ * (t * f ^ q) := by rw [← hh]; simp
  rw [hh', hg', hf']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_inv]
  module

private theorem exchange_cleared_identity {R : Type*} [CommRing R]
    (b c d f g h t : Rˣ) (p q : ℕ)
    (h0 : ((b * d) ^ p : Rˣ) = -(t * c ^ q))
    (hf : b * f = t * d ^ q)
    (hg : c * g = (f * d) ^ p)
    (hh : d * h = t * f ^ q) :
    (t : R) ^ (2 * p) * (((h * f : Rˣ) : R) ^ p + (t : R) * (g : R) ^ q) =
      (((h * f : Rˣ) : R) ^ p) * ((t : R) ^ (2 * p) - (t : R) ^ 2) := by
  have he := exchange_unit_identity b c d f g h t p q hf hg hh
  rw [h0] at he
  have he' := congrArg (fun u : Rˣ => (u : R)) he
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg] at he'
  have hc : (c : R) ^ q * ↑((c ^ q)⁻¹) = 1 := by
    exact Units.mul_inv (c ^ q)
  have hx : (t : R) ^ (2 * p) * ((t : R) * (g : R) ^ q) =
      -((t : R) ^ 2 * (((h * f : Rˣ) : R) ^ p)) := by
    calc
      _ = (t : R) * -((t : R) * (c : R) ^ q) * ↑((c ^ q)⁻¹) *
          (((h * f : Rˣ) : R) ^ p) := he'
      _ = -((t : R) ^ 2 * (((h * f : Rˣ) : R) ^ p)) := by
        calc
          _ = -((t : R) ^ 2 * (((h * f : Rˣ) : R) ^ p)) *
              ((c : R) ^ q * ↑((c ^ q)⁻¹)) := by ring
          _ = _ := by rw [hc]; ring
  linear_combination hx

private theorem inr_dvd_iff (E : DualNumber ℤ) (hE : E.fst ≠ 0) (k : ℤ) :
    E ∣ inr k ↔ E.fst ∣ k := by
  constructor
  · rintro ⟨X, hX⟩
    have hr : E.fst * X.fst = 0 := by
      simpa using (congrArg (fst (R := ℤ) (M := ℤ)) hX).symm
    have hx : X.fst = 0 := (mul_eq_zero.mp hr).resolve_left hE
    refine ⟨X.snd, ?_⟩
    have hi := congrArg (snd (R := ℤ) (M := ℤ)) hX
    simpa [DualNumber.snd_mul, hx] using hi
  · rintro ⟨y, hy⟩
    refine ⟨inr y, ?_⟩
    apply TrivSqZeroExt.ext
    · simp
    · simpa [DualNumber.snd_mul] using hy

private theorem unit_mod_of_coprime {R : Type*} [CommRing R]
    (φ : DualNumber ℤ →+* R) (B E : DualNumber ℤ)
    (hE : φ E = 0) (hBE : IsCoprime B.fst E.fst) : IsUnit (φ B) := by
  obtain ⟨r, s, hrs⟩ := hBE
  have hu : IsUnit ((inl r : DualNumber ℤ) * B + inl s * E) := by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    simpa only [fst_add, fst_mul, fst_inl, hrs] using (isUnit_one : IsUnit (1 : ℤ))
  have hv := hu.map φ
  simp only [map_add, map_mul, hE, mul_zero, add_zero] at hv
  exact (IsUnit.mul_iff.mp hv).2

private theorem deformation_power_difference (p : ℕ) (v : ℤ) :
    (1 + inr v : DualNumber ℤ) ^ (2 * p) -
      (1 + inr v) ^ 2 = inr ((2 * (p : ℤ) - 2) * v) := by
  apply TrivSqZeroExt.ext
  · simp
  · simp [TrivSqZeroExt.snd_pow, show (2 : DualNumber ℤ).fst = 2 from rfl]
    ring

/-- The local obstruction depends on the real divisor, independently of all shadows. -/
private theorem local_divisibility (A B C D E F G H : DualNumber ℤ) (p q : ℕ) (v : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hE : E.fst ≠ 0)
    (hB : IsCoprime B.fst E.fst) (hC : IsCoprime C.fst E.fst)
    (hD : IsCoprime D.fst E.fst)
    (h0 : E * A = (B * D) ^ p + (1 + inr v) * C ^ q)
    (h1 : F * B = (C * E) ^ p + (1 + inr v) * D ^ q)
    (h2 : G * C = (D * F) ^ p + (1 + inr v) * E ^ q)
    (h3 : H * D = (E * G) ^ p + (1 + inr v) * F ^ q) :
    E ∣ (F * H) ^ p + (1 + inr v) * G ^ q ↔
      E.fst ∣ (2 * (p : ℤ) - 2) * v := by
  let I := Ideal.span ({E} : Set (DualNumber ℤ))
  let φ := Ideal.Quotient.mk I
  have hE0 : φ E = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self E)
  have huB := unit_mod_of_coprime φ B E hE0 hB
  have huC := unit_mod_of_coprime φ C E hE0 hC
  have huD := unit_mod_of_coprime φ D E hE0 hD
  have huT : IsUnit (φ (1 + inr v)) :=
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by simp)).map φ
  have e0 : (φ B * φ D) ^ p = -(φ (1 + inr v) * φ C ^ q) := by
    have he := congrArg φ h0
    simp only [map_mul, map_add, map_pow, hE0, zero_mul] at he
    exact eq_neg_of_add_eq_zero_left he.symm
  have e1 : φ B * φ F = φ (1 + inr v) * φ D ^ q := by
    have he := congrArg φ h1
    simpa [hE0, zero_pow (Nat.ne_of_gt hp), mul_comm] using he
  have e2 : φ C * φ G = (φ F * φ D) ^ p := by
    have he := congrArg φ h2
    simpa [hE0, zero_pow (Nat.ne_of_gt hq), mul_comm] using he
  have e3 : φ D * φ H = φ (1 + inr v) * φ F ^ q := by
    have he := congrArg φ h3
    simpa [hE0, zero_pow (Nat.ne_of_gt hp), mul_comm] using he
  have huF : IsUnit (φ F) :=
    (IsUnit.mul_iff.mp (e1.symm ▸ huT.mul (huD.pow q))).2
  have huG : IsUnit (φ G) :=
    (IsUnit.mul_iff.mp (e2.symm ▸ (huF.mul huD).pow p)).2
  have huH : IsUnit (φ H) :=
    (IsUnit.mul_iff.mp (e3.symm ▸ huT.mul (huF.pow q))).2
  let b := huB.unit
  have hb : (b : DualNumber ℤ ⧸ I) = φ B := huB.unit_spec
  let c := huC.unit
  have hc : (c : DualNumber ℤ ⧸ I) = φ C := huC.unit_spec
  let d := huD.unit
  have hd : (d : DualNumber ℤ ⧸ I) = φ D := huD.unit_spec
  let f := huF.unit
  have hf : (f : DualNumber ℤ ⧸ I) = φ F := huF.unit_spec
  let g := huG.unit
  have hg : (g : DualNumber ℤ ⧸ I) = φ G := huG.unit_spec
  let h := huH.unit
  have hh : (h : DualNumber ℤ ⧸ I) = φ H := huH.unit_spec
  let t := huT.unit
  have ht : (t : DualNumber ℤ ⧸ I) = φ (1 + inr v) := huT.unit_spec
  have he := exchange_cleared_identity b c d f g h t p q
    (Units.ext (by simpa [hb, hc, hd, ht] using e0))
    (Units.ext (by simpa [hb, hf, hd, ht] using e1))
    (Units.ext (by simpa [hc, hg, hf, hd] using e2))
    (Units.ext (by simpa [hd, hh, ht, hf] using e3))
  simp only [Units.val_mul, hf, hg, hh, ht] at he
  have hdiff : φ (1 + inr v) ^ (2 * p) -
      φ (1 + inr v) ^ 2 = φ (inr ((2 * (p : ℤ) - 2) * v)) := by
    simpa only [map_sub, map_pow] using congrArg φ (deformation_power_difference p v)
  rw [hdiff] at he
  have hzero : φ ((F * H) ^ p + (1 + inr v) * G ^ q) = 0 ↔
      φ (inr ((2 * (p : ℤ) - 2) * v)) = 0 := by
    have hu1 := huT.pow (2 * p)
    have hu2 := (huH.mul huF).pow p
    simp only [map_add, map_pow, map_mul, mul_comm (φ F) (φ H)]
    calc
      _ ↔ φ (1 + inr v) ^ (2 * p) *
          ((φ H * φ F) ^ p + φ (1 + inr v) * φ G ^ q) = 0 :=
        hu1.mul_right_eq_zero.symm
      _ ↔ (φ H * φ F) ^ p * φ (inr ((2 * (p : ℤ) - 2) * v)) = 0 := by
        rw [he]
      _ ↔ _ := hu2.mul_right_eq_zero
  calc
    _ ↔ φ ((F * H) ^ p + (1 + inr v) * G ^ q) = 0 := by
      exact (Ideal.mem_span_singleton.symm.trans Ideal.Quotient.eq_zero_iff_mem.symm)
    _ ↔ φ (inr ((2 * (p : ℤ) - 2) * v)) = 0 := hzero
    _ ↔ E ∣ inr ((2 * (p : ℤ) - 2) * v) :=
      Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
    _ ↔ _ := inr_dvd_iff E hE _

private theorem coprime_add_of_dvd {R : Type*} [CommRing R] {x y z : R}
    (h : IsCoprime x y) (hz : y ∣ z) : IsCoprime (x + z) y := by
  obtain ⟨t, rfl⟩ := hz
  exact h.add_mul_left_left t

private theorem coprime_next {R : Type*} [CommRing R] (a b c d e : R)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hbc : IsCoprime b c) (hcd : IsCoprime c d)
    (he : a * e = (b * d) ^ p + c ^ q) :
    IsCoprime b e ∧ IsCoprime c e ∧ IsCoprime d e := by
  have hb : b ∣ (b * d) ^ p := dvd_trans (dvd_mul_right b d) (dvd_pow_self _ (Nat.ne_of_gt hp))
  have hd : d ∣ (b * d) ^ p := dvd_trans (dvd_mul_left d b) (dvd_pow_self _ (Nat.ne_of_gt hp))
  have hc : c ∣ c ^ q := dvd_pow_self _ (Nat.ne_of_gt hq)
  have hNb : IsCoprime ((b * d) ^ p + c ^ q) b := by
    simpa only [add_comm] using coprime_add_of_dvd hbc.symm.pow_left hb
  have hNc : IsCoprime ((b * d) ^ p + c ^ q) c :=
    coprime_add_of_dvd (hbc.mul_left hcd.symm).pow_left hc
  have hNd : IsCoprime ((b * d) ^ p + c ^ q) d := by
    simpa only [add_comm] using coprime_add_of_dvd hcd.pow_left hd
  rw [← he] at hNb hNc hNd
  exact ⟨hNb.of_mul_left_right.symm, hNc.of_mul_left_right.symm,
    hNd.of_mul_left_right.symm⟩

/-- Coefficientwise inclusion of integer dual numbers in rational dual numbers. -/
private def integerCast : DualNumber ℤ →+* DualNumber ℚ where
  toFun x := inl (x.fst : ℚ) + inr (x.snd : ℚ)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private theorem integerCast_injective : Function.Injective integerCast := by
  intro x y h
  apply TrivSqZeroExt.ext
  · have h' := congrArg (fst (R := ℚ) (M := ℚ)) h
    simpa [integerCast] using h'
  · have h' := congrArg (snd (R := ℚ) (M := ℚ)) h
    simpa [integerCast] using h'

/-- The total forward orbit uses the canonical inverse of a rational dual number. -/
private noncomputable def orbit (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ) (n : ℕ) : DualNumber ℚ :=
  if hn : n < 4 then 1 + inr (c ⟨n, hn⟩ : ℚ) else
    (((orbit p q v c (n - 4 + 1) * orbit p q v c (n - 4 + 3)) ^ p +
      (1 + inr (v : ℚ)) * orbit p q v c (n - 4 + 2) ^ q) *
      (orbit p q v c (n - 4))⁻¹)
termination_by n
decreasing_by all_goals omega

private theorem orbit_initial (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ) (i : Fin 4) :
    orbit p q v c i = 1 + inr (c i : ℚ) := by
  rw [orbit, dite_eq_left i.isLt]

private theorem orbit_step (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ) (n : ℕ) :
    orbit p q v c (n + 4) =
      ((orbit p q v c (n + 1) * orbit p q v c (n + 3)) ^ p +
        (1 + inr (v : ℚ)) * orbit p q v c (n + 2) ^ q) * (orbit p q v c n)⁻¹ := by
  rw [orbit, dite_eq_right (by omega)]
  simp only [Nat.add_sub_cancel]

/-- Positivity follows from the specified initial real parts and positive summands. -/
private theorem orbit_positive (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ) (n : ℕ) :
    0 < (orbit p q v c n).fst := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · rw [orbit, dite_eq_left hn]
      simp
    · have h0 := ih (n - 4) (by omega)
      have h1 := ih (n - 4 + 1) (by omega)
      have h2 := ih (n - 4 + 2) (by omega)
      have h3 := ih (n - 4 + 3) (by omega)
      rw [orbit, dite_eq_right hn]
      simp only [fst_mul, fst_add, fst_pow, fst_inv, fst_one, fst_inr,
        add_zero, one_mul]
      exact mul_pos (add_pos (pow_pos (mul_pos h1 h3) _) (pow_pos h2 _)) (inv_pos.mpr h0)

/-- Exchange equations hold without additional nonvanishing assumptions. -/
private theorem orbit_exchange (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ) (n : ℕ) :
    orbit p q v c (n + 4) * orbit p q v c n =
      (orbit p q v c (n + 1) * orbit p q v c (n + 3)) ^ p +
        (1 + inr (v : ℚ)) * orbit p q v c (n + 2) ^ q := by
  rw [orbit_step]
  have hi := TrivSqZeroExt.mul_inv_cancel (ne_of_gt (orbit_positive p q v c n))
  calc
    _ = ((orbit p q v c (n + 1) * orbit p q v c (n + 3)) ^ p +
        (1 + inr (v : ℚ)) * orbit p q v c (n + 2) ^ q) *
        (orbit p q v c n * (orbit p q v c n)⁻¹) := by ring
    _ = _ := by rw [hi, mul_one]

private def CoprimeWindow (a : ℕ → ℤ) (n : ℕ) : Prop :=
  IsCoprime (a n) (a (n + 1)) ∧ IsCoprime (a n) (a (n + 2)) ∧
  IsCoprime (a n) (a (n + 3)) ∧ IsCoprime (a (n + 1)) (a (n + 2)) ∧
  IsCoprime (a (n + 1)) (a (n + 3)) ∧ IsCoprime (a (n + 2)) (a (n + 3))

private theorem coprime_windows (a : ℕ → ℤ) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ha : ∀ i < 4, a i = 1) (n : ℕ)
    (hex : ∀ k < n, a (k + 4) * a k = (a (k + 1) * a (k + 3)) ^ p + a (k + 2) ^ q) :
    CoprimeWindow a n := by
  induction n with
  | zero => simp [CoprimeWindow, ha, isCoprime_one_left]
  | succ n ih =>
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ih (fun k hk => hex k (by omega))
    have he : a n * a (n + 4) = (a (n + 1) * a (n + 3)) ^ p + a (n + 2) ^ q := by
      simpa [mul_comm] using hex n (by omega)
    obtain ⟨hbe, hce, hde⟩ := coprime_next _ _ _ _ _ p q hp hq hbc hcd he
    simpa only [CoprimeWindow, Nat.add_assoc, Nat.succ_eq_add_one] using
      (show IsCoprime (a (n + 1)) (a (n + 2)) ∧
        IsCoprime (a (n + 1)) (a (n + 3)) ∧ IsCoprime (a (n + 1)) (a (n + 4)) ∧
        IsCoprime (a (n + 2)) (a (n + 3)) ∧ IsCoprime (a (n + 2)) (a (n + 4)) ∧
        IsCoprime (a (n + 3)) (a (n + 4)) from ⟨hbc, hbd, hbe, hcd, hce, hde⟩)

/-- Integral means membership in the coefficientwise image of the integer duals. -/
private def Integral (x : DualNumber ℚ) : Prop := ∃ z : DualNumber ℤ, integerCast z = x

private theorem integral_of_divides (X : DualNumber ℚ) (E N : DualNumber ℤ)
    (hE : (integerCast E).fst ≠ 0) (hX : X * integerCast E = integerCast N)
    (hdiv : E ∣ N) : Integral X := by
  obtain ⟨W, hW⟩ := hdiv
  refine ⟨W, ?_⟩
  have hu : IsUnit (integerCast E) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hE)
  apply hu.mul_right_cancel
  rw [hX, hW, map_mul, mul_comm]

private theorem prefix_exchange (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ)
    (z : ℕ → DualNumber ℤ) (N : ℕ)
    (hz : ∀ i < N, integerCast (z i) = orbit p q v c i) (k : ℕ) (hk : k + 4 < N) :
    z (k + 4) * z k = (z (k + 1) * z (k + 3)) ^ p + (1 + inr v) * z (k + 2) ^ q := by
  apply integerCast_injective
  simp only [map_mul, map_add, map_pow, map_one]
  have hv : integerCast (inr v) = inr (v : ℚ) := by ext <;> simp [integerCast]
  rw [hv, hz _ hk, hz _ (by omega), hz _ (by omega), hz _ (by omega), hz _ (by omega)]
  exact orbit_exchange p q v c k

private theorem prefix_coprime (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ)
    (hp : 0 < p) (hq : 0 < q) (z : ℕ → DualNumber ℤ) (N : ℕ)
    (hz : ∀ i < N, integerCast (z i) = orbit p q v c i)
    (n : ℕ) (hn : n + 3 < N) : CoprimeWindow (fun i => (z i).fst) n := by
  apply coprime_windows _ p q hp hq
  · intro i hi
    have he := congrArg (fst (R := ℚ) (M := ℚ)) (hz i (by omega))
    rw [orbit_initial p q v c ⟨i, hi⟩] at he
    simpa [integerCast] using he
  · intro k hk
    have he := congrArg (fst (R := ℤ) (M := ℤ))
      (prefix_exchange p q v c z N hz k (by omega))
    simpa using he

private theorem integral_next (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ)
    (hp : 0 < p) (hq : 0 < q) (hkappa : (2 * (p : ℤ) - 2) * v = 0)
    (n : ℕ) (hprefix : ∀ i < n + 4, Integral (orbit p q v c i)) :
    Integral (orbit p q v c (n + 4)) := by
  classical
  let z : ℕ → DualNumber ℤ := fun i => if hi : i < n + 4 then
    (hprefix i hi).choose else 0
  have hz : ∀ i < n + 4, integerCast (z i) = orbit p q v c i := by
    intro i hi
    simpa only [z, dite_eq_left hi] using (hprefix i hi).choose_spec
  let N : DualNumber ℤ := (z (n + 1) * z (n + 3)) ^ p +
    (1 + inr v) * z (n + 2) ^ q
  have hmap : orbit p q v c (n + 4) * integerCast (z n) = integerCast N := by
    simp only [N, map_add, map_mul, map_pow, map_one]
    have hv : integerCast (inr v) = inr (v : ℚ) := by ext <;> simp [integerCast]
    rw [hv, hz _ (by omega), hz _ (by omega), hz _ (by omega), hz _ (by omega)]
    exact orbit_exchange p q v c n
  apply integral_of_divides _ (z n) N
  · rw [hz _ (by omega)]
    exact ne_of_gt (orbit_positive p q v c n)
  · exact hmap
  · by_cases hn : n < 4
    · have he := congrArg (fst (R := ℚ) (M := ℚ)) (hz n (by omega))
      rw [orbit_initial p q v c ⟨n, hn⟩] at he
      have hreal : (z n).fst = 1 := by simpa [integerCast] using he
      have hu : IsUnit (z n) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (hreal ▸ isUnit_one)
      exact hu.dvd
    · have hn4 : 4 ≤ n := by omega
      let k := n - 4
      have hkn : k + 4 = n := by omega
      have hw := prefix_coprime p q v c hp hq z (n + 4) hz
        (k + 1) (by omega)
      obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hw
      have hre : (z (k + 4)).fst ≠ 0 := by
        have he := congrArg (fst (R := ℚ) (M := ℚ)) (hz (k + 4) (by omega))
        have ho := ne_of_gt (orbit_positive p q v c (k + 4))
        intro hf
        apply ho
        rw [← he]
        simp [integerCast, hf]
      have he0 := prefix_exchange p q v c z (n + 4) hz k (by omega)
      have he1 := prefix_exchange p q v c z (n + 4) hz (k + 1) (by omega)
      have he2 := prefix_exchange p q v c z (n + 4) hz (k + 2) (by omega)
      have he3 := prefix_exchange p q v c z (n + 4) hz (k + 3) (by omega)
      have hd := (local_divisibility (z k) (z (k + 1)) (z (k + 2)) (z (k + 3))
        (z (k + 4)) (z (k + 5)) (z (k + 6)) (z (k + 7)) p q v hp hq hre
        (by simpa only [Nat.add_assoc] using had)
        (by simpa only [Nat.add_assoc] using hbd)
        (by simpa only [Nat.add_assoc] using hcd)
        he0 (by simpa only [Nat.add_assoc] using he1)
        (by simpa only [Nat.add_assoc] using he2)
        (by simpa only [Nat.add_assoc] using he3)).mpr (by rw [hkappa]; exact dvd_zero _)
      simpa only [N, ← hkn, Nat.add_assoc] using hd

/-- When the obstruction vanishes, the full infinite integer-dual orbit exists. -/
private theorem integral_orbit_of_zero_obstruction (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ)
    (hp : 0 < p) (hq : 0 < q) (hkappa : (2 * (p : ℤ) - 2) * v = 0) :
    ∀ n, Integral (orbit p q v c n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · refine ⟨1 + inr (c ⟨n, hn⟩), ?_⟩
      rw [orbit_initial p q v c ⟨n, hn⟩]
      ext <;> simp [integerCast]
    · have he : n - 4 + 4 = n := by omega
      rw [← he]
      exact integral_next p q v c hp hq hkappa (n - 4) (fun i hi => ih i (by omega))

private theorem orbit_fst_independent (p q : ℕ) (v w : ℤ) (c d : Fin 4 → ℤ) (n : ℕ) :
    (orbit p q v c n).fst = (orbit p q w d n).fst := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · rw [orbit_initial p q v c ⟨n, hn⟩, orbit_initial p q w d ⟨n, hn⟩]
      simp
    · conv_lhs => rw [orbit, dite_eq_right hn]
      conv_rhs => rw [orbit, dite_eq_right hn]
      simp only [fst_mul, fst_add, fst_pow, fst_inv, fst_one, fst_inr, add_zero, one_mul]
      rw [ih (n - 4 + 1) (by omega), ih (n - 4 + 2) (by omega),
        ih (n - 4 + 3) (by omega), ih (n - 4) (by omega)]

private theorem real_integral (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ)
    (hp : 0 < p) (hq : 0 < q) (n : ℕ) :
    ∃ a : ℤ, (a : ℚ) = (orbit p q v c n).fst := by
  obtain ⟨z, hz⟩ := integral_orbit_of_zero_obstruction p q 0 (fun _ => 0) hp hq
    (by simp) n
  refine ⟨z.fst, ?_⟩
  have he := congrArg (fst (R := ℚ) (M := ℚ)) hz
  have he' : (z.fst : ℚ) = (orbit p q 0 (fun _ => 0) n).fst := by
    simpa [integerCast] using he
  exact he'.trans (orbit_fst_independent p q 0 v (fun _ => 0) c n)

private theorem integral_iff_shadow (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ)
    (hp : 0 < p) (hq : 0 < q) (n : ℕ) :
    Integral (orbit p q v c n) ↔ ∃ b : ℤ, (b : ℚ) = (orbit p q v c n).snd := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.snd, ?_⟩
    simpa [integerCast] using congrArg (snd (R := ℚ) (M := ℚ)) hz
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := real_integral p q v c hp hq n
    refine ⟨inl a + inr b, ?_⟩
    apply TrivSqZeroExt.ext <;> simpa [integerCast] using (by assumption)

private theorem orbit_fst_initial (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ)
    (i : ℕ) (hi : i < 4) : (orbit p q v c i).fst = 1 := by
  rw [orbit_initial p q v c ⟨i, hi⟩]
  simp

private theorem orbit_fifth_real (p q : ℕ) (v : ℤ) (c : Fin 4 → ℤ) :
    (orbit p q v c 5).fst = (2 : ℚ) ^ p + 1 := by
  have h0 := orbit_fst_initial p q v c 0 (by omega)
  have h1 := orbit_fst_initial p q v c 1 (by omega)
  have h2 := orbit_fst_initial p q v c 2 (by omega)
  have h3 := orbit_fst_initial p q v c 3 (by omega)
  have he4 := congrArg (fst (R := ℚ) (M := ℚ)) (orbit_exchange p q v c 0)
  have he5 := congrArg (fst (R := ℚ) (M := ℚ)) (orbit_exchange p q v c 1)
  simp only [fst_mul, fst_add, fst_pow, fst_one, fst_inr, add_zero, one_mul,
    Nat.reduceAdd, h0, h1, h2, h3, one_pow, mul_one] at he4 he5
  simpa only [he4, one_add_one_eq_two] using he5

private theorem obstruction_bound (p : ℕ) (hp : 2 ≤ p) :
    0 < 2 * (p : ℤ) - 2 ∧ 2 * (p : ℤ) - 2 < (2 : ℤ) ^ p + 1 := by
  have hi : 2 * (p : ℤ) ≤ (2 : ℤ) ^ p := by
    exact_mod_cast (Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) p)
  constructor <;> omega

private theorem parameter_one_of_integral (p q : ℕ) (c : Fin 4 → ℤ)
    (hp : 0 < p) (hq : 0 < q) (hAll : ∀ n, Integral (orbit p q 1 c n)) : p = 1 := by
  classical
  let z : ℕ → DualNumber ℤ := fun n => (hAll n).choose
  have hz : ∀ n, integerCast (z n) = orbit p q 1 c n := fun n => (hAll n).choose_spec
  have hw := prefix_coprime p q 1 c hp hq z 10 (fun i _ => hz i) 2 (by omega)
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hw
  have hre : (z 5).fst ≠ 0 := by
    have he := congrArg (fst (R := ℚ) (M := ℚ)) (hz 5)
    have ho := ne_of_gt (orbit_positive p q 1 c 5)
    intro hf
    apply ho
    rw [← he]
    simp [integerCast, hf]
  have hex : ∀ k < 6, z (k + 4) * z k =
      (z (k + 1) * z (k + 3)) ^ p + (1 + inr (1 : ℤ)) * z (k + 2) ^ q :=
    fun k hk => prefix_exchange p q 1 c z 10 (fun i _ => hz i) k (by omega)
  have hdv : z 5 ∣ (z 6 * z 8) ^ p + (1 + inr (1 : ℤ)) * z 7 ^ q :=
    ⟨z 9, by simpa only [Nat.reduceAdd, mul_comm] using (hex 5 (by omega)).symm⟩
  have hd := (local_divisibility (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8)
    p q 1 hp hq hre had hbd hcd (hex 1 (by omega)) (hex 2 (by omega))
      (hex 3 (by omega)) (hex 4 (by omega))).mp hdv
  simp only [mul_one] at hd
  have h5 : (z 5).fst = (2 : ℤ) ^ p + 1 := by
    have he := congrArg (fst (R := ℚ) (M := ℚ)) (hz 5)
    rw [orbit_fifth_real] at he
    have he' : ((z 5).fst : ℚ) = (2 : ℚ) ^ p + 1 := by
      simpa [integerCast] using he
    exact_mod_cast he'
  rw [h5] at hd
  by_contra hne
  have hp2 : 2 ≤ p := by omega
  obtain ⟨hpos, hlt⟩ := obstruction_bound p hp2
  have hle := Int.le_of_dvd hpos hd
  omega

/-- Every integer initial tuple is retained inside the equivalence. -/
private theorem all_shadows_integral_iff (p q : ℕ) (c : Fin 4 → ℤ)
    (hp : 0 < p) (hq : 0 < q) :
    (∀ n, ∃ b : ℤ, (b : ℚ) = (orbit p q 1 c n).snd) ↔ p = 1 := by
  constructor
  · intro h
    exact parameter_one_of_integral p q c hp hq (fun n =>
      (integral_iff_shadow p q 1 c hp hq n).mpr (h n))
  · intro hp1 n
    apply (integral_iff_shadow p q 1 c hp hq n).mp
    apply integral_orbit_of_zero_obstruction p q 1 c hp hq
    simp [hp1]

/-- The source exchange relation and the four prescribed dual initial values. -/
def IsOrbit (p q : ℕ) (c : Fin 4 → ℤ) (X : ℕ → DualNumber ℚ) : Prop :=
  (∀ i : Fin 4, X i = 1 + inr (c i : ℚ)) ∧
  ∀ n, X (n + 4) * X n = (X (n + 1) * X (n + 3)) ^ p +
    (1 + DualNumber.eps) * X (n + 2) ^ q

private theorem orbit_unique (p q : ℕ) (c : Fin 4 → ℤ) (X : ℕ → DualNumber ℚ)
    (hX : IsOrbit p q c X) : X = orbit p q 1 c := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · exact (hX.1 ⟨n, hn⟩).trans (orbit_initial p q 1 c ⟨n, hn⟩).symm
    · let k := n - 4
      have hk : k + 4 = n := by omega
      have he := hX.2 k
      rw [ih k (by omega), ih (k + 1) (by omega), ih (k + 2) (by omega),
        ih (k + 3) (by omega), hk] at he
      have ho := orbit_exchange p q 1 c k
      rw [hk] at ho
      have hu : IsUnit (orbit p q 1 c k) :=
        TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
          (isUnit_iff_ne_zero.mpr (ne_of_gt (orbit_positive p q 1 c k)))
      apply hu.mul_right_cancel
      exact he.trans ho.symm

/-- The faithful coefficientwise inclusion into the source's real dual numbers. -/
noncomputable def realCast : DualNumber ℚ →+* DualNumber ℝ where
  toFun x := inl (x.fst : ℝ) + inr (x.snd : ℝ)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

/-- The original real-dual formulation has the same four initial shadows. -/
def IsRealOrbit (p q : ℕ) (c : Fin 4 → ℤ) (X : ℕ → DualNumber ℝ) : Prop :=
  (∀ i : Fin 4, X i = 1 + inr (c i : ℝ)) ∧
  ∀ n, X (n + 4) * X n = (X (n + 1) * X (n + 3)) ^ p +
    (1 + DualNumber.eps) * X (n + 2) ^ q

private theorem realCast_injective : Function.Injective realCast := by
  intro x y he
  apply TrivSqZeroExt.ext
  · have h := congrArg (fst (R := ℝ) (M := ℝ)) he
    simpa [realCast] using h
  · have h := congrArg (snd (R := ℝ) (M := ℝ)) he
    simpa [realCast] using h

private theorem real_orbit_bridge (p q : ℕ) (c : Fin 4 → ℤ) :
    ∀ B, IsRealOrbit p q c B ↔ B = fun n => realCast (orbit p q 1 c n) := by
  let A := fun n => realCast (orbit p q 1 c n)
  have hA : IsRealOrbit p q c A := by
    constructor
    · intro i
      simp [A, orbit_initial p q 1 c i, realCast]
    · intro n
      have he := congrArg realCast (orbit_exchange p q 1 c n)
      have ht : realCast (1 + inr ((1 : ℤ) : ℚ)) =
          (1 + DualNumber.eps : DualNumber ℝ) := by ext <;> simp [realCast]
      simpa only [map_mul, map_add, map_pow, ht] using he
  intro B
  constructor
  · intro hB
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < 4
      · exact (hB.1 ⟨n, hn⟩).trans (hA.1 ⟨n, hn⟩).symm
      · let k := n - 4
        have hk : k + 4 = n := by omega
        have he := hB.2 k
        rw [ih k (by omega), ih (k + 1) (by omega), ih (k + 2) (by omega),
          ih (k + 3) (by omega), hk] at he
        have ho := hA.2 k
        rw [hk] at ho
        have hpos : 0 < (A k).fst := by
          simpa [A, realCast] using
            (Rat.cast_pos.mpr (orbit_positive p q 1 c k) : (0 : ℝ) < _)
        have hu : IsUnit (A k) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
          (isUnit_iff_ne_zero.mpr (ne_of_gt hpos))
        apply hu.mul_right_cancel
        exact he.trans ho.symm
  · rintro rfl
    exact hA

private theorem real_shadow_iff (x : DualNumber ℚ) :
    (∃ b : ℤ, (b : ℝ) = (realCast x).snd) ↔ ∃ b : ℤ, (b : ℚ) = x.snd := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, Rat.cast_injective (α := ℝ) ?_⟩
    simpa [realCast] using hb
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    simpa [realCast] using congrArg (fun r : ℚ => (r : ℝ)) hb

/-- Full pointwise statement, including the faithful real-dual source realization. -/
theorem result (p q : ℕ) (c : Fin 4 → ℤ) (hp : 0 < p) (hq : 0 < q) :
    ∃ A : ℕ → DualNumber ℚ,
      IsOrbit p q c A ∧ (∀ X, IsOrbit p q c X → X = A) ∧
      (∀ n, 0 < (A n).fst) ∧
      ((∀ n, ∃ b : ℤ, (b : ℚ) = (A n).snd) ↔ p = 1) ∧
      (∀ B, IsRealOrbit p q c B ↔ B = fun n => realCast (A n)) ∧
      ((∀ n, ∃ b : ℤ, (b : ℝ) = (realCast (A n)).snd) ↔ p = 1) ∧
      Function.Injective realCast := by
  refine ⟨orbit p q 1 c, ⟨orbit_initial p q 1 c, ?_⟩,
    fun X hX => orbit_unique p q c X hX, orbit_positive p q 1 c,
    all_shadows_integral_iff p q c hp hq, real_orbit_bridge p q c, ?_, realCast_injective⟩
  · intro n
    simpa only [Int.cast_one, show (inr (1 : ℚ) : DualNumber ℚ) = DualNumber.eps from rfl]
      using orbit_exchange p q 1 c n
  · simp only [real_shadow_iff]
    exact all_shadows_integral_iff p q c hp hq

#print axioms result

end D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality
