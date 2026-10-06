/- GID: D5/S3/Arith/Covering/SemiprimeDivisorRepairRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/SemiprimeDivisorRepairRefutation
   mirror-E: none(waiver:finite-refutation-no-numeric-artifact)
   anchors: [D5/S3/Arith/Covering/CoveringSystem, mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Covering/SemiprimeDivisorRepairRefutation.claim; result=D5/S3/Arith/Covering/SemiprimeDivisorRepairRefutation.result; claim=D5/S3/Arith/Covering/SemiprimeDivisorRepairRefutation.claim
   digest: Six semiprime congruence packets cannot be covered by one arbitrary-residue class per prescribed ternary divisor modulus. -/

import Mathlib
import D5.S3.Arith.Covering.CoveringSystem

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open D5.S3.Arith.Covering.CoveringSystem

namespace D5.S3.Arith.Covering.SemiprimeDivisorRepairRefutation

/-- The six distinct semiprime anchors. -/
def anchor : Fin 6 → ℕ := ![35, 77, 55, 65, 221, 85]

/-- The original residues, each divisible by nine. -/
def literal : Fin 6 → ℕ := ![36, 441, 396, 495, 936, 0]

/-- The union of all divisors of the six anchors. -/
def bank : Finset ℕ := {1, 5, 7, 11, 13, 17, 35, 77, 55, 65, 221, 85}

/-- One residue for each prescribed modulus covers every source packet. -/
def claim : Prop :=
  ∃ r : ℕ → ℕ, ∀ i : Fin 6, ∀ x : ℤ,
    x ≡ 0 [ZMOD 9] → x ≡ (literal i : ℤ) [ZMOD (anchor i : ℤ)] →
    ∃ d ∈ bank, x ≡ (r d : ℤ) [ZMOD (27*d : ℕ)]

private def Service (phase : ℕ → ℕ) (digit : ℕ → Fin 3) : Prop :=
  ∀ i : Fin 6, ∀ c : Fin 3, ∃ d : ℕ,
    d ∣ anchor i ∧ phase d % d = literal i % d ∧ digit d = c

private theorem three_children_force_endpoint
    (m p q a : ℕ) (hm : m ≠ 0)
    (hdiv : m.divisors = {1, p, q, m})
    (phase : ℕ → ℕ) (digit : ℕ → Fin 3)
    (hservice : ∀ c : Fin 3, ∃ d : ℕ,
      d ∣ m ∧ phase d % d = a % d ∧ digit d = c) :
    phase p % p = a % p ∨ phase q % q = a % q := by
  obtain ⟨c, hc1, hcm⟩ := Fin.exists_ne_and_ne_of_two_lt (digit 1) (digit m) (by decide)
  obtain ⟨d, hd, hphase, hdigit⟩ := hservice c
  have hdmem : d ∈ m.divisors := Nat.mem_divisors.mpr ⟨hd, hm⟩
  rw [hdiv] at hdmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
  rcases hdmem with rfl | rfl | rfl | rfl
  · exact False.elim (hc1 hdigit.symm)
  · exact Or.inl hphase
  · exact Or.inr hphase
  · exact False.elim (hcm hdigit.symm)

private theorem no_common_signature_table :
    ¬ ∃ phase : ℕ → ℕ, ∃ digit : ℕ → Fin 3, Service phase digit := by
  rintro ⟨phase, digit, hs⟩
  have h0 := three_children_force_endpoint 35 5 7 36 (by decide) (by decide)
    phase digit (hs 0)
  have h1 := three_children_force_endpoint 77 7 11 441 (by decide) (by decide)
    phase digit (hs 1)
  have h2 := three_children_force_endpoint 55 11 5 396 (by decide) (by decide)
    phase digit (hs 2)
  have h3 := three_children_force_endpoint 65 5 13 495 (by decide) (by decide)
    phase digit (hs 3)
  have h4 := three_children_force_endpoint 221 13 17 936 (by decide) (by decide)
    phase digit (hs 4)
  have h5 := three_children_force_endpoint 85 17 5 0 (by decide) (by decide)
    phase digit (hs 5)
  norm_num at h0 h1 h2 h3 h4 h5
  omega

private theorem affine_cover_forces_divisor
    (B : Finset ℕ) (m a : ℕ) (r : ℕ → ℕ)
    (hpos : ∀ d ∈ B, 0 < d)
    (hsmall : (∑ d ∈ B.filter (fun d => ¬d ∣ m),
      (Nat.gcd m d : ℚ) / d) < 1)
    (hcover : ∀ t : ℤ, ∃ d ∈ B,
      (a : ℤ) + 27*m*t ≡ (r d : ℤ) [ZMOD (27*d : ℕ)]) :
    ∃ d ∈ B, d ∣ m ∧ a ≡ r d [MOD 27*d] := by
  classical
  by_contra! hn
  let D := B.filter (fun d => ¬d ∣ m)
  let n : ℕ → ℕ := fun d => d / Nat.gcd d m
  have hnpos : ∀ d ∈ D, 0 < n d := by
    intro d hd
    have hdpos := hpos d (Finset.mem_filter.mp hd).1
    exact Nat.div_pos (Nat.gcd_le_left _ hdpos) (Nat.gcd_pos_of_pos_left _ hdpos)
  let hit (d : ℕ) (t : ℤ) :=
    (a : ℤ) + 27*m*t ≡ (r d : ℤ) [ZMOD (27*d : ℕ)]
  let witness (d : ℕ) : ℤ :=
    if h : ∃ t : ℤ, hit d t then Classical.choose h else 0
  have hwitness {d : ℕ} {t : ℤ} (ht : hit d t) : hit d (witness d) := by
    simp only [witness, dif_pos (show ∃ t, hit d t from ⟨t, ht⟩)]
    exact Classical.choose_spec (show ∃ t, hit d t from ⟨t, ht⟩)
  let residue : ℕ → ℕ := fun d => (witness d % (n d : ℤ)).toNat
  have hresidue {d : ℕ} (hd : d ∈ D) :
      witness d ≡ (residue d : ℤ) [ZMOD (n d : ℤ)] := by
    have hnonneg : 0 ≤ witness d % (n d : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast (hnpos d hd).ne')
    simp only [residue, Int.toNat_of_nonneg hnonneg, Int.ModEq, Int.emod_emod]
  have hDcover : ∀ t : ℤ, ∃ d ∈ D, t ≡ (residue d : ℤ) [ZMOD (n d : ℤ)] := by
    intro t
    obtain ⟨d, hdB, hdt⟩ := hcover t
    have hnd : ¬d ∣ m := by
      intro hdm
      have hdstep : (27*d : ℤ) ∣ 27*m*t := by
        obtain ⟨k, hk⟩ := hdm
        refine ⟨(k : ℤ)*t, ?_⟩
        rw [hk]
        push_cast
        ring
      have hzero : 27*(m : ℤ)*t ≡ 0 [ZMOD (27*d : ℕ)] :=
        Int.modEq_zero_iff_dvd.mpr hdstep
      have ha : (a : ℤ) ≡ (r d : ℤ) [ZMOD (27*d : ℕ)] :=
        ((Int.ModEq.refl (a : ℤ)).add hzero).symm.trans (by simpa using hdt)
      exact hn d hdB hdm (Int.natCast_modEq_iff.mp ha)
    have hdD : d ∈ D := Finset.mem_filter.mpr ⟨hdB, hnd⟩
    have hdt' : hit d t := hdt
    have hw := hwitness hdt'
    have hpair : (27*(m : ℤ)*t) ≡ (27*(m : ℤ)*witness d) [ZMOD (27*d : ℕ)] :=
      Int.ModEq.add_left_cancel' (a : ℤ) (hdt.trans hw.symm)
    have hstrip : (m : ℤ)*t ≡ (m : ℤ)*witness d [ZMOD (d : ℤ)] := by
      apply Int.ModEq.mul_left_cancel' (show (27 : ℤ) ≠ 0 by norm_num)
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hpair
    have hcancel := hstrip.cancel_left_div_gcd
      (show (0 : ℤ) < d by exact_mod_cast hpos d hdB)
    have hcancel' : t ≡ witness d [ZMOD (n d : ℤ)] := by
      simpa only [n, Int.gcd_natCast_natCast, Int.natCast_div] using hcancel
    exact ⟨d, hdD, hcancel'.trans (hresidue hdD)⟩
  let C := D.image (fun d => (residue d, n d))
  have hC : IsCoveringSystem C := by
    constructor
    · intro p hp
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
      exact hnpos d hd
    · intro t
      obtain ⟨d, hd, hdt⟩ := hDcover t
      exact ⟨(residue d, n d), Finset.mem_image.mpr ⟨d, hd, rfl⟩, hdt⟩
  have hsum := sum_reciprocal_moduli_ge_one hC
  have himage : (∑ p ∈ C, (1 : ℚ)/p.2) ≤ ∑ d ∈ D, (1 : ℚ)/n d := by
    exact Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
  have heq : (∑ d ∈ D, (1 : ℚ)/n d) = ∑ d ∈ D, (Nat.gcd m d : ℚ)/d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos := hpos d (Finset.mem_filter.mp hd).1
    have hgp : 0 < Nat.gcd d m := Nat.gcd_pos_of_pos_left _ hdpos
    dsimp only [n]
    rw [Nat.cast_div (Nat.gcd_dvd_left d m) (by exact_mod_cast hgp.ne'), Nat.gcd_comm m d]
    field_simp
  rw [heq] at himage
  exact (not_le_of_gt hsmall) (hsum.trans himage)

private theorem all_six_relative_margins : ∀ i : Fin 6,
    (∑ d ∈ bank.filter (fun d => ¬d ∣ anchor i),
      (Nat.gcd (anchor i) d : ℚ)/d) < 1 := by
  intro i
  have h35 : bank.filter (fun d => ¬d ∣ 35) = {11, 13, 17, 77, 55, 65, 221, 85} := by decide
  have h77 : bank.filter (fun d => ¬d ∣ 77) = {5, 13, 17, 35, 55, 65, 221, 85} := by decide
  have h55 : bank.filter (fun d => ¬d ∣ 55) = {7, 13, 17, 35, 77, 65, 221, 85} := by decide
  have h65 : bank.filter (fun d => ¬d ∣ 65) = {7, 11, 17, 35, 77, 55, 221, 85} := by decide
  have h221 : bank.filter (fun d => ¬d ∣ 221) = {5, 7, 11, 35, 77, 55, 65, 85} := by decide
  have h85 : bank.filter (fun d => ¬d ∣ 85) = {7, 11, 13, 35, 77, 55, 65, 221} := by decide
  fin_cases i
  · change (∑ d ∈ bank.filter (fun d => ¬d ∣ 35), (Nat.gcd 35 d : ℚ)/d) < 1
    rw [h35]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · change (∑ d ∈ bank.filter (fun d => ¬d ∣ 77), (Nat.gcd 77 d : ℚ)/d) < 1
    rw [h77]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · change (∑ d ∈ bank.filter (fun d => ¬d ∣ 55), (Nat.gcd 55 d : ℚ)/d) < 1
    rw [h55]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · change (∑ d ∈ bank.filter (fun d => ¬d ∣ 65), (Nat.gcd 65 d : ℚ)/d) < 1
    rw [h65]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · change (∑ d ∈ bank.filter (fun d => ¬d ∣ 221), (Nat.gcd 221 d : ℚ)/d) < 1
    rw [h221]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · change (∑ d ∈ bank.filter (fun d => ¬d ∣ 85), (Nat.gcd 85 d : ℚ)/d) < 1
    rw [h85]
    norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- The six source packets admit no repair with these twelve numerical labels,
regardless of the output residues. -/
theorem result : ¬ claim := by
  rintro ⟨r, hcover⟩
  apply no_common_signature_table
  let digit : ℕ → Fin 3 := fun d => ⟨r d / 9 % 3, Nat.mod_lt _ (by decide)⟩
  refine ⟨r, digit, ?_⟩
  intro i c
  have hcop : Nat.Coprime 27 (anchor i) := by
    fin_cases i <;> decide
  let a := Nat.chineseRemainder hcop (9*c.val) (literal i)
  have ha27 : a.val ≡ 9*c.val [MOD 27] := a.prop.1
  have ham : a.val ≡ literal i [MOD anchor i] := a.prop.2
  have hpos : ∀ d ∈ bank, 0 < d := by
    intro d hd
    simp only [bank, Finset.mem_insert, Finset.mem_singleton] at hd
    omega
  have hlocal : ∀ t : ℤ, ∃ d ∈ bank,
      (a.val : ℤ) + 27*(anchor i)*t ≡ (r d : ℤ) [ZMOD (27*d : ℕ)] := by
    intro t
    apply hcover i ((a.val : ℤ) + 27*(anchor i)*t)
    · have ha9 : a.val ≡ 0 [MOD 9] :=
        (ha27.of_dvd (by decide : 9 ∣ 27)).trans
          (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 9 c.val))
      have hz : 27*(anchor i : ℤ)*t ≡ 0 [ZMOD 9] := by
        apply Int.modEq_zero_iff_dvd.mpr
        exact ⟨3*(anchor i : ℤ)*t, by ring⟩
      simpa using (Int.natCast_modEq_iff.mpr ha9).add hz
    · have hz : 27*(anchor i : ℤ)*t ≡ 0 [ZMOD (anchor i : ℤ)] := by
        apply Int.modEq_zero_iff_dvd.mpr
        exact ⟨27*t, by ring⟩
      simpa using (Int.natCast_modEq_iff.mpr ham).add hz
  obtain ⟨d, _, hdm, had⟩ := affine_cover_forces_divisor
    bank (anchor i) a.val r hpos (all_six_relative_margins i) hlocal
  refine ⟨d, hdm, ?_, ?_⟩
  · exact ((had.of_dvd (dvd_mul_left d 27)).symm.trans (ham.of_dvd hdm))
  · apply Fin.ext
    have har := (had.of_dvd (dvd_mul_right 27 d))
    have hac := ha27
    change a.val % 27 = r d % 27 at har
    change a.val % 27 = (9*c.val) % 27 at hac
    have hc := c.isLt
    change r d / 9 % 3 = c.val
    omega


end D5.S3.Arith.Covering.SemiprimeDivisorRepairRefutation
