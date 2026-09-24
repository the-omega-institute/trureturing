/- GID: D5/S3/ArithUnits/CenteredReducedResidueProgressions
   generality: G
   mirror-B: D5/B/S3/ArithUnits/CenteredReducedResidueProgressions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The longest progression in a short centered squarefree reduced residue system. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses
import LeanInformationAudit.Syntax
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.CenteredReducedResidueProgressions

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit

set_option backward.isDefEq.respectTransparency.types false

/-- The source's fixed centered representative system. The all-parity formula
uses the interval of length `n` beginning at `-((n+1)/2)+1`. -/
def CenteredReducedResidue (n : ℕ) (x : ℤ) : Prop :=
  -((n + 1) / 2 : ℤ) + 1 ≤ x ∧
    x ≤ -((n + 1) / 2 : ℤ) + n ∧
    x.gcd n = 1

/-- A length admitted by a positive-step arithmetic progression in the fixed
centered reduced residue system. -/
def AdmissibleLength (n s : ℕ) : Prop :=
  ∃ a : ℤ, ∃ h : ℕ, 0 < h ∧
    ∀ i : ℕ, i < s → CenteredReducedResidue n (a + (i * h : ℕ))

/-- The greatest prime factor, expressed through the pinned `primeFactors`
interface rather than a separate partial maximum. -/
def GreatestPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The source's finite arithmetic choice: `0` decodes the printed subtraction
and `1` is the sensitivity variant with addition in the quotient term. -/
def SourceCorrection : Bool := false

def decodeSourceCorrection (choice : Bool) (p q : ℕ) : ℕ :=
  if choice = false then p - 1 - q else p - 1 + q

private def sourceCorrectionRealization (f : Bool → Bool) :
    PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization f

register_information_template sourceCorrectionRealization

def sourceCorrectionArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (n : ℕ) (hn_even : Even n) (hn_squarefree : Squarefree n)
    (hn_factors : 3 ≤ n.primeFactors.card)
    (hn_short : n / GreatestPrimeFactor n < 2 * GreatestPrimeFactor n),
    let p := GreatestPrimeFactor n
    let d := n / p
    IsGreatest {s : ℕ | AdmissibleLength n s}
        (decodeSourceCorrection (r.readout () SourceCorrection) p (2 * p / d)) ∧
      ⌊(p : ℚ) - (2 * p : ℚ) / d⌋ =
        (decodeSourceCorrection (r.readout () SourceCorrection) p (2 * p / d) : ℕ)

local instance : DecidableEq sourceCorrectionArena.State :=
  instDecidableEqBool

private lemma prime_dvd_progression_term {q s h : ℕ} {a : ℤ}
    (hq : q.Prime) (hh : ¬ q ∣ h) (hs : q ≤ s) :
    ∃ i : ℕ, i < s ∧ (q : ℤ) ∣ a + (i * h : ℕ) := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hh0 : (h : ZMod q) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hh
  let i : ℕ := ((-(a : ZMod q)) / (h : ZMod q)).val
  have hiq : i < q := ZMod.val_lt _
  refine ⟨i, hiq.trans_le hs, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  have hi : (i : ZMod q) = (-(a : ZMod q)) / (h : ZMod q) := by
    exact ZMod.natCast_zmod_val _
  rw [hi]
  field_simp
  ring

private lemma no_long_progression_of_missing_prime {n d p s h : ℕ} {a : ℤ}
    (hn : n = d * p) (hd_even : Even d) (hd_squarefree : Squarefree d)
    (hd6 : 6 ≤ d) (hshort : d < 2 * p)
    (hprime_lt : ∀ q ∈ d.primeFactors, q < p)
    (hh : ¬ d ∣ h) (hhpos : 0 < h)
    (ha : ∀ i : ℕ, i < s → CenteredReducedResidue n (a + (i * h : ℕ))) :
    s ≤ p - 1 - (2 * p / d) := by
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    simp at hd_squarefree
  have hh0 : h ≠ 0 := Nat.ne_of_gt hhpos
  rw [← Nat.prod_primeFactors_of_squarefree hd_squarefree,
    Nat.prod_primeFactors_dvd_iff hh0] at hh
  simp only [Finset.subset_iff] at hh
  push Not at hh
  obtain ⟨q, hqd, hqh⟩ := hh
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqd
  have hqnh : ¬ q ∣ h := by
    intro hdiv
    exact hqh (hq.mem_primeFactors hdiv hh0)
  have hsq : s ≤ q - 1 := by
    by_contra hsq
    have hqs : q ≤ s := by omega
    obtain ⟨i, his, hdiv⟩ := prime_dvd_progression_term hq hqnh hqs
    have hgcd := (ha i his).2.2
    have hqn : q ∣ n := hn.symm ▸ dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors hqd) p
    have hqgcdZ : (q : ℤ) ∣ ((a + (i * h : ℕ)).gcd n : ℤ) :=
      Int.dvd_coe_gcd hdiv (by exact_mod_cast hqn)
    have hqgcd : q ∣ (a + (i * h : ℕ)).gcd n := by exact_mod_cast hqgcdZ
    rw [hgcd] at hqgcd
    exact hq.not_dvd_one hqgcd
  let r := 2 * p / d
  have hdpos : 0 < d := by omega
  have hrpos : 0 < r := by
    dsimp [r]
    exact Nat.div_pos (by omega) hdpos
  have hrmul : r * d ≤ 2 * p := by
    dsimp [r]
    exact Nat.div_mul_le_self _ _
  have hqr : q + r ≤ p := by
    by_cases hq2 : q = 2
    · subst q
      have hsix : 6 * r ≤ d * r := Nat.mul_le_mul_right r hd6
      have hthree : 3 * r ≤ p := by nlinarith [hrmul, hsix]
      omega
    · have htwo_d : 2 ∣ d := even_iff_two_dvd.mp hd_even
      have htwoq : Nat.Coprime 2 q :=
        (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
      have hprod : 2 * q ∣ d := htwoq.mul_dvd_of_dvd_of_dvd htwo_d
        (Nat.dvd_of_mem_primeFactors hqd)
      have hdq : 2 * q ≤ d := Nat.le_of_dvd hdpos hprod
      have hscaled : r * (2 * q) ≤ r * d := Nat.mul_le_mul_left r hdq
      have hscaled' : 2 * (r * q) ≤ r * d := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
      have htwobound : 2 * (r * q) ≤ 2 * p := hscaled'.trans hrmul
      have hrq : r * q ≤ p := Nat.le_of_mul_le_mul_left htwobound Nat.two_pos
      have hq3 : 3 ≤ q := by
        have := hq.two_le
        omega
      have hqp := hprime_lt q hqd
      by_cases hr1 : r = 1
      · omega
      · have hr2 : 2 ≤ r := by omega
        nlinarith
  dsimp [r] at hsq hqr ⊢
  omega

private lemma source_floor_identity {d p : ℕ}
    (hd : 0 < d) (hrem : ¬ d ∣ 2 * p)
    (hquot : 2 * p / d + 1 ≤ p) :
    ⌊(p : ℚ) - (2 * p : ℚ) / d⌋ = (p - 1 - (2 * p / d) : ℕ) := by
  let r := 2 * p / d
  let k := p - 1 - r
  have hrmod := Nat.div_add_mod (2 * p) d
  have hmodpos : 0 < (2 * p) % d := by
    have hne : (2 * p) % d ≠ 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero] using hrem
    omega
  have hmodlt : (2 * p) % d < d := Nat.mod_lt _ hd
  have hrmod' : (2 * p / d) * d + (2 * p) % d = 2 * p := by
    simpa [Nat.mul_comm] using hrmod
  have hrlo : r * d < 2 * p := by
    calc
      r * d < r * d + (2 * p) % d := Nat.lt_add_of_pos_right hmodpos
      _ = 2 * p := by simpa [r] using hrmod'
  have hrhi : 2 * p < (r + 1) * d := by
    calc
      2 * p = r * d + (2 * p) % d := by simpa [r] using hrmod'.symm
      _ < r * d + d := Nat.add_lt_add_left hmodlt _
      _ = (r + 1) * d := by ring
  have hkform : k + r + 1 = p := by
    dsimp [k, r]
    omega
  apply Int.floor_eq_iff.mpr
  have hfraclo : (r : ℚ) < (2 * p : ℚ) / d := by
    apply (lt_div_iff₀ (show (0 : ℚ) < d by positivity)).mpr
    exact_mod_cast hrlo
  have hfrachi : (2 * p : ℚ) / d < (r + 1 : ℕ) := by
    apply (div_lt_iff₀ (show (0 : ℚ) < d by positivity)).mpr
    exact_mod_cast hrhi
  have hkformQ : (k : ℚ) + r + 1 = p := by exact_mod_cast hkform
  have hlower : (k : ℚ) + (2 * p : ℚ) / d < k + r + 1 := by
    push_cast at hfrachi
    linarith
  have hupper : (k : ℚ) + r + 1 < k + 1 + (2 * p : ℚ) / d := by
    linarith
  constructor
  · rw [le_sub_iff_add_le]
    change (k : ℚ) + (2 * p : ℚ) / d ≤ p
    exact hlower.le.trans_eq hkformQ
  · rw [sub_lt_iff_lt_add]
    change (p : ℚ) < (k : ℚ) + 1 + (2 * p : ℚ) / d
    exact hkformQ.symm.trans_lt hupper

private lemma no_long_progression_of_large_multiple
    {n d p s h t : ℕ} {a : ℤ}
    (hn : n = d * p) (hd_even : Even d) (hd6 : 6 ≤ d)
    (hp5 : 5 ≤ p) (hshort : d < 2 * p)
    (hh : h = t * d) (ht : 2 ≤ t) (hs : 0 < s)
    (ha : ∀ i : ℕ, i < s → CenteredReducedResidue n (a + (i * h : ℕ))) :
    s ≤ p - 1 - (2 * p / d) := by
  have hn_even : Even n := hn.symm ▸ hd_even.mul_right p
  have hspan : ((s - 1) * h : ℕ) ≤ n - 1 := by
    have centered_even (x : ℤ) : CenteredReducedResidue n x ↔
        -(n / 2 : ℤ) + 1 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ x.gcd n = 1 := by
      obtain ⟨m, rfl⟩ := hn_even
      simp [CenteredReducedResidue]
      omega
    have hzero := (centered_even a).mp (by simpa using ha 0 hs)
    have hlast := (centered_even (a + ((s - 1) * h : ℕ))).mp
      (ha (s - 1) (Nat.sub_lt hs (by omega)))
    have hnpos : 0 < n := by
      by_contra hz
      have : n = 0 := by omega
      subst n
      omega
    have hz : (-(n / 2 : ℤ) + 1) ≤ a := hzero.1
    have hu : a + (((s - 1) * h : ℕ) : ℤ) ≤ (n / 2 : ℤ) := hlast.2.1
    obtain ⟨m, hm⟩ := hn_even
    have heven : 2 * (n / 2) = n := by omega
    have hevenZ : (2 : ℤ) * ((n / 2 : ℕ) : ℤ) = n := by exact_mod_cast heven
    have hhalf : (n : ℤ) / 2 = ((n / 2 : ℕ) : ℤ) := (Int.natCast_div n 2).symm
    rw [hhalf] at hz hu
    have hspanZ : (((s - 1) * h : ℕ) : ℤ) ≤ (n - 1 : ℕ) := by omega
    exact_mod_cast hspanZ
  have hdpos : 0 < d := by omega
  have hnpos : 0 < n := by rw [hn]; positivity
  have hmul_lt : ((s - 1) * t) * d < p * d := by
    calc
      ((s - 1) * t) * d = (s - 1) * h := by rw [hh]; ring
      _ ≤ n - 1 := hspan
      _ < n := Nat.sub_lt hnpos (by omega)
      _ = p * d := by rw [hn]; ring
  have hst : (s - 1) * t < p := by
    exact (Nat.mul_lt_mul_right hdpos).mp (by simpa [Nat.mul_comm] using hmul_lt)
  have htwo : 2 * (s - 1) < p := by
    have hle : 2 * (s - 1) ≤ t * (s - 1) := Nat.mul_le_mul_right (s - 1) ht
    nlinarith [hst]
  let r := 2 * p / d
  have hrpos : 0 < r := by
    dsimp [r]
    exact Nat.div_pos (by omega) hdpos
  have hrmul : r * d ≤ 2 * p := by
    dsimp [r]
    exact Nat.div_mul_le_self _ _
  have hsix : 6 * r ≤ d * r := Nat.mul_le_mul_right r hd6
  have hthree : 3 * r ≤ p := by
    nlinarith [hrmul, hsix]
  dsimp [r] at hrpos hthree
  omega

set_option maxHeartbeats 800000 in
-- The centered representative construction uses several large mixed Int/Nat goals.
private lemma no_long_progression_of_step
    {n d e p s : ℕ} {a : ℤ}
    (hn : n = d * p) (hde : d = 2 * e)
    (he3 : 3 ≤ e) (heodd : Odd e) (hp : p.Prime) (hdp : d.Coprime p)
    (hshort : d < 2 * p)
    (ha : ∀ i : ℕ, i < s → CenteredReducedResidue n (a + (i * d : ℕ))) :
    s ≤ p - 1 - (2 * p / d) := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hs : 0 < s := Nat.pos_of_ne_zero hs0
  have hdpos : 0 < d := by omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  let _ : Fact p.Prime := ⟨hp⟩
  have hn_even : Even n := hn.symm ▸ (hde ▸ even_two_mul e).mul_right p
  have centered_even (x : ℤ) : CenteredReducedResidue n x ↔
      -(n / 2 : ℤ) + 1 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ x.gcd n = 1 := by
    obtain ⟨m, rfl⟩ := hn_even
    simp [CenteredReducedResidue]
    omega
  have ha0 := (centered_even a).mp (by simpa using ha 0 hs)
  have hhalf : n / 2 = e * p := by
    calc
      n / 2 = (2 * (e * p)) / 2 := by rw [hn, hde]; ring_nf
      _ = e * p := by omega
  have hhalfZ : (n : ℤ) / 2 = (e * p : ℕ) := by
    calc
      (n : ℤ) / 2 = ((n / 2 : ℕ) : ℤ) := (Int.natCast_div n 2).symm
      _ = (e * p : ℕ) := by exact_mod_cast hhalf
  rw [hhalfZ] at ha0
  have hdp' : p.Coprime d := hdp.symm
  have hdcast : (d : ZMod p) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hp.coprime_iff_not_dvd.mp hdp'
  let j : ℕ := ((-(a : ZMod p)) / (d : ZMod p)).val
  have hj : j < p := ZMod.val_lt _
  have hjcast : (j : ZMod p) = (-(a : ZMod p)) / (d : ZMod p) :=
    ZMod.natCast_zmod_val _
  let t0 : ℤ := a + (j * d : ℕ)
  have hpt0 : (p : ℤ) ∣ t0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp [t0]
    push_cast
    rw [hjcast]
    field_simp
    ring
  have ht0lo : -(e * p : ℤ) + 1 ≤ t0 := by
    dsimp [t0]
    have halo : -(e : ℤ) * p + 1 ≤ a := by simpa using ha0.1
    rw [show -(e * p : ℤ) = -(e : ℤ) * p by ring]
    exact halo.trans (le_add_of_nonneg_right
      (mul_nonneg (Int.natCast_nonneg j) (Int.natCast_nonneg d)))
  have ht0hi : t0 < (e * p : ℤ) + n := by
    dsimp [t0]
    have hjle : j * d ≤ (p - 1) * d := Nat.mul_le_mul_right d (by omega)
    have hpd : (p - 1) * d < p * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
    have hnd : p * d = n := by rw [hn]; ring
    have hjd : (j * d : ℕ) < n := by omega
    exact_mod_cast (show a + ((j * d : ℕ) : ℤ) < (e * p : ℕ) + n by omega)
  let t : ℤ := if t0 ≤ (e * p : ℤ) then t0 else t0 - n
  have htlo : -(e * p : ℤ) + 1 ≤ t := by
    dsimp [t]
    split_ifs with h
    · exact ht0lo
    · have hnZ : (n : ℤ) = 2 * (e * p : ℕ) := by
        rw [hn, hde]
        push_cast
        ring
      omega
  have hthi : t ≤ (e * p : ℤ) := by
    dsimp [t]
    split_ifs with h
    · exact h
    · omega
  have hpt : (p : ℤ) ∣ t := by
    dsimp [t]
    split_ifs
    · exact hpt0
    · exact dvd_sub hpt0 (by rw [hn]; exact_mod_cast dvd_mul_left p d)
  have hdta : (d : ℤ) ∣ t - a := by
    dsimp [t, t0]
    split_ifs
    · refine ⟨j, by ring⟩
    · refine ⟨(j : ℤ) - p, ?_⟩
      rw [hn]
      push_cast
      ring
  have had : a.gcd d = 1 := by
    apply Int.gcd_eq_one_of_gcd_mul_right_eq_one_left
    simpa [hn] using ha0.2.2
  have htd : t.gcd d = 1 := by
    obtain ⟨w, hw⟩ := hdta
    have hta : t = a + d * w := by omega
    rw [hta, Int.gcd_add_mul_left_left]
    exact had
  obtain ⟨z, hz⟩ := hpt
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hzlo : -(e : ℤ) + 1 ≤ z := by
    rw [hz] at htlo
    by_contra hh
    have hlt : z < -(e : ℤ) + 1 := by omega
    have hmul := mul_lt_mul_of_pos_left hlt hpZ
    nlinarith
  have hzhi : z ≤ e := by
    rw [hz] at hthi
    by_contra hh
    have hlt : (e : ℤ) < z := by omega
    have hmul := mul_lt_mul_of_pos_left hlt hpZ
    nlinarith
  have hzne : z ≠ e ∧ z ≠ e - 1 ∧ z ≠ -e + 1 := by
    constructor
    · intro hze
      subst z
      have het : (e : ℤ) ∣ t := by rw [hz]; exact ⟨p, by ring⟩
      have hedNat : e ∣ d := by rw [hde]; exact dvd_mul_left e 2
      have hed : (e : ℤ) ∣ d := by exact_mod_cast hedNat
      have hediv : e ∣ t.gcd d := Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd het hed)
      rw [htd] at hediv
      have := Nat.dvd_one.mp hediv
      omega
    constructor
    · intro hze
      subst z
      obtain ⟨v, hv⟩ := heodd
      have ht2 : (2 : ℤ) ∣ t := by
        rw [hz, hv]
        refine ⟨(p : ℤ) * v, ?_⟩
        push_cast
        ring
      have hd2Nat : 2 ∣ d := by rw [hde]; exact dvd_mul_right 2 e
      have hd2 : (2 : ℤ) ∣ d := by exact_mod_cast hd2Nat
      have : 2 ∣ t.gcd d := Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd ht2 hd2)
      rw [htd] at this
      norm_num at this
    · intro hze
      subst z
      obtain ⟨v, hv⟩ := heodd
      have ht2 : (2 : ℤ) ∣ t := by
        rw [hz, hv]
        refine ⟨-(p : ℤ) * v, ?_⟩
        push_cast
        ring
      have hd2Nat : 2 ∣ d := by rw [hde]; exact dvd_mul_right 2 e
      have hd2 : (2 : ℤ) ∣ d := by exact_mod_cast hd2Nat
      have : 2 ∣ t.gcd d := Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd ht2 hd2)
      rw [htd] at this
      norm_num at this
  have hzrange : -(e : ℤ) + 2 ≤ z ∧ z ≤ e - 2 := by omega
  have halast := (centered_even (a + ((s - 1) * d : ℕ))).mp
    (ha (s - 1) (Nat.sub_lt hs (by omega)))
  rw [hhalfZ] at halast
  have hnot_between : ¬(a ≤ t ∧ t ≤ a + (((s - 1) * d : ℕ) : ℤ)) := by
    rintro ⟨hat, htl⟩
    obtain ⟨w, hw⟩ := hdta
    have hw0 : 0 ≤ w := by
      have hdZ : (0 : ℤ) < d := by exact_mod_cast hdpos
      nlinarith only [hw, hat, hdZ]
    have hwle : w ≤ s - 1 := by
      have hdZ : (0 : ℤ) < d := by exact_mod_cast hdpos
      push_cast at htl
      by_contra hh
      have hlt : ((s - 1 : ℕ) : ℤ) < w := by omega
      have hmul := mul_lt_mul_of_pos_left hlt hdZ
      nlinarith only [hw, htl, hmul]
    let i := w.toNat
    have hiw : (i : ℤ) = w := by
      dsimp [i]
      exact Int.toNat_of_nonneg hw0
    have hisZ : (i : ℤ) < s := by rw [hiw]; omega
    have his : i < s := by exact_mod_cast hisZ
    have hit : a + ((i * d : ℕ) : ℤ) = t := by
      push_cast
      rw [hiw]
      nlinarith
    have hunit := (ha i his).2.2
    rw [hit] at hunit
    have hpn : (p : ℤ) ∣ n := by rw [hn]; exact_mod_cast dvd_mul_left p d
    have hpt' : (p : ℤ) ∣ t := ⟨z, hz⟩
    have hpgcdZ : (p : ℤ) ∣ (t.gcd n : ℤ) := Int.dvd_coe_gcd hpt' hpn
    have hpgcd : p ∣ t.gcd n := by exact_mod_cast hpgcdZ
    rw [hunit] at hpgcd
    exact hp.not_dvd_one hpgcd
  have hside : a + (((s - 1) * d : ℕ) : ℤ) < t ∨ t < a := by omega
  have hdpge : 2 * p ≤ d * p := by
    rw [hde]
    exact Nat.mul_le_mul_right p (by omega)
  have hsd : ((s * d : ℕ) : ℤ) ≤ (d * p : ℕ) - (2 * p : ℕ) := by
    rcases hside with hbelow | habove
    · have hdiv : (d : ℤ) ∣ t - (a + (((s - 1) * d : ℕ) : ℤ)) := by
        have hm : (d : ℤ) ∣ (((s - 1) * d : ℕ) : ℤ) := by
          exact_mod_cast (dvd_mul_left d (s - 1))
        rw [show t - (a + (((s - 1) * d : ℕ) : ℤ)) =
          (t - a) - (((s - 1) * d : ℕ) : ℤ) by ring]
        exact hdta.sub hm
      obtain ⟨w, hw⟩ := hdiv
      have hwpos : 0 < w := by
        have hdZ : (0 : ℤ) < d := by exact_mod_cast hdpos
        nlinarith only [hw, hbelow, hdZ]
      have hgap : (d : ℤ) ≤ t - (a + (((s - 1) * d : ℕ) : ℤ)) := by
        have hdZ : (0 : ℤ) < d := by exact_mod_cast hdpos
        rw [hw]
        have hwone : (1 : ℤ) ≤ w := by omega
        nlinarith only [hwone, hdZ]
      have hsdEq : ((s * d : ℕ) : ℤ) =
          (((s - 1) * d : ℕ) : ℤ) + d := by
        have hsdec := Nat.sub_add_cancel (show 1 ≤ s by omega)
        push_cast
        have hsdecZ : (s : ℤ) = ((s - 1 : ℕ) : ℤ) + 1 := by exact_mod_cast hsdec.symm
        rw [hsdecZ]
        ring
      have hgap' : (((s - 1) * d : ℕ) : ℤ) + d ≤ t - a := by
        nlinarith only [hgap]
      push_cast at hgap'
      have halo : -(e : ℤ) * p + 1 ≤ a := by simpa using ha0.1
      have hmargin : ((s * d : ℕ) : ℤ) ≤ t - (-(e * p : ℤ) + 1) := by
        calc
          ((s * d : ℕ) : ℤ) = (((s - 1) * d : ℕ) : ℤ) + d := hsdEq
          _ ≤ t - (-(e * p : ℤ) + 1) := by
            push_cast
            nlinarith only [hgap', halo]
      rw [hz] at hmargin
      have hzmul := mul_le_mul_of_nonneg_left hzrange.2 hpZ.le
      have hdeZ : (d : ℤ) = 2 * e := by exact_mod_cast hde
      push_cast at hmargin
      calc
        (s : ℤ) * d ≤ p * z - (-(e * p : ℤ) + 1) := hmargin
        _ ≤ (d : ℤ) * p - 2 * p := by nlinarith only [hzmul, hdeZ]
        _ = ((d * p : ℕ) : ℤ) - ((2 * p : ℕ) : ℤ) := by push_cast; ring
    · have hdiv : (d : ℤ) ∣ a - t := by
        simpa only [neg_sub] using (dvd_neg.mpr hdta)
      obtain ⟨w, hw⟩ := hdiv
      have hwpos : 0 < w := by
        have hdZ : (0 : ℤ) < d := by exact_mod_cast hdpos
        nlinarith only [hw, habove, hdZ]
      have hgap : (d : ℤ) ≤ a - t := by
        have hdZ : (0 : ℤ) < d := by exact_mod_cast hdpos
        rw [hw]
        have hwone : (1 : ℤ) ≤ w := by omega
        nlinarith only [hwone, hdZ]
      have hsdEq : ((s * d : ℕ) : ℤ) =
          (((s - 1) * d : ℕ) : ℤ) + d := by
        have hsdec := Nat.sub_add_cancel (show 1 ≤ s by omega)
        push_cast
        have hsdecZ : (s : ℤ) = ((s - 1 : ℕ) : ℤ) + 1 := by exact_mod_cast hsdec.symm
        rw [hsdecZ]
        ring
      have hgap' : (((s - 1) * d : ℕ) : ℤ) + d ≤ a - t + (((s - 1) * d : ℕ) : ℤ) := by
        nlinarith only [hgap]
      push_cast at hgap'
      have haup : a + (((s - 1) * d : ℕ) : ℤ) ≤ (e : ℤ) * p := by
        simpa using halast.2.1
      push_cast at haup
      have hmargin : ((s * d : ℕ) : ℤ) ≤ (e * p : ℤ) - t := by
        calc
          ((s * d : ℕ) : ℤ) = (((s - 1) * d : ℕ) : ℤ) + d := hsdEq
          _ ≤ (e * p : ℤ) - t := by
            push_cast
            nlinarith only [hgap', haup]
      rw [hz] at hmargin
      have hzmul := mul_le_mul_of_nonneg_left hzrange.1 hpZ.le
      have hdeZ : (d : ℤ) = 2 * e := by exact_mod_cast hde
      push_cast at hmargin
      calc
        (s : ℤ) * d ≤ (e : ℤ) * p - p * z := hmargin
        _ ≤ (d : ℤ) * p - 2 * p := by nlinarith only [hzmul, hdeZ]
        _ = ((d * p : ℕ) : ℤ) - ((2 * p : ℕ) : ℤ) := by push_cast; ring
  let r := 2 * p / d
  have hrem : ¬d ∣ 2 * p := by
    intro hdiv
    have hd2 : d ∣ 2 := hdp.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdiv)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by omega) hd2
    omega
  have hrmod := Nat.div_add_mod (2 * p) d
  have hmodpos : 0 < (2 * p) % d := by
    have : (2 * p) % d ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hrem
    omega
  have hrlo : r * d < 2 * p := by
    dsimp [r]
    have hrmod' : (2 * p / d) * d + (2 * p) % d = 2 * p := by
      simpa [Nat.mul_comm] using hrmod
    omega
  have hrlt : r < p := by
    have := hshort
    have hdpos' : 0 < d := by omega
    by_contra hh
    have hmul : p * d ≤ r * d := Nat.mul_le_mul_right d (by omega)
    nlinarith [hrlo]
  have hsdlt : s * d < (p - r) * d := by
    have hsumZ : ((s * d : ℕ) : ℤ) + (2 * p : ℕ) ≤ (d * p : ℕ) := by
      calc
        ((s * d : ℕ) : ℤ) + (2 * p : ℕ) ≤
            (((d * p : ℕ) : ℤ) - (2 * p : ℕ)) + (2 * p : ℕ) :=
          by simpa [add_comm] using add_le_add_right hsd ((2 * p : ℕ) : ℤ)
        _ = (d * p : ℕ) := by ring
    have hsum : s * d + 2 * p ≤ d * p := by exact_mod_cast hsumZ
    have : s * d + r * d < d * p :=
      (Nat.add_lt_add_left hrlo (s * d)).trans_le hsum
    have hsum_lt : (s + r) * d < p * d := by
      calc
        (s + r) * d = s * d + r * d := Nat.add_mul _ _ _
        _ < d * p := this
        _ = p * d := Nat.mul_comm _ _
    have hsr : s + r < p := (Nat.mul_lt_mul_right hdpos).mp hsum_lt
    have hsr' : s < p - r := by omega
    exact (Nat.mul_lt_mul_right hdpos).mpr hsr'
  have hsp : s < p - r := (Nat.mul_lt_mul_right hdpos).mp
    (by simpa [Nat.mul_comm] using hsdlt)
  dsimp [r] at hsp ⊢
  omega

set_option maxHeartbeats 800000 in
-- This large local budget is needed by the centered interval and prime-divisor
-- arithmetic; it does not alter the theorem's hypotheses or conclusion.
private lemma attained_progression
    {n d e p : ℕ}
    (hn : n = d * p) (hde : d = 2 * e)
    (he3 : 3 ≤ e) (heodd : Odd e) (hp : p.Prime) (hdp : d.Coprime p)
    (hshort : d < 2 * p) :
    AdmissibleLength n (p - 1 - (2 * p / d)) := by
  let r := 2 * p / d
  let k := p - 1 - r
  let y : ℤ := (p : ℤ) * (2 - (e : ℤ))
  have hdpos : 0 < d := by omega
  have hpne2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hpne2
  have hpoddZ : Odd (p : ℤ) := Odd.natCast hpodd
  have heoddZ : Odd (e : ℤ) := Odd.natCast heodd
  obtain ⟨v, hv⟩ := hpodd
  have hp5 : 5 ≤ p := by omega
  have hn_even : Even n := hn.symm ▸ (hde ▸ even_two_mul e).mul_right p
  have centered_even (x : ℤ) : CenteredReducedResidue n x ↔
      -(n / 2 : ℤ) + 1 ≤ x ∧ x ≤ (n / 2 : ℤ) ∧ x.gcd n = 1 := by
    obtain ⟨m, rfl⟩ := hn_even
    simp [CenteredReducedResidue]
    omega
  have hhalf : n / 2 = e * p := by
    calc
      n / 2 = (2 * (e * p)) / 2 := by rw [hn, hde]; ring_nf
      _ = e * p := by omega
  have hhalfZ : (n : ℤ) / 2 = (e * p : ℕ) := by
    calc
      (n : ℤ) / 2 = ((n / 2 : ℕ) : ℤ) := (Int.natCast_div n 2).symm
      _ = (e * p : ℕ) := by exact_mod_cast hhalf
  have hrpos : 0 < r := by
    dsimp [r]
    exact Nat.div_pos (by omega) hdpos
  have hrmul : r * d ≤ 2 * p := by
    dsimp [r]
    exact Nat.div_mul_le_self _ _
  have hrem : ¬d ∣ 2 * p := by
    intro hdiv
    have hd2 : d ∣ 2 := hdp.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdiv)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by omega) hd2
    omega
  have hrmod := Nat.div_add_mod (2 * p) d
  have hmodpos : 0 < (2 * p) % d := by
    have : (2 * p) % d ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hrem
    omega
  have hrlo : r * d < 2 * p := by
    dsimp [r]
    have hrmod' : (2 * p / d) * d + (2 * p) % d = 2 * p := by
      simpa [Nat.mul_comm] using hrmod
    omega
  have hrhi : 2 * p < (r + 1) * d := by
    have hmodlt : (2 * p) % d < d := Nat.mod_lt _ hdpos
    dsimp [r]
    have hrmod' : (2 * p / d) * d + (2 * p) % d = 2 * p := by
      simpa [Nat.mul_comm] using hrmod
    calc
      2 * p = (2 * p / d) * d + (2 * p) % d := hrmod'.symm
      _ < (2 * p / d) * d + d := Nat.add_lt_add_left hmodlt _
      _ = (2 * p / d + 1) * d := by ring
  have hrlt : r < p := by
    by_contra hh
    have hmul : p * d ≤ r * d := Nat.mul_le_mul_right d (by omega)
    nlinarith [hrlo]
  have hkform : k + r + 1 = p := by
    dsimp [k]
    omega
  refine ⟨y + d, d, hdpos, ?_⟩
  intro i hi
  let j := i + 1
  have hjpos : 0 < j := by omega
  have hjle : j ≤ k := by omega
  have hjp : j < p := by omega
  have hterm : y + (d : ℤ) + ((i * d : ℕ) : ℤ) = y + ((j * d : ℕ) : ℤ) := by
    dsimp [j]
    ring
  rw [hterm, centered_even, hhalfZ]
  have hlower : -(e * p : ℤ) + 1 ≤ y + ((j * d : ℕ) : ℤ) := by
    dsimp [y]
    rw [hde]
    nlinarith
  have hupperNat : 2 * p + j * d ≤ d * p := by
    have hjd : j * d ≤ k * d := Nat.mul_le_mul_right d hjle
    have hbound : k * d + 2 * p ≤ d * p := by
      have : 2 * p ≤ (r + 1) * d := hrhi.le
      calc
        k * d + 2 * p ≤ k * d + (r + 1) * d := Nat.add_le_add_left this _
        _ = (k + r + 1) * d := by ring
        _ = d * p := by rw [hkform]; ring
    omega
  have hupper : y + ((j * d : ℕ) : ℤ) ≤ (e * p : ℕ) := by
    dsimp [y]
    rw [hde] at hupperNat
    nlinarith
  refine ⟨hlower, hupper, ?_⟩
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro q hq hqgcd
  have hqtermZ : (q : ℤ) ∣ y + ((j * d : ℕ) : ℤ) := by
    exact dvd_trans (by exact_mod_cast hqgcd) (Int.gcd_dvd_left _ _)
  have hqnZ : (q : ℤ) ∣ (n : ℤ) := by
    exact dvd_trans (by exact_mod_cast hqgcd) (Int.gcd_dvd_right _ _)
  have hqn : q ∣ n := by exact_mod_cast hqnZ
  rw [hn] at hqn
  rcases hq.dvd_mul.mp hqn with hqd | hqp
  · have hqnp : ¬q ∣ p := by
      intro hqp
      have : q ∣ Nat.gcd d p := Nat.dvd_gcd hqd hqp
      rw [hdp.gcd_eq_one] at this
      exact hq.not_dvd_one this
    have hqjdZ : (q : ℤ) ∣ ((j * d : ℕ) : ℤ) := by exact_mod_cast dvd_mul_of_dvd_right hqd j
    have hqyZ : (q : ℤ) ∣ y := by
      have := hqtermZ.sub hqjdZ
      simpa only [add_sub_cancel_right] using this
    by_cases hq2 : q = 2
    · subst q
      have hyodd : Odd y := by
        dsimp [y]
        exact hpoddZ.mul ((even_two : Even (2 : ℤ)).sub_odd heoddZ)
      have hjdeven : Even (((j * d : ℕ) : ℤ)) := by
        exact ((hde ▸ even_two_mul e).mul_left j).natCast
      have htermodd : Odd (y + ((j * d : ℕ) : ℤ)) := hyodd.add_even hjdeven
      exact (Int.not_even_iff_odd.mpr htermodd) (even_iff_two_dvd.mpr hqtermZ)
    · have hqe : q ∣ e := by
        rcases hq.dvd_mul.mp (by simpa [hde] using hqd) with hq2' | hqe
        · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2'
          exact (hq2 this).elim
        · exact hqe
      have hqy : q ∣ y.natAbs := Int.natCast_dvd.mp hqyZ
      have hqdiff : q ∣ (2 - (e : ℤ)).natAbs := by
        rw [show y.natAbs = p * (2 - (e : ℤ)).natAbs by
          simp [y, Int.natAbs_mul]] at hqy
        exact (hq.dvd_mul.mp hqy).resolve_left hqnp
      have hqdiffZ : (q : ℤ) ∣ 2 - (e : ℤ) := Int.natCast_dvd.mpr hqdiff
      have hqeZ : (q : ℤ) ∣ (e : ℤ) := by exact_mod_cast hqe
      have hq2Z : (q : ℤ) ∣ (2 : ℤ) := by
        simpa only [sub_add_cancel] using hqdiffZ.add hqeZ
      have hq2Nat : q ∣ 2 := by exact_mod_cast hq2Z
      have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2Nat
      exact hq2 this
  · have hqpEq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    subst q
    have hpyZ : (p : ℤ) ∣ y := by
      dsimp [y]
      exact dvd_mul_right _ _
    have hpjdZ : (p : ℤ) ∣ ((j * d : ℕ) : ℤ) := by
      have := hqtermZ.sub hpyZ
      simpa only [add_sub_cancel_left] using this
    have hpjd : p ∣ j * d := by exact_mod_cast hpjdZ
    rcases hp.dvd_mul.mp hpjd with hpj | hpd
    · have := Nat.le_of_dvd hjpos hpj
      omega
    · exact (hp.coprime_iff_not_dvd.mp hdp.symm) hpd

def actualSourceCorrectionRealization :
    PrimitiveRealization (cutSignature Bool Bool) :=
  sourceCorrectionRealization (fun x : Bool => x)

def alternateSourceCorrectionRealization :
    PrimitiveRealization (cutSignature Bool Bool) :=
  sourceCorrectionRealization (fun _ => true)


private theorem sourceCorrection_sensitivity_core :
    sourceCorrectionArena.Law actualSourceCorrectionRealization ∧
      FiniteSlotSensitivity sourceCorrectionArena ∧
      FiniteLawVariation sourceCorrectionArena := by
  suffices actualLaw : sourceCorrectionArena.Law actualSourceCorrectionRealization by
    have alternateNotLaw : ¬ sourceCorrectionArena.Law alternateSourceCorrectionRealization := by
      intro h
      have hpf : (30 : ℕ).primeFactors = {2, 3, 5} := by
        rw [show (30 : ℕ) = 2 * (3 * 5) by norm_num]
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
        rw [Nat.primeFactors_mul (by norm_num) (by norm_num)]
        ext q
        simp [Nat.prime_two.primeFactors, (by decide : Nat.Prime 3).primeFactors,
          (by decide : Nat.Prime 5).primeFactors]
        constructor
        · intro hq
          rcases hq with rfl | rfl | rfl <;> simp
        · intro hq
          rcases hq with rfl | rfl | rfl <;> simp
      have hsq : Squarefree (30 : ℕ) := by
        rw [show (30 : ℕ) = 2 * (3 * 5) by norm_num]
        rw [Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
        exact ⟨by decide, Nat.prime_two.squarefree, by decide,
          (by decide : Nat.Prime 3).squarefree, (by decide : Nat.Prime 5).squarefree⟩
      have hcard : 3 ≤ (30 : ℕ).primeFactors.card := by
        rw [hpf]
        norm_num
      have hshort : 30 / GreatestPrimeFactor 30 < 2 * GreatestPrimeFactor 30 := by
        rw [GreatestPrimeFactor, hpf]
        norm_num
      have h30 := h 30 (by norm_num) hsq hcard hshort
      dsimp [sourceCorrectionArena, alternateSourceCorrectionRealization,
        sourceCorrectionRealization, cutRealization, decodeSourceCorrection,
        GreatestPrimeFactor, hpf] at h30
      have hfloor := h30.2
      norm_num [sourceCorrectionArena, alternateSourceCorrectionRealization,
        sourceCorrectionRealization, cutRealization, decodeSourceCorrection,
        GreatestPrimeFactor, hpf] at hfloor
    refine ⟨actualLaw, ?_, ⟨actualSourceCorrectionRealization,
      alternateSourceCorrectionRealization, actualLaw, alternateNotLaw⟩⟩
    constructor
    · intro i
      cases i
      refine ⟨actualSourceCorrectionRealization, alternateSourceCorrectionRealization,
        ?_, ?_, ?_⟩
      · intro j hne
        exact (hne rfl).elim
      · intro j
        exact Fin.elim0 j
      · exact ⟨fun _ => alternateNotLaw, fun _ => actualLaw⟩
    · intro i
      exact Fin.elim0 i
  intro n hn_even hn_squarefree hn_factors hn_short
  let p := GreatestPrimeFactor n
  let d := n / p
  change IsGreatest {s : ℕ | AdmissibleLength n s} (p - 1 - (2 * p / d)) ∧
    ⌊(p : ℚ) - (2 * p : ℚ) / d⌋ = (p - 1 - (2 * p / d) : ℕ)
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    simp at hn_factors
  have hn_gt1 : 1 < n := by
    by_contra h
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp at hn_factors
  have hpf_nonempty : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn_gt1
  have hp_mem : p ∈ n.primeFactors := by
    have hmem := Finset.sup_mem_of_nonempty (s := n.primeFactors) (f := id) hpf_nonempty
    simpa [p, GreatestPrimeFactor] using hmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hpdiv : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
  have hfactor_le : ∀ q ∈ n.primeFactors, q ≤ p := by
    intro q hq
    simpa [p, GreatestPrimeFactor] using (Finset.le_sup (f := id) hq)
  have hp5 : 5 ≤ p := by
    by_contra hp5
    have hsubset : n.primeFactors ⊆ {2, 3} := by
      intro q hq
      have hqprime := Nat.prime_of_mem_primeFactors hq
      have hqle := hfactor_le q hq
      have hqlt : q < 5 := by omega
      have hq2 := hqprime.two_le
      have hqne4 : q ≠ 4 := by
        intro hq4
        subst q
        norm_num at hqprime
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcard := Finset.card_le_card hsubset
    norm_num at hcard
    omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hnfac : n = d * p := by
    dsimp [d]
    exact (Nat.div_mul_cancel hpdiv).symm
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn_ne
  have hdpos : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    rw [hnfac, this] at hnpos
    simp at hnpos
  have hsdp : Squarefree (d * p) := by simpa [← hnfac] using hn_squarefree
  have hd_squarefree : Squarefree d := hsdp.of_mul_left
  have hdp : d.Coprime p := Nat.coprime_of_squarefree_mul hsdp
  have hd_even0 : Even d := by
    have htwo : 2 ∣ d * p := by
      rw [← hnfac]
      exact even_iff_two_dvd.mp hn_even
    rcases Nat.prime_two.dvd_mul.mp htwo with htwo | htwo
    · exact even_iff_two_dvd.mpr htwo
    · have : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp htwo
      omega
  obtain ⟨e, he⟩ := hd_even0
  have hde : d = 2 * e := by omega
  have hd_even : Even d := hde ▸ even_two_mul e
  have hd6 : 6 ≤ d := by
    by_contra hd6
    have hd_cases : d = 2 ∨ d = 4 := by
      have := hdpos
      have := even_iff_two_dvd.mp hd_even
      omega
    rcases hd_cases with hd2 | hd4
    · have hpf : n.primeFactors = {2, p} := by
        rw [hnfac, hd2, Nat.primeFactors_mul (by norm_num) hp.ne_zero,
          Nat.prime_two.primeFactors, hp.primeFactors]
        ext q
        simp
      rw [hpf] at hn_factors
      have hpne : p ≠ 2 := by omega
      have h2not : 2 ∉ ({p} : Finset ℕ) := by simpa using hpne.symm
      have hcard : ({2, p} : Finset ℕ).card = 2 := by
        rw [Finset.card_insert_of_notMem h2not]
        simp
      rw [hcard] at hn_factors
      omega
    · have hnot := Nat.squarefree_iff_prime_squarefree.mp hd_squarefree 2 Nat.prime_two
      exact (hnot (by omega))
  have he3 : 3 ≤ e := by omega
  have heodd : Odd e := by
    have htwoe : Nat.Coprime 2 e := by
      apply Nat.coprime_of_squarefree_mul
      simpa [hde] using hd_squarefree
    apply Nat.not_even_iff_odd.mp
    intro heven
    exact (Nat.prime_two.coprime_iff_not_dvd.mp htwoe) (even_iff_two_dvd.mp heven)
  have hprime_lt : ∀ q ∈ d.primeFactors, q < p := by
    intro q hqd
    have hqprime := Nat.prime_of_mem_primeFactors hqd
    have hqdivd := Nat.dvd_of_mem_primeFactors hqd
    have hqdivn : q ∣ n := hnfac.symm ▸ dvd_mul_of_dvd_left hqdivd p
    have hqn : q ∈ n.primeFactors := hqprime.mem_primeFactors hqdivn hn_ne
    have hqle := hfactor_le q hqn
    have hqne : q ≠ p := by
      intro hqp
      subst q
      exact (hp.coprime_iff_not_dvd.mp hdp.symm) hqdivd
    omega
  have hrem : ¬d ∣ 2 * p := by
    intro hdiv
    have hd2 : d ∣ 2 := hdp.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdiv)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by omega) hd2
    omega
  have hquot : 2 * p / d + 1 ≤ p := by
    let r := 2 * p / d
    have hrmul : r * d ≤ 2 * p := by
      dsimp [r]
      exact Nat.div_mul_le_self _ _
    have hsix : 6 * r ≤ d * r := Nat.mul_le_mul_right r hd6
    have hthree : 3 * r ≤ p := by nlinarith [hrmul, hsix]
    dsimp [r] at hthree ⊢
    omega
  constructor
  · constructor
    · exact attained_progression hnfac hde he3 heodd hp hdp hn_short
    · intro s hs
      obtain ⟨a, h, hhpos, ha⟩ := hs
      by_cases hdh : d ∣ h
      · obtain ⟨t, ht⟩ := hdh
        have hht : h = t * d := by rw [ht]; ring
        have htpos : 0 < t := by
          apply Nat.pos_of_ne_zero
          intro ht0
          subst t
          simp [hht] at hhpos
        by_cases ht1 : t = 1
        · subst t
          apply no_long_progression_of_step hnfac hde he3 heodd hp hdp hn_short
          simpa [hht] using ha
        · have ht2 : 2 ≤ t := by omega
          by_cases hs0 : s = 0
          · omega
          · exact no_long_progression_of_large_multiple hnfac hd_even hd6 hp5 hn_short
              hht ht2 (Nat.pos_of_ne_zero hs0) ha
      · exact no_long_progression_of_missing_prime hnfac hd_even hd_squarefree hd6 hn_short
          hprime_lt hdh hhpos ha
  · exact source_floor_identity hdpos hrem hquot

private theorem sourceCorrection_sensitivity : FiniteSlotSensitivity sourceCorrectionArena :=
  sourceCorrection_sensitivity_core.2.1

private theorem sourceCorrection_variation : FiniteLawVariation sourceCorrectionArena :=
  sourceCorrection_sensitivity_core.2.2

/- The source conjecture: for an even squarefree modulus with at least three
prime factors and short complementary factor, the stated length is attained,
bounds every positive-step progression, and equals the source's rational floor. -/
information_theorem result in sourceCorrectionArena
  readout via (sourceCorrectionRealization (fun x : Bool => x))
  primitives actualSourceCorrectionRealization
  variation sourceCorrection_variation sensitivity sourceCorrection_sensitivity
  escape from (SourceCorrection) escape continues (open)
  : ∀ (n : ℕ), Even n → Squarefree n →
      3 ≤ n.primeFactors.card →
      n / GreatestPrimeFactor n < 2 * GreatestPrimeFactor n →
      let p := GreatestPrimeFactor n
      let d := n / p
      IsGreatest {s : ℕ | AdmissibleLength n s}
          (decodeSourceCorrection SourceCorrection p (2 * p / d)) ∧
        ⌊(p : ℚ) - (2 * p : ℚ) / d⌋ =
          (decodeSourceCorrection SourceCorrection p (2 * p / d) : ℕ) := by
  intro n hn_even hn_squarefree hn_factors hn_short
  have h := sourceCorrection_sensitivity_core.1 n hn_even hn_squarefree
    hn_factors hn_short
  simpa [sourceCorrectionArena, actualSourceCorrectionRealization,
    sourceCorrectionRealization, cutRealization, SourceCorrection] using h
end D5.S3.ArithUnits.CenteredReducedResidueProgressions
