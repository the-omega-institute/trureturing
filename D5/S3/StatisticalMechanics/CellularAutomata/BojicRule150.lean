/- GID: D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/BojicRule150
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Rule 150 semisimple local orders have LCM q for admissible Mersenne q. -/

import Mathlib

/-!
# Bojić's Rule 150 local-order identity

The factor indexed by `f` is the quotient by `f ^ (2 ^ m)`.
Reduction to the quotient by `f` identifies the order of the unique odd-order
factor in the semisimple–unipotent decomposition. The lower bound on the LCM
comes from a polynomial of degree at most twice the proposed exponent.

Source-bound Reg audits are pending for `project_eq_zero`, `project_X_pow`,
`local_pow_eq_of_reduce_eq`, `reduce_eq_of_isSemisimplePart`, and
`semisimple_order_eq_residue_order`. Each needs a typed source binding with
variation, sensitivity, and dependence evidence. [#35075](https://github.com/the-omega-institute/trureturing/issues/35075)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial UniqueFactorizationMonoid

namespace D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150

noncomputable section

abbrev P := Polynomial (ZMod 2)

abbrev Mod (f : P) := P ⧸ Ideal.span {f}

def project (f : P) : P →+* Mod f := Ideal.Quotient.mk _

def cycle (q : ℕ) : P := X ^ q - 1

def multiplier (n : ℕ) : P := 1 + X + X ^ (n - 1)

def quadratic : P := 1 + X + X ^ 2

def factors (q : ℕ) : Finset P := (normalizedFactors (cycle q)).toFinset

def nontrivialFactors (q : ℕ) : Finset P := (factors q).erase (X + 1)

private theorem cycle_ne_zero {q : ℕ} (hq : 0 < q) : cycle q ≠ 0 := by
  simpa [cycle] using X_pow_sub_C_ne_zero hq (1 : ZMod 2)

private theorem mem_factors {q : ℕ} (hq : 0 < q) {f : P} :
    f ∈ factors q ↔ Irreducible f ∧ f.Monic ∧ f ∣ cycle q := by
  rw [factors, Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff (cycle_ne_zero hq)]

@[simp] theorem project_eq_zero {f p : P} : project f p = 0 ↔ f ∣ p :=
  Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

private theorem mem_nontrivialFactors {q : ℕ} (hq : 0 < q) {f : P} :
    f ∈ nontrivialFactors q ↔ f ≠ X + 1 ∧ Irreducible f ∧ f.Monic ∧ f ∣ cycle q := by
  rw [nontrivialFactors, Finset.mem_erase, mem_factors hq]

theorem project_X_pow {f : P} {q : ℕ} (hf : f ∣ cycle q) :
    project f X ^ q = 1 := by
  have h := project_eq_zero.mpr hf
  simpa [cycle, map_sub, sub_eq_zero] using h

private theorem project_multiplier_mul_X {f : P} {q n : ℕ}
    (hf : f ∣ cycle q) (hqn : q ∣ n) (hn : 0 < n) :
    project f (multiplier n) * project f X = project f quadratic := by
  have hpow : project f X ^ n = 1 := by
    obtain ⟨c, rfl⟩ := hqn
    rw [pow_mul, project_X_pow hf, one_pow]
  have hlast : project f X ^ (n - 1) * project f X = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, hpow]
  simp only [multiplier, quadratic, map_add, map_pow, map_one, add_mul, one_mul, hlast]
  ring

private theorem mersenne_pos (k : ℕ) (hk : 0 < k) : 0 < 2 ^ k - 1 := by
  have h : 1 < (2 : ℕ) ^ k := one_lt_pow₀ (by decide) (Nat.ne_of_gt hk)
  omega

private theorem mersenne_succ (k : ℕ) : (2 ^ k - 1) + 1 = 2 ^ k :=
  Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))

private theorem mersenne_odd (k : ℕ) (hk : 0 < k) : Odd (2 ^ k - 1) := by
  have h : Even ((2 : ℕ) ^ k) := Nat.even_pow.mpr ⟨by decide, Nat.ne_of_gt hk⟩
  have hmod := Nat.even_iff.mp h
  have hpos := mersenne_pos k hk
  rw [Nat.odd_iff]
  omega

private theorem pow_mersenne_succ {M : Type*} [Monoid M] {x : M} {k : ℕ}
    (h : x ^ (2 ^ k - 1) = 1) : x ^ (2 ^ k) = x := by
  rw [← mersenne_succ k, pow_succ, h, one_mul]

/-- The residue of the actual Rule 150 multiplier has order dividing the Mersenne odd part. -/
private theorem residue_pow_eq_one (k n : ℕ)
    (h3 : ¬ 3 ∣ 2 ^ k - 1) (hqn : (2 ^ k - 1) ∣ n) (hn : 0 < n)
    {f : P} (hi : Irreducible f) (hf : f ∣ cycle (2 ^ k - 1)) :
    project f (multiplier n) ^ (2 ^ k - 1) = 1 := by
  let : (Ideal.span {f}).IsMaximal :=
    (Ideal.irreducible_iff_isMaximal_span_singleton hi.ne_zero).mp hi
  let : Field (Mod f) := Ideal.Quotient.field _
  let : CharP (Mod f) 2 := CharP.of_ringHom_of_ne_zero (project f) 2 (by decide)
  let a : Mod f := project f X
  let g : Mod f := project f (multiplier n)
  have haq : a ^ (2 ^ k - 1) = 1 := project_X_pow hf
  have htwo : (1 : Mod f) + 1 = 0 := by
    simpa only [Nat.cast_ofNat, one_add_one_eq_two] using CharP.cast_eq_zero (Mod f) 2
  have hunit : g ≠ 0 := by
    intro hg
    have hga : g * a = 1 + a + a ^ 2 := by
      simpa only [quadratic, map_add, map_one, map_pow] using
        project_multiplier_mul_X hf hqn hn
    have hs : 1 + a + a ^ 2 = 0 := by rw [← hga, hg, zero_mul]
    have ha3 : a ^ 3 = 1 := by
      linear_combination (a - 1) * hs
    have ho3 := orderOf_dvd_iff_pow_eq_one.mpr ha3
    have hoq := orderOf_dvd_iff_pow_eq_one.mpr haq
    have ha : a = 1 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp ho3 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact (h3 (h ▸ hoq)).elim
    simp [ha, htwo] at hs
  have haf : a ^ (2 ^ k) = a := pow_mersenne_succ haq
  have hgf : g ^ (2 ^ k) = g := by
    change (project f (1 + X + X ^ (n - 1))) ^ (2 ^ k) = _
    simp only [map_add, map_one, map_pow]
    change (1 + a + a ^ (n - 1)) ^ (2 ^ k) = 1 + a + a ^ (n - 1)
    rw [add_pow_char_pow, add_pow_char_pow, one_pow, haf,
      ← pow_mul, Nat.mul_comm (n - 1), pow_mul, haf]
  rw [← mersenne_succ k, pow_succ] at hgf
  exact mul_right_cancel₀ hunit (hgf.trans (one_mul g).symm)

private theorem X_sub_one : (X : P) - 1 = X + 1 := by
  have htwo : (1 : P) + 1 = 0 := by
    simpa only [Nat.cast_ofNat, one_add_one_eq_two] using CharP.cast_eq_zero P 2
  linear_combination -htwo

/-- For odd part one the nontrivial factor set is empty. -/
@[simp] private theorem nontrivialFactors_one : nontrivialFactors 1 = ∅ := by
  have hcycle : cycle 1 = (X : P) - C 1 := by simp [cycle]
  have hi : Irreducible (cycle 1) := hcycle ▸ irreducible_X_sub_C (1 : ZMod 2)
  have hm : (cycle 1).Monic := hcycle ▸ monic_X_sub_C (1 : ZMod 2)
  have ht : cycle 1 = X + 1 := by simpa [cycle] using X_sub_one
  rw [nontrivialFactors, factors, normalizedFactors_irreducible hi, hm.normalize_eq_self, ht]
  simp

private theorem trivial_residue (n : ℕ) : project (X + 1) (multiplier n) = 1 := by
  have htwo : (1 : P) + 1 = 0 := by
    simpa only [Nat.cast_ofNat, one_add_one_eq_two] using CharP.cast_eq_zero P 2
  have hx : project (X + 1) X = 1 := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem X 1).mpr
    rw [Ideal.mem_span_singleton]
    rw [X_sub_one]
  have htwo' := congrArg (project (X + 1)) htwo
  simp only [map_add, map_one, map_zero] at htwo'
  simp [multiplier, hx, add_assoc, htwo']

/-- Squarefreeness combines divisibility by all distinct monic irreducible factors. -/
private theorem cycle_dvd_of_factors {q : ℕ} (hq : Odd q) {p : P}
    (h : ∀ f ∈ factors q, f ∣ p) : cycle q ∣ p := by
  by_cases hp : p = 0
  · simp [hp]
  have hc := cycle_ne_zero hq.pos
  have hqcast : (q : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp hq]
    decide
  have hs : Squarefree (cycle q) := by
    simpa [cycle] using (separable_X_pow_sub_C 1 hqcast one_ne_zero).squarefree
  have hnodup := (squarefree_iff_nodup_normalizedFactors hc).mp hs
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hc hp).mpr
  apply (Multiset.le_iff_subset hnodup).mpr
  intro f hf
  have ⟨hirr, hmonic, _⟩ := (Polynomial.mem_normalizedFactors_iff hc).mp hf
  exact (Polynomial.mem_normalizedFactors_iff hp).mpr
    ⟨hirr, hmonic, h f (Multiset.mem_toFinset.mpr hf)⟩

/-- A common exponent of the residues on the nontrivial factors has twice its size at least `q`. -/
private theorem degree_le_of_common_residue_exponent {q n d : ℕ} (hq : Odd q)
    (hqn : q ∣ n) (hn : 0 < n) (hd : 0 < d)
    (h : ∀ f ∈ nontrivialFactors q, project f (multiplier n) ^ d = 1) : q ≤ 2 * d := by
  let p : P := quadratic ^ d - X ^ d
  have hp : p ≠ 0 := by
    intro hzero
    have he := congrArg (evalRingHom (0 : ZMod 2)) hzero
    simp [p, quadratic, Nat.ne_of_gt hd] at he
  have hpdvd : cycle q ∣ p := by
    apply cycle_dvd_of_factors hq
    intro f hf
    have hfdvd := ((mem_factors hq.pos).mp hf).2.2
    have hlocal : project f (multiplier n) ^ d = 1 := by
      by_cases htriv : f = X + 1
      · subst f
        rw [trivial_residue, one_pow]
      · exact h f (Finset.mem_erase.mpr ⟨htriv, hf⟩)
    apply project_eq_zero.mp
    change project f (quadratic ^ d - X ^ d) = 0
    rw [map_sub, map_pow, map_pow, ← project_multiplier_mul_X hfdvd hqn hn,
      mul_pow, hlocal, one_mul, sub_self]
  have hquad : quadratic.natDegree ≤ 2 := by
    unfold quadratic
    refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  have hdeg : p.natDegree ≤ 2 * d := by
    change (quadratic ^ d - X ^ d).natDegree ≤ 2 * d
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simpa only [Nat.mul_comm] using natDegree_pow_le_of_le d hquad
    · rw [natDegree_X_pow]
      omega
  have hcycle : (cycle q).natDegree = q := by
    simpa [cycle] using (natDegree_X_pow_sub_C (R := ZMod 2) (n := q) (r := 1))
  exact hcycle ▸ (natDegree_le_of_dvd hpdvd hp).trans hdeg

/-- The exact LCM of the orders of the Rule 150 residues on the nontrivial factors. -/
private theorem residueOrder_lcm (k n : ℕ) (hk : 0 < k)
    (h3 : ¬ 3 ∣ 2 ^ k - 1) (hqn : (2 ^ k - 1) ∣ n) (hn : 0 < n) :
    (nontrivialFactors (2 ^ k - 1)).lcm (fun f => orderOf (project f (multiplier n))) =
      2 ^ k - 1 := by
  let q := 2 ^ k - 1
  let d := (nontrivialFactors q).lcm (fun f => orderOf (project f (multiplier n)))
  have hq := mersenne_odd k hk
  have hdvd : d ∣ q := by
    apply Finset.lcm_dvd
    intro f hf
    have hi := (mem_factors hq.pos).mp (Finset.mem_erase.mp hf).2
    exact orderOf_dvd_iff_pow_eq_one.mpr (residue_pow_eq_one k n h3 hqn hn hi.1 hi.2.2)
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hq.pos
  have hbound : q ≤ 2 * d := by
    apply degree_le_of_common_residue_exponent hq hqn hn hd
    intro f hf
    exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_lcm hf)
  obtain ⟨c, hc⟩ := hdvd
  have hcOdd : Odd c := hq.of_dvd_nat ⟨d, by simpa [Nat.mul_comm] using hc⟩
  have hcle : c ≤ 2 := by
    apply Nat.le_of_mul_le_mul_left _ hd
    rw [← hc, Nat.mul_comm d]
    exact hbound
  have hone : c = 1 := by
    have := Nat.odd_iff.mp hcOdd
    omega
  change d = q
  simpa [hone] using hc.symm

/-- The primary factor of thickness `2 ^ m` in the source's CRT decomposition. -/
abbrev Local (f : P) (m : ℕ) := Mod (f ^ (2 ^ m))

private theorem localIdeal_le_residueIdeal (f : P) (m : ℕ) :
    Ideal.span {f ^ (2 ^ m)} ≤ Ideal.span {f} :=
  Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self f (by positivity))

/-- Reduction from the primary factor to its residue modulo `f`. -/
def reduce (f : P) (m : ℕ) : Local f m →+* Mod f :=
  Ideal.Quotient.factor (localIdeal_le_residueIdeal f m)

@[simp] private theorem reduce_project (f p : P) (m : ℕ) :
    reduce f m (project (f ^ (2 ^ m)) p) = project f p :=
  Ideal.Quotient.factor_mk _ _

/-- Congruence modulo `f` becomes equality after raising to the thickness. -/
theorem local_pow_eq_of_reduce_eq {f : P} {m : ℕ} {x y : Local f m}
    (h : reduce f m x = reduce f m y) : x ^ (2 ^ m) = y ^ (2 ^ m) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  change reduce f m (project (f ^ (2 ^ m)) p) = reduce f m (project (f ^ (2 ^ m)) r) at h
  rw [reduce_project, reduce_project] at h
  have hdvd : f ∣ p - r := project_eq_zero.mp (by rw [map_sub, h, sub_self])
  have hzero := project_eq_zero.mpr (pow_dvd_pow_of_dvd hdvd (2 ^ m))
  have hsub : (p - r) ^ (2 ^ m) = p ^ (2 ^ m) - r ^ (2 ^ m) :=
    sub_pow_char_pow p r m
  change project (f ^ (2 ^ m)) p ^ (2 ^ m) = project (f ^ (2 ^ m)) r ^ (2 ^ m)
  simpa only [hsub, map_sub, map_pow, sub_eq_zero] using hzero

/-- Reduction preserves the full order of every odd-order element of the primary factor. -/
private theorem orderOf_reduce_eq {f : P} {m : ℕ} {s : Local f m} (hs : Odd (orderOf s)) :
    orderOf (reduce f m s) = orderOf s := by
  apply Nat.dvd_antisymm (orderOf_map_dvd (reduce f m).toMonoidHom s)
  have hpow : (reduce f m s) ^ orderOf (reduce f m s) = 1 := pow_orderOf_eq_one _
  have heq : reduce f m (s ^ orderOf (reduce f m s)) = reduce f m 1 := by
    rw [map_pow, map_one, hpow]
  have hlocal := local_pow_eq_of_reduce_eq heq
  rw [one_pow, ← pow_mul] at hlocal
  have hc := (Nat.coprime_two_right.mpr hs).pow_right m
  exact hc.dvd_of_dvd_mul_right (orderOf_dvd_iff_pow_eq_one.mpr hlocal)

/-- The source's semisimple factor is an odd-order unit with a unipotent cofactor
whose nilpotent difference from one lies in the residue kernel. -/
def IsSemisimplePart {f : P} {m : ℕ} (g s : Local f m) : Prop :=
  IsUnit s ∧ Odd (orderOf s) ∧
    ∃ ν : Local f m, reduce f m ν = 0 ∧ IsNilpotent ν ∧ g = s * (1 + ν)

theorem reduce_eq_of_isSemisimplePart {f : P} {m : ℕ} {g s : Local f m}
    (hs : IsSemisimplePart (f := f) (m := m) g s) : reduce f m s = reduce f m g := by
  obtain ⟨_, _, ν, hν, _, hg⟩ := hs
  rw [hg, map_mul, map_add, map_one, hν, add_zero, mul_one]

/-- This applies to any decomposition with the properties in the source's Theorem 8.8. -/
theorem semisimple_order_eq_residue_order {f : P} {m : ℕ} {g s : Local f m}
    (hs : IsSemisimplePart (f := f) (m := m) g s) :
    orderOf s = orderOf (reduce f m g) :=
  (orderOf_reduce_eq hs.2.1).symm.trans (congrArg orderOf (reduce_eq_of_isSemisimplePart hs))

/-- The class of the actual `n`-cycle multiplier in the primary factor. -/
def localMultiplier (n : ℕ) (f : P) (m : ℕ) : Local f m :=
  project (f ^ (2 ^ m)) (multiplier n)

/-- An explicit representative of the semisimple factor for Mersenne odd part. -/
def semisimplePart (k m : ℕ) (f : P) : Local f m :=
  localMultiplier (2 ^ m * (2 ^ k - 1)) f m ^ ((2 ^ k) ^ m)

private theorem pow_mersenne_iterate {M : Type*} [Monoid M] {x : M} {k : ℕ}
    (hx : x ^ (2 ^ k - 1) = 1) (m : ℕ) : x ^ ((2 ^ k) ^ m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, ih, pow_mersenne_succ hx]

/-- Existence and uniqueness of the source's odd-order part for the actual local multiplier. -/
theorem semisimplePart_spec (k m : ℕ) (h3 : ¬ 3 ∣ 2 ^ k - 1)
    {f : P} (hf : f ∈ factors (2 ^ k - 1)) :
    IsSemisimplePart (f := f) (m := m)
        (localMultiplier (2 ^ m * (2 ^ k - 1)) f m) (semisimplePart k m f) ∧
      ∀ s, IsSemisimplePart (f := f) (m := m)
        (localMultiplier (2 ^ m * (2 ^ k - 1)) f m) s → s = semisimplePart k m f := by
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk
    subst k
    exact h3 (by simp)
  let q := 2 ^ k - 1
  let n := 2 ^ m * q
  let g := localMultiplier n f m
  let s := semisimplePart k m f
  have hq : 0 < q := mersenne_pos k hk
  have hqn : q ∣ n := by
    use 2 ^ m
    exact Nat.mul_comm _ _
  have hn : 0 < n := by dsimp [n]; positivity
  have hfactor := (mem_factors hq).mp hf
  have hres : (reduce f m g) ^ q = 1 := by
    simp only [g, localMultiplier, reduce_project]
    exact residue_pow_eq_one k n h3 hqn hn hfactor.1 hfactor.2.2
  have hgs : g ^ ((2 ^ k) ^ m) = s := rfl
  have hrs : reduce f m s = reduce f m g := by
    rw [← hgs, map_pow, pow_mersenne_iterate hres]
  have hkernel : g ^ (q * 2 ^ m) = 1 := by
    have h : reduce f m (g ^ q) = reduce f m 1 := by rw [map_pow, map_one, hres]
    simpa only [one_pow, pow_mul] using local_pow_eq_of_reduce_eq h
  have hthick : 2 ^ m ∣ (2 ^ k) ^ m := by
    rw [← pow_mul]
    apply Nat.pow_dvd_pow
    simpa using Nat.mul_le_mul_right m hk
  have hsq : s ^ q = 1 := by
    rw [← hgs, ← pow_mul, Nat.mul_comm _ q, pow_mul]
    have hkernel' : (g ^ q) ^ (2 ^ m) = 1 := by rwa [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp
      (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr hkernel') hthick)
  have hodd := (mersenne_odd k hk).of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hsq)
  let w := s ^ (q - 1) * g
  have hsinv : s * s ^ (q - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hq, hsq]
  have hsw : s * w = g := by
    change s * (s ^ (q - 1) * g) = g
    rw [← mul_assoc, hsinv, one_mul]
  have hw : reduce f m w = 1 := by
    change reduce f m (s ^ (q - 1) * g) = 1
    rw [map_mul, ← hrs, ← map_mul, mul_comm, hsinv, map_one]
  have hν : reduce f m (w - 1) = 0 := by rw [map_sub, hw, map_one, sub_self]
  have hnil : IsNilpotent (w - 1) := by
    refine ⟨2 ^ m, ?_⟩
    have hz : reduce f m (w - 1) = reduce f m 0 := by simpa using hν
    simpa [zero_pow (show 2 ^ m ≠ 0 by positivity)] using local_pow_eq_of_reduce_eq hz
  refine ⟨⟨IsUnit.of_mul_eq_one _ hsinv, hodd, w - 1, hν, hnil, ?_⟩, ?_⟩
  · rw [show 1 + (w - 1) = w by ring, hsw]
  · intro t ht
    change t = s
    have hrt := reduce_eq_of_isSemisimplePart ht
    have htq : t ^ q = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [← orderOf_reduce_eq ht.2.1, hrt]
      exact orderOf_dvd_iff_pow_eq_one.mpr hres
    have heq : t ^ (2 ^ m) = s ^ (2 ^ m) :=
      local_pow_eq_of_reduce_eq (hrt.trans hrs.symm)
    obtain ⟨c, hc⟩ := hthick
    have hpowers : t ^ ((2 ^ k) ^ m) = s ^ ((2 ^ k) ^ m) := by
      rw [hc, pow_mul, pow_mul, heq]
    simpa only [pow_mersenne_iterate htq, pow_mersenne_iterate hsq] using hpowers

/-- The source's local semisimple order agrees with the ordinary residue order. -/
theorem semisimplePart_order (k m : ℕ) (h3 : ¬ 3 ∣ 2 ^ k - 1)
    {f : P} (hf : f ∈ factors (2 ^ k - 1)) :
    orderOf (semisimplePart k m f) =
      orderOf (project f (multiplier (2 ^ m * (2 ^ k - 1)))) := by
  simpa only [localMultiplier, reduce_project] using
    semisimple_order_eq_residue_order (semisimplePart_spec k m h3 hf).1

/-- Bojić's exact LCM identity, with the odd-order parts of the actual local multipliers. -/
theorem semisimpleOrder_lcm (k m : ℕ) (h3 : ¬ 3 ∣ 2 ^ k - 1) :
    (nontrivialFactors (2 ^ k - 1)).lcm (fun f => orderOf (semisimplePart k m f)) =
      2 ^ k - 1 := by
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk
    subst k
    exact h3 (by simp)
  have hq := mersenne_pos k hk
  have hn : 0 < 2 ^ m * (2 ^ k - 1) := by positivity
  have hqn : (2 ^ k - 1) ∣ 2 ^ m * (2 ^ k - 1) := dvd_mul_left _ _
  calc
    _ = (nontrivialFactors (2 ^ k - 1)).lcm
          (fun f => orderOf (project f (multiplier (2 ^ m * (2 ^ k - 1))))) := by
        apply Finset.lcm_congr rfl
        intro f hf
        have hmem := (mem_nontrivialFactors hq).mp hf
        exact semisimplePart_order k m h3 ((mem_factors hq).mpr hmem.2)
    _ = 2 ^ k - 1 := residueOrder_lcm k _ hk h3 hqn hn

end

end D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150
