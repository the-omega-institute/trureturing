/- GID: D5/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/BojicThreeTerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three-distinct-offset cyclic branch has the preregistered local unipotent valuation and order. -/

import D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150

/-!
# Bojić's three-distinct-offset cyclic branch

The cycle has length `2 ^ m * q` with `q` odd. The primary factors are
indexed by irreducible factors of `X ^ q - 1`. The valuation of the local
unipotent factor minus one is the first positive Taylor degree capped at
the thickness `2 ^ m`. The dyadic case split in `preregisteredDegree`
scales the normalized first positive degree by the largest common power
of two dividing the three offsets.

The source-bound Reg audit for `piecewise_trinomial_interface` is pending.
It needs a bridge to the actual degree function over the full theorem
scope, with variation and dependence on valid cyclic inputs. [#35075](https://github.com/the-omega-institute/trureturing/issues/35075)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial
open D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150

namespace D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm

noncomputable section
open scoped Polynomial

private abbrev K (f : P) := AdjoinRoot f
private abbrev zeta (f : P) : K f := AdjoinRoot.root f
private abbrev kMap (f : P) : ZMod 2 →+* K f := AdjoinRoot.of f

private def jet (f : P) : P →+* (K f)[X] :=
  (taylorAlgHom (zeta f)).toRingHom.comp (Polynomial.mapRingHom (kMap f))

@[simp] private theorem jet_coeff_zero (f p : P) : (jet f p).coeff 0 = AdjoinRoot.mk f p := by
  change (taylor (zeta f) (p.map (kMap f))).coeff 0 = _
  rw [taylor_coeff_zero, ← eval₂_eq_eval_map]
  exact AdjoinRoot.aeval_eq (f := f) p

private theorem jet_f_coeff_one {f : P} [Nontrivial (K f)] (hf : f.Separable) :
    (jet f f).coeff 1 ≠ 0 := by
  change (taylor (zeta f) (f.map (kMap f))).coeff 1 ≠ 0
  rw [taylor_coeff_one, derivative_map, ← eval₂_eq_eval_map]
  apply hf.eval₂_derivative_ne_zero _
  change aeval (zeta f) f = 0
  rw [AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_eq_zero.mpr (dvd_refl f)

private theorem X_dvd_jet_iff (f p : P) : X ∣ jet f p ↔ f ∣ p := by
  rw [← pow_one (X : (K f)[X]), X_pow_dvd_iff]
  simp [AdjoinRoot.mk_eq_zero]

private theorem f_pow_dvd_iff_X_pow_dvd_jet {f : P} [IsDomain (K f)] (hf : f.Separable)
    (p : P) (n : ℕ) : f ^ n ∣ p ↔ X ^ n ∣ jet f p := by
  have hfcoeff := jet_f_coeff_one hf
  obtain ⟨u, hu⟩ := (X_dvd_jet_iff f f).2 (dvd_refl f)
  have hu' : ¬ X ∣ u := by
    intro h
    apply hfcoeff
    apply (X_pow_dvd_iff.mp ?_) 1 (by decide : 1 < 2)
    simpa [hu, pow_two, mul_assoc] using mul_dvd_mul_left X h
  have hX : Prime (X : (K f)[X]) := Polynomial.prime_X
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    constructor
    · intro h
      have h' := (map_dvd (jet f) h)
      rw [map_pow, hu, mul_pow] at h'
      exact dvd_trans (dvd_mul_right _ _) h'
    · intro h
      have hfp : f ∣ p := (X_dvd_jet_iff f p).1 (dvd_trans (dvd_pow_self _ (by omega)) h)
      obtain ⟨v, rfl⟩ := hfp
      rw [map_mul, hu, mul_assoc, pow_succ'] at h
      have h' : X ^ n ∣ u * jet f v := (mul_dvd_mul_iff_left (X_ne_zero : (X : (K f)[X]) ≠ 0)).1 h
      have hj : X ^ n ∣ jet f v := hX.pow_dvd_of_dvd_mul_left n hu' h'
      rw [pow_succ']
      exact mul_dvd_mul_left _ ((ih v).2 hj)

private theorem f_separable_of_odd_cycle {q : ℕ} (hq : Odd q) {f : P} (hf : f ∣ cycle q) :
    f.Separable := by
  apply Polynomial.Separable.of_dvd _ hf
  simpa [cycle] using
    (separable_X_pow_sub_C' 2 q (1 : ZMod 2) (by simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hq)) one_ne_zero)

private def jetDifference (f p : P) : (K f)[X] :=
  jet f p - C (AdjoinRoot.mk f p)

private def FirstPositive (f p : P) (r : ℕ) : Prop :=
  0 < r ∧ (∀ i, 0 < i → i < r → (jet f p).coeff i = 0) ∧ (jet f p).coeff r ≠ 0

private theorem difference_pow_dvd_iff {f p : P} {r : ℕ} (hr : FirstPositive f p r) (n : ℕ) :
    X ^ n ∣ jetDifference f p ↔ n ≤ r := by
  have hcoeff (i : ℕ) (hi : i ≠ 0) :
      (jetDifference f p).coeff i = (jet f p).coeff i := by
    simp [jetDifference, coeff_C, hi]
  rw [X_pow_dvd_iff]
  constructor
  · intro h
    by_contra! hlt
    exact hr.2.2 ((hcoeff r (Nat.ne_of_gt hr.1)).symm.trans (h r hlt))
  · intro h i hi
    obtain rfl | hip := i.eq_zero_or_pos
    · simp [jetDifference]
    · exact (hcoeff i (Nat.ne_of_gt hip)).trans (hr.2.1 i hip (lt_of_lt_of_le hi h))

end

noncomputable section

private abbrev Trunc (f : P) (n : ℕ) := AdjoinRoot ((X : (K f)[X]) ^ n)
private abbrev trunc (f : P) (n : ℕ) : (K f)[X] →+* Trunc f n := AdjoinRoot.mk _
private abbrev liftConst (f : P) (n : ℕ) : K f →+* Trunc f n := AdjoinRoot.of _

private def localJet {f : P} [IsDomain (K f)] (hf : f.Separable)
    {m n : ℕ} (hn : n ≤ 2 ^ m) : Local f m →+* Trunc f n :=
  Ideal.Quotient.lift _ ((trunc f n).comp (jet f)) fun p hp =>
    AdjoinRoot.mk_eq_zero.mpr
      ((f_pow_dvd_iff_X_pow_dvd_jet hf p n).1
        ((pow_dvd_pow f hn).trans (Ideal.mem_span_singleton.mp hp)))

@[simp] private theorem localJet_project {f p : P} [IsDomain (K f)] (hf : f.Separable)
    {m n : ℕ} (hn : n ≤ 2 ^ m) :
    localJet hf hn (project (f ^ (2 ^ m)) p) = trunc f n (jet f p) := rfl

private theorem project_onto (f : P) : Function.Surjective (project f) :=
  Ideal.Quotient.mk_surjective

private theorem jet_difference_thickness {f : P} [IsDomain (K f)] {m : ℕ}
    (p : P) :
    trunc f (2 ^ m) (jet f p) ^ (2 ^ m) =
      liftConst f (2 ^ m) (AdjoinRoot.mk f p) ^ (2 ^ m) := by
  have h : X ∣ jetDifference f p := by
    rw [← pow_one (X : (K f)[X]), X_pow_dvd_iff]
    simp [jetDifference]
  let : CharP (K f) 2 := CharP.of_ringHom_of_ne_zero (kMap f) 2 (by decide)
  have hzero := (AdjoinRoot.mk_eq_zero (f := (X : (K f)[X]) ^ (2 ^ m))).mpr
    (pow_dvd_pow_of_dvd h (2 ^ m))
  change trunc f (2 ^ m) (jetDifference f p ^ (2 ^ m)) = 0 at hzero
  change _ = (trunc f (2 ^ m) (C (AdjoinRoot.mk f p))) ^ (2 ^ m)
  simpa only [jetDifference, sub_pow_char_pow, map_sub, map_pow, sub_eq_zero] using hzero

private theorem eq_of_powers_eq_of_odd_order {M : Type*} [CommMonoid M]
    {x y : M} {d m : ℕ} (hd : Odd d)
    (hx : x ^ d = 1) (hy : y ^ d = 1) (hxy : x ^ (2 ^ m) = y ^ (2 ^ m)) :
    x = y := by
  have hyu := IsUnit.of_pow_eq_one hy (Nat.ne_of_gt hd.pos)
  obtain ⟨yi, hyi⟩ := isUnit_iff_exists_inv.mp hyu
  have hyi_pow (n : ℕ) : y ^ n * yi ^ n = 1 := by rw [← mul_pow, hyi, one_pow]
  have hz : x * yi = 1 := by
    apply (pow_eq_one_iff_of_coprime ((Nat.coprime_two_right.mpr hd).pow_right m)).mp
    constructor
    · rw [mul_pow, hx, one_mul]
      simpa [hy] using hyi_pow d
    · rw [mul_pow, hxy, hyi_pow]
  calc
    x = x * (y * yi) := by rw [hyi, mul_one]
    _ = y * (x * yi) := mul_left_comm _ _ _
    _ = y := by rw [hz, mul_one]

private abbrev residue (f : P) (m : ℕ) : Local f m →+* K f := reduce f m

private theorem localJet_eq_const_of_odd_order {f : P} [IsDomain (K f)] (hf : f.Separable)
    {m n : ℕ} (hn : n ≤ 2 ^ m) (s : Local f m) (hs : Odd (orderOf s)) :
    localJet hf hn s = liftConst f n (residue f m s) := by
  have hzero (p : (K f)[X]) (hp : trunc f (2 ^ m) p = 0) : trunc f n p = 0 :=
    AdjoinRoot.mk_eq_zero.mpr
      ((pow_dvd_pow X hn).trans (AdjoinRoot.mk_eq_zero.mp hp))
  have hpow (p : P) :
      trunc f n (jet f p) ^ (2 ^ m) = liftConst f n (AdjoinRoot.mk f p) ^ (2 ^ m) := by
    have h := jet_difference_thickness (f := f) (m := m) p
    have h' : trunc f (2 ^ m) ((jet f p) ^ (2 ^ m) - (C (AdjoinRoot.mk f p)) ^ (2 ^ m)) = 0 := by
      simp only [map_sub, map_pow, sub_eq_zero]
      exact h
    change _ = (trunc f n (C (AdjoinRoot.mk f p))) ^ (2 ^ m)
    simpa only [map_sub, map_pow, sub_eq_zero] using hzero _ h'
  have hleft : (localJet hf hn s) ^ orderOf s = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hright : (liftConst f n (residue f m s)) ^ orderOf s = 1 := by
    have h := congrArg ((liftConst f n).comp (residue f m)) (pow_orderOf_eq_one s)
    simpa only [map_pow, map_one, RingHom.comp_apply] using h
  apply eq_of_powers_eq_of_odd_order hs hleft hright
  obtain ⟨p, rfl⟩ := project_onto _ s
  exact hpow p

private theorem truncated_valuation_iff {f G v : P} [IsDomain (K f)] (hf : f.Separable) {m r : ℕ}
    {s : Local f m} (hs : IsSemisimplePart (f := f) (m := m) (project (f ^ (2 ^ m)) G) s)
    (hv : project (f ^ (2 ^ m)) G = s * (1 + project (f ^ (2 ^ m)) v))
    (hr : FirstPositive f G r) (n : ℕ) (hn : n ≤ 2 ^ m) :
    f ^ n ∣ v ↔ n ≤ r := by
  -- Match the actual semisimple factor, then cancel its constant unit.
  have hconst := localJet_eq_const_of_odd_order hf hn s hs.2.1
  have hrs : residue f m s = AdjoinRoot.mk f G := by
    exact reduce_eq_of_isSemisimplePart hs
  have hmul := congrArg (localJet hf hn) hv
  simp only [localJet_project, map_mul, map_add, map_one, hconst, hrs] at hmul
  have hdiff : trunc f n (jetDifference f G) =
      liftConst f n (AdjoinRoot.mk f G) * trunc f n (jet f v) := by
    simp only [jetDifference, map_sub, hmul]
    change liftConst f n (AdjoinRoot.mk f G) * (1 + trunc f n (jet f v)) -
      liftConst f n (AdjoinRoot.mk f G) = _
    rw [mul_add, mul_one, add_sub_cancel_left]
  have hu : IsUnit (liftConst f n (AdjoinRoot.mk f G)) :=
    hrs ▸ (hs.1.map (residue f m)).map (liftConst f n)
  have heq : trunc f n (jetDifference f G) = 0 ↔ trunc f n (jet f v) = 0 := by
    rw [hdiff]
    exact ⟨fun h => hu.mul_right_inj.mp (h.trans (mul_zero _).symm), fun h => by rw [h, mul_zero]⟩
  exact ((f_pow_dvd_iff_X_pow_dvd_jet hf v n).trans AdjoinRoot.mk_eq_zero.symm).trans
    (heq.symm.trans (AdjoinRoot.mk_eq_zero.trans (difference_pow_dvd_iff hr n)))

end

noncomputable section

private theorem truncated_valuation {f G v : P} [IsDomain (K f)] (hf : f.Separable) {m r : ℕ}
    {s : Local f m} (hs : IsSemisimplePart (f := f) (m := m) (project (f ^ (2 ^ m)) G) s)
    (hv : project (f ^ (2 ^ m)) G = s * (1 + project (f ^ (2 ^ m)) v))
    (hr : FirstPositive f G r) (n : ℕ) :
    n ≤ min r (2 ^ m) ↔ n ≤ 2 ^ m ∧ f ^ n ∣ v := by
  rw [le_min_iff]
  exact ⟨fun ⟨hnr, hne⟩ => ⟨hne, (truncated_valuation_iff hf hs hv hr n hne).2 hnr⟩,
    fun ⟨hne, hd⟩ => ⟨(truncated_valuation_iff hf hs hv hr n hne).1 hd, hne⟩⟩

private theorem local_pow_iff_dvd (f v : P) (m k : ℕ) :
    (1 + project (f ^ (2 ^ m)) v) ^ (2 ^ k) = 1 ↔ f ^ (2 ^ m) ∣ v ^ (2 ^ k) := by
  have h : (1 + v) ^ (2 ^ k) = 1 + v ^ (2 ^ k) := by rw [add_pow_char_pow, one_pow]
  have hh := congrArg (project (f ^ (2 ^ m))) h
  simp only [map_pow, map_add, map_one] at hh
  rw [hh, add_eq_left, ← map_pow, project_eq_zero]

private theorem unipotent_pow_iff {f G v : P} [IsDomain (K f)] (hf : f.Separable) (hfi : Irreducible f)
    {m r : ℕ} {s : Local f m}
    (hs : IsSemisimplePart (f := f) (m := m) (project (f ^ (2 ^ m)) G) s)
    (hv : project (f ^ (2 ^ m)) G = s * (1 + project (f ^ (2 ^ m)) v))
    (hr : FirstPositive f G r) (k : ℕ) :
    (1 + project (f ^ (2 ^ m)) v) ^ (2 ^ k) = 1 ↔ 2 ^ m ≤ r * 2 ^ k := by
  rw [local_pow_iff_dvd]
  by_cases h : r < 2 ^ m
  · have hd := (truncated_valuation_iff hf hs hv hr r h.le).2 le_rfl
    have hnd : ¬ f ^ (r + 1) ∣ v :=
      (truncated_valuation_iff hf hs hv hr (r + 1) h).not.mpr (Nat.not_succ_le_self r)
    have hm := emultiplicity_eq_of_dvd_of_not_dvd hd hnd
    rw [pow_dvd_iff_le_emultiplicity, emultiplicity_pow hfi.prime, hm, ← Nat.cast_mul]
    exact_mod_cast (show (2 ^ m ≤ 2 ^ k * r) ↔ (2 ^ m ≤ r * 2 ^ k) by rw [Nat.mul_comm r])
  · have he : 2 ^ m ≤ r := Nat.le_of_not_gt h
    have hd := (truncated_valuation_iff hf hs hv hr (2 ^ m) le_rfl).2 he
    have hp : 1 ≤ (2 : ℕ) ^ k := Nat.two_pow_pos k
    have hle : 2 ^ m ≤ r * 2 ^ k := he.trans (by simpa using Nat.mul_le_mul_left r hp)
    exact iff_of_true (hd.trans (dvd_pow_self _ (pow_ne_zero _ (by decide)))) hle

private theorem unipotent_order {f G v : P} [IsDomain (K f)] (hf : f.Separable) (hfi : Irreducible f)
    {m r : ℕ} {s : Local f m}
    (hs : IsSemisimplePart (f := f) (m := m) (project (f ^ (2 ^ m)) G) s)
    (hv : project (f ^ (2 ^ m)) G = s * (1 + project (f ^ (2 ^ m)) v))
    (hr : FirstPositive f G r) :
    IsLeast {p : ℕ | (∃ k : ℕ, p = 2 ^ k) ∧ 2 ^ m ≤ r * p}
      (orderOf (1 + project (f ^ (2 ^ m)) v)) := by
  let u := 1 + project (f ^ (2 ^ m)) v
  have htop : u ^ (2 ^ m) = 1 := (unipotent_pow_iff hf hfi hs hv hr m).2 (by
    simpa using Nat.mul_le_mul_right (2 ^ m) (show 1 ≤ r from hr.1))
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (orderOf_dvd_of_pow_eq_one htop)
  refine ⟨⟨⟨k, hk⟩, ?_⟩, ?_⟩
  · rw [hk]
    exact (unipotent_pow_iff hf hfi hs hv hr k).1 (hk ▸ pow_orderOf_eq_one u)
  · rintro _ ⟨⟨j, rfl⟩, hj⟩
    exact Nat.le_of_dvd (by positivity)
      (orderOf_dvd_of_pow_eq_one ((unipotent_pow_iff hf hfi hs hv hr j).2 hj))

end

noncomputable section

def trinomial (a b c : ℕ) : P := X ^ a + X ^ b + X ^ c

private theorem semisimple_of_odd_residue_exponent {f : P} {m d : ℕ} {g : Local f m}
    (hd : Odd d) (hg : reduce f m g ^ d = 1) :
    ∃! s : Local f m, IsSemisimplePart (f := f) (m := m) g s := by
  let e := (2 : ℕ) ^ m
  let N := (d + 1) ^ m
  let s := g ^ N
  have hN : e ∣ N := by
    exact pow_dvd_pow_of_dvd (even_iff_two_dvd.mp hd.add_one) m
  have hrPow (i : ℕ) : (reduce f m g) ^ ((d + 1) ^ i) = reduce f m g := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_mul, ih, pow_succ, hg, one_mul]
  have hr : reduce f m s = reduce f m g := by
    change (reduce f m) (g ^ ((d + 1) ^ m)) = _
    rw [map_pow, hrPow]
  have hgD : g ^ (d * e) = 1 := by
    rw [pow_mul]
    have h : reduce f m (g ^ d) = reduce f m 1 := by rw [map_pow, map_one, hg]
    simpa only [one_pow] using local_pow_eq_of_reduce_eq h
  have hsD : s ^ d = 1 := by
    obtain ⟨j, hj⟩ := hN
    change (g ^ N) ^ d = 1
    rw [← pow_mul, hj, mul_right_comm e j d, mul_comm e d, pow_mul, hgD, one_pow]
  have hso := hd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hsD)
  let w := s ^ (d - 1) * g
  have hsinv : s * s ^ (d - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hd.pos, hsD]
  have hsw : s * w = g := by change s * (s ^ (d - 1) * g) = g; rw [← mul_assoc, hsinv, one_mul]
  have hw : reduce f m w = 1 := by
    change reduce f m (s ^ (d - 1) * g) = 1
    rw [map_mul, ← hr, ← map_mul, mul_comm, hsinv, map_one]
  have hv : reduce f m (w - 1) = 0 := by rw [map_sub, hw, map_one, sub_self]
  have hvnil : IsNilpotent (w - 1) := by
    have heq : reduce f m (w - 1) = reduce f m 0 := by simpa using hv
    exact ⟨e, by simpa [e, zero_pow (pow_ne_zero m (by decide : (2 : ℕ) ≠ 0))]
      using local_pow_eq_of_reduce_eq heq⟩
  refine ⟨s, ⟨IsUnit.of_mul_eq_one _ hsinv, hso, w - 1, hv, hvnil, ?_⟩, ?_⟩
  · rw [show 1 + (w - 1) = w by ring, hsw]
  · intro t ht
    have htr := reduce_eq_of_isSemisimplePart ht
    have htD : t ^ d = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [semisimple_order_eq_residue_order ht]
      exact orderOf_dvd_of_pow_eq_one hg
    exact eq_of_powers_eq_of_odd_order hd htD hsD (local_pow_eq_of_reduce_eq (htr.trans hr.symm))

private theorem semisimple_exists_unique {f G : P} (hmi : f.Monic) (hi : Irreducible f)
    (hG : ¬ f ∣ G) (m : ℕ) :
    ∃! s : Local f m, IsSemisimplePart (f := f) (m := m) (project (f ^ (2 ^ m)) G) s := by
  classical
  let : Fact (Irreducible f) := ⟨hi⟩
  let : CharP (K f) 2 := CharP.of_ringHom_of_ne_zero (kMap f) 2 (by decide)
  let : Module.Finite (ZMod 2) (K f) := hmi.finite_adjoinRoot
  let : Finite (K f) := Module.finite_of_finite (ZMod 2)
  let : Fintype (K f) := Fintype.ofFinite _
  let d := Fintype.card (K f) - 1
  have hd : Odd d := by
    have h := FiniteField.even_card_of_char_two (F := K f) (ringChar.eq (K f) 2)
    have hc : 0 < Fintype.card (K f) := Fintype.card_pos
    rw [Nat.odd_iff]
    dsimp [d]
    omega
  have hne : AdjoinRoot.mk f G ≠ 0 := mt AdjoinRoot.mk_eq_zero.mp hG
  apply semisimple_of_odd_residue_exponent hd
  change AdjoinRoot.mk f G ^ d = 1
  exact FiniteField.pow_card_sub_one_eq_one _ hne

private theorem trinomial_interface {q m a b c r : ℕ} {f : P}
    (hq : Odd q) (hm : f.Monic) (hi : Irreducible f) (hf : f ∣ cycle q)
    (hG : ¬ f ∣ trinomial a b c) (hr : FirstPositive f (trinomial a b c) r) :
    (∃! s : Local f m, IsSemisimplePart (f := f) (m := m)
      (project (f ^ (2 ^ m)) (trinomial a b c)) s) ∧
    ∀ (s : Local f m) (v : P),
      IsSemisimplePart (f := f) (m := m) (project (f ^ (2 ^ m)) (trinomial a b c)) s →
      project (f ^ (2 ^ m)) (trinomial a b c) = s * (1 + project (f ^ (2 ^ m)) v) →
      (∀ n : ℕ, n ≤ min r (2 ^ m) ↔ n ≤ 2 ^ m ∧ f ^ n ∣ v) ∧
      IsLeast {p : ℕ | (∃ k : ℕ, p = 2 ^ k) ∧ 2 ^ m ≤ r * p}
        (orderOf (1 + project (f ^ (2 ^ m)) v)) := by
  let : Fact (Irreducible f) := ⟨hi⟩
  have hsep := f_separable_of_odd_cycle hq hf
  refine ⟨semisimple_exists_unique hm hi hG m, ?_⟩
  intro s v hs hv
  exact ⟨truncated_valuation hsep hs hv hr, unipotent_order hsep hi hs hv hr⟩

end
noncomputable section

private def twoOddDegree (f : P) (s a b c : ℕ) : ℕ := by
  classical
  exact
    let A := min a b
    let D := max a b
    let d := 2 ^ (D - A).factorization 2
    let b₀ := 2 ^ c.factorization 2
    if zeta f ^ (D - A) ≠ 1 then s
    else if c = 0 then s * d
    else if d ≠ b₀ then s * min d b₀
    else if zeta f ^ A ≠ zeta f ^ c then s * d
    else s * (d + 1)

def preregisteredDegree (f : P) (a b c : ℕ) : ℕ :=
  let s := 2 ^ (a.gcd (b.gcd c)).factorization 2
  let A := a / s
  let B := b / s
  let C := c / s
  if Odd A ∧ Odd B ∧ Even C then twoOddDegree f s A B C
  else if Odd A ∧ Odd C ∧ Even B then twoOddDegree f s A C B
  else if Odd B ∧ Odd C ∧ Even A then twoOddDegree f s B C A
  else s

private def PiecewiseSupplier : Prop :=
  ∀ (q m a b c : ℕ) (f : P),
    Odd q → a < 2 ^ m * q → b < 2 ^ m * q → c < 2 ^ m * q →
    a ≠ b → a ≠ c → b ≠ c →
    f.Monic → Irreducible f → f ∣ cycle q → ¬ f ∣ trinomial a b c →
    FirstPositive f (trinomial a b c) (preregisteredDegree f a b c)

end



noncomputable section

private theorem dyadic_dvd (n : ℕ) : 2 ^ n.factorization 2 ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (Nat.prime_two.pow_dvd_iff_le_factorization hn).2 le_rfl

private theorem odd_div_dyadic {n : ℕ} (hn : n ≠ 0) :
    Odd (n / 2 ^ n.factorization 2) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h
  apply Nat.pow_succ_factorization_not_dvd hn Nat.prime_two
  have hmul := Nat.mul_div_cancel' (dyadic_dvd n)
  rw [pow_succ]
  calc
    2 ^ n.factorization 2 * 2 ∣ 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) :=
      Nat.mul_dvd_mul_left _ h
    _ = n := hmul

private theorem cast_odd_two {R : Type*} [Ring R] [CharP R 2] {n : ℕ} (h : Odd n) :
    (n : R) = 1 := by
  rw [CharP.cast_eq_mod R 2 n, Nat.odd_iff.mp h, Nat.cast_one]

private theorem cast_even_two {R : Type*} [Ring R] [CharP R 2] {n : ℕ} (h : Even n) :
    (n : R) = 0 :=
  (CharP.cast_eq_zero_iff R 2 n).2 (even_iff_two_dvd.1 h)

private theorem coeff_one_shifted_pow {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    ((X + C z) ^ n).coeff 1 = z ^ (n - 1) * (n : R) := by
  rw [coeff_X_add_C_pow, Nat.choose_one_right]

private theorem coeff_one_shifted_pow_mul {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    ((X + C z) ^ n).coeff 1 * z = z ^ n * (n : R) := by
  rw [coeff_one_shifted_pow, mul_right_comm]
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]

private theorem jet_monomial (f : P) (n : ℕ) :
    jet f (X ^ n) = (X + C (zeta f)) ^ n := by
  change taylor (zeta f) ((X ^ n : P).map (kMap f)) = _
  rw [Polynomial.map_pow, map_X, taylor_X_pow]

private theorem jetDifference_coeff_pos (f p : P) {i : ℕ} (hi : 0 < i) :
    (jetDifference f p).coeff i = (jet f p).coeff i := by
  simp [jetDifference, coeff_C, Nat.ne_of_gt hi]

private theorem firstPositive_of_factor {f : P} {p : P} {r : ℕ} {Q : (K f)[X]}
    (hr : 0 < r) (h : jetDifference f p = X ^ r * Q) (hQ : Q.coeff 0 ≠ 0) :
    FirstPositive f p r := by
  refine ⟨hr, ?_, ?_⟩
  · intro i hi hir
    rw [← jetDifference_coeff_pos f p hi, h, coeff_X_pow_mul', ite_eq_right hir.not_ge]
  · rw [← jetDifference_coeff_pos f p hr, h, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
    exact hQ

private theorem firstPositive_pow {f : P} [IsDomain (K f)] [CharP (K f) 2]
    {p : P} {r : ℕ} (h : FirstPositive f p r) (k : ℕ) :
    FirstPositive f (p ^ (2 ^ k)) (2 ^ k * r) := by
  obtain ⟨Q, hQ⟩ := (difference_pow_dvd_iff h r).2 le_rfl
  have hQ0 : Q.coeff 0 ≠ 0 := by
    have hc := congrArg (fun p : (K f)[X] => p.coeff r) hQ
    rw [jetDifference_coeff_pos f p h.1, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self] at hc
    exact hc ▸ h.2.2
  refine firstPositive_of_factor (Nat.mul_pos (Nat.two_pow_pos k) h.1) (Q := Q ^ (2 ^ k)) ?_ ?_
  · have hp : jetDifference f (p ^ (2 ^ k)) = (jetDifference f p) ^ (2 ^ k) := by
      simp only [jetDifference, map_pow, sub_pow_char_pow]
    rw [hp, hQ, mul_pow, ← pow_mul, Nat.mul_comm r]
  · rw [coeff_zero_eq_eval_zero, eval_pow]
    exact pow_ne_zero _ (by rwa [← coeff_zero_eq_eval_zero])

private theorem shifted_pow_dyadic_factor {R : Type*} [CommRing R] [CharP R 2] (z : R)
    {n : ℕ} (hn : n ≠ 0) :
    let r := 2 ^ n.factorization 2
    ∃ Q : R[X], (X + C z) ^ n - C (z ^ n) = X ^ r * Q ∧
      Q.coeff 0 * z ^ r = z ^ n ∧ (Even r → Q.coeff 1 = 0) := by
  dsimp only
  let r := 2 ^ n.factorization 2
  let u := n / r
  have hu : Odd u := odd_div_dyadic hn
  have hnur : u * r = n := by simpa only [u, r, Nat.mul_comm] using Nat.mul_div_cancel' (dyadic_dvd n)
  have hdiv : X ∣ (X + C z) ^ u - C (z ^ u) := by
    rw [← pow_one (X : R[X]), X_pow_dvd_iff]
    intro i hi
    have : i = 0 := by omega
    subst i
    simp [coeff_zero_eq_eval_zero]
  obtain ⟨V, hV⟩ := hdiv
  have hV0 : V.coeff 0 * z = z ^ u := by
    have hc := congrArg (fun p : R[X] => p.coeff 1) hV
    simp only [coeff_sub, coeff_C, one_ne_zero, ite_false, sub_zero,
      coeff_X_mul V 0, coeff_one_shifted_pow, cast_odd_two hu, mul_one] at hc
    rw [← hc, ← pow_succ, Nat.sub_add_cancel hu.pos]
  refine ⟨V ^ r, ?_, ?_, ?_⟩
  · change (X + C z) ^ n - C (z ^ n) = X ^ r * V ^ r
    rw [← hnur, pow_mul, pow_mul, map_pow, ← sub_pow_char_pow (p := 2) (n := n.factorization 2),
      hV, mul_pow]
  · change (V ^ r).coeff 0 * z ^ r = z ^ n
    rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, ← mul_pow, hV0, ← pow_mul, hnur]
  · intro hr
    have hd : derivative (V ^ r) = 0 := by
      rw [derivative_pow, cast_even_two hr, map_zero, zero_mul, zero_mul]
    have hc := congrArg (fun p : R[X] => p.coeff 0) hd
    simpa [coeff_derivative] using hc

end

noncomputable section

private theorem firstPositive_one_of_scaled_coeff {f : P} {p : P}
    (h : (jet f p).coeff 1 * zeta f ≠ 0) : FirstPositive f p 1 := by
  refine ⟨by decide, by omega, ?_⟩
  exact fun hz => h (by rw [hz, zero_mul])

private theorem jet_trinomial_shift (f : P) (a b c : ℕ) :
    jet f (trinomial a b c) =
      (X + C (zeta f)) ^ a + (X + C (zeta f)) ^ b + (X + C (zeta f)) ^ c := by
  simp only [trinomial, map_add, jet_monomial]

private theorem firstPositive_one_odd {f : P} [IsDomain (K f)] [CharP (K f) 2]
    {a b c : ℕ} (hz : zeta f ≠ 0) (ha : Odd a) (hb : Even b) (hc : Even c) :
    FirstPositive f (trinomial a b c) 1 := by
  apply firstPositive_one_of_scaled_coeff
  rw [jet_trinomial_shift]
  simp only [coeff_add, add_mul, coeff_one_shifted_pow_mul, cast_odd_two ha, cast_even_two hb,
    cast_even_two hc, mul_one, mul_zero, add_zero]
  exact pow_ne_zero _ hz

private theorem firstPositive_three_odd {f : P} [CharP (K f) 2] {a b c : ℕ}
    (ha : Odd a) (hb : Odd b) (hc : Odd c) (hG : ¬ f ∣ trinomial a b c) :
    FirstPositive f (trinomial a b c) 1 := by
  apply firstPositive_one_of_scaled_coeff
  have hval : AdjoinRoot.mk f (trinomial a b c) =
      zeta f ^ a + zeta f ^ b + zeta f ^ c := by
    simp only [trinomial, map_add, map_pow, AdjoinRoot.mk_X]
  rw [jet_trinomial_shift]
  simp only [coeff_add, add_mul, coeff_one_shifted_pow_mul, cast_odd_two ha, cast_odd_two hb,
    cast_odd_two hc, mul_one, ← hval]
  exact mt AdjoinRoot.mk_eq_zero.mp hG

private theorem firstPositive_two_odd_noncancel {f : P} [IsDomain (K f)] [CharP (K f) 2]
    {A D c : ℕ} (hz : zeta f ≠ 0) (hAD : A ≤ D) (hA : Odd A) (hD : Odd D)
    (hc : Even c) (hroot : zeta f ^ (D - A) ≠ 1) :
    FirstPositive f (trinomial A D c) 1 := by
  apply firstPositive_one_of_scaled_coeff
  rw [jet_trinomial_shift]
  simp only [coeff_add, add_mul, coeff_one_shifted_pow_mul, cast_odd_two hA, cast_odd_two hD,
    cast_even_two hc, mul_one, mul_zero, add_zero]
  have hsum : 1 + zeta f ^ (D - A) ≠ 0 := by
    intro hs
    apply hroot
    have ht := congrArg (fun v => v + (1 : K f)) hs
    rwa [add_right_comm, CharTwo.add_self_eq_zero, zero_add, zero_add] at ht
  have hpow : zeta f ^ D = zeta f ^ A * zeta f ^ (D - A) := by
    rw [← pow_add, Nat.add_sub_of_le hAD]
  rw [hpow]
  simpa only [mul_add, mul_one] using mul_ne_zero (pow_ne_zero A hz) hsum

private theorem two_odd_pair_factor {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]
    {z : R} (hz : z ≠ 0) {A D : ℕ} (hAD : A < D) (hA : Odd A) (hD : Odd D)
    (hroot : z ^ (D - A) = 1) :
    let d := 2 ^ (D - A).factorization 2
    ∃ U : R[X], (X + C z) ^ A + (X + C z) ^ D = X ^ d * U ∧
      U.coeff 0 * z ^ d = z ^ A ∧ U.coeff 1 ≠ 0 := by
  dsimp only
  let d := 2 ^ (D - A).factorization 2
  let H : R[X] := X + C z
  have hd : Even d := by
    apply even_iff_two_dvd.mpr
    have hΔ : 2 ∣ D - A := by
      rw [← even_iff_two_dvd]
      have hA' := Nat.odd_iff.mp hA
      have hD' := Nat.odd_iff.mp hD
      rw [Nat.even_iff]
      omega
    have hk := Nat.prime_two.factorization_pos_of_dvd (Nat.sub_ne_zero_of_lt hAD) hΔ
    exact dvd_pow_self 2 hk.ne'
  obtain ⟨Q, hQ, hQ0, hQ1⟩ := shifted_pow_dyadic_factor z (Nat.sub_ne_zero_of_lt hAD)
  change H ^ (D - A) - C (z ^ (D - A)) = X ^ d * Q at hQ
  refine ⟨H ^ A * Q, ?_, ?_, ?_⟩
  · change H ^ A + H ^ D = X ^ d * (H ^ A * Q)
    have hpow : H ^ D = H ^ A * H ^ (D - A) := by
      rw [← pow_add, Nat.add_sub_of_le hAD.le]
    calc
      H ^ A + H ^ D = H ^ A * (1 + H ^ (D - A)) := by rw [hpow, mul_add, mul_one]
      _ = X ^ d * (H ^ A * Q) := by
        rw [mul_left_comm, ← hQ, hroot, C_1]
        have htwo : (1 : R[X]) + 1 = 0 := CharTwo.add_self_eq_zero 1
        congr 1
        linear_combination htwo
  · change (H ^ A * Q).coeff 0 * z ^ d = z ^ A
    have hH0 : (H ^ A).coeff 0 = z ^ A := by simp [H, coeff_zero_eq_eval_zero]
    rw [mul_coeff_zero, hH0, mul_assoc, hQ0, hroot, mul_one]
  · rw [mul_coeff_one, hQ1 hd, mul_zero, zero_add, coeff_one_shifted_pow, cast_odd_two hA,
      mul_one]
    exact mul_ne_zero (pow_ne_zero _ hz) (fun h => by rw [h, zero_mul, hroot] at hQ0; exact zero_ne_one hQ0)

end

noncomputable section

private theorem jetDifference_trinomial_two_odd {f : P} [CharP (K f) 2]
    {A D c : ℕ} (hAD : A ≤ D) (hroot : zeta f ^ (D - A) = 1) :
    jetDifference f (trinomial A D c) =
      ((X + C (zeta f)) ^ A + (X + C (zeta f)) ^ D) +
      ((X + C (zeta f)) ^ c - C (zeta f ^ c)) := by
  have hpow : zeta f ^ D = zeta f ^ A := by
    nth_rw 1 [← Nat.add_sub_of_le hAD]
    rw [pow_add, hroot, mul_one]
  have hval : AdjoinRoot.mk f (trinomial A D c) = zeta f ^ c := by
    simp only [trinomial, map_add, map_pow, AdjoinRoot.mk_X, hpow, CharTwo.add_self_eq_zero, zero_add]
  rw [jetDifference, jet_trinomial_shift, hval, add_sub_assoc]

private theorem firstPositive_of_two_factors {f : P} {p : P} {d b₀ : ℕ} {U V : (K f)[X]}
    (hd : 0 < d) (hb₀ : 0 < b₀) (h : jetDifference f p = X ^ d * U + X ^ b₀ * V)
    (hU0 : U.coeff 0 ≠ 0) (hV0 : V.coeff 0 ≠ 0) (hne : d ≠ b₀) :
    FirstPositive f p (min d b₀) := by
  refine ⟨lt_min hd hb₀, ?_, ?_⟩
  · intro i hi hmin
    rw [lt_min_iff] at hmin
    rw [← jetDifference_coeff_pos f p hi, h, coeff_add, coeff_X_pow_mul', coeff_X_pow_mul',
      ite_eq_right hmin.1.not_ge, ite_eq_right hmin.2.not_ge, add_zero]
  · rw [← jetDifference_coeff_pos f p (lt_min hd hb₀), h, coeff_add]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rwa [min_eq_left hlt.le, coeff_X_pow_mul', coeff_X_pow_mul', ite_eq_left le_rfl,
        Nat.sub_self, ite_eq_right hlt.not_ge, add_zero]
    · rwa [min_eq_right hgt.le, coeff_X_pow_mul', coeff_X_pow_mul', ite_eq_right hgt.not_ge,
        ite_eq_left le_rfl, Nat.sub_self, zero_add]

private theorem firstPositive_of_factor_cancel {f : P} {p : P} {d : ℕ} {W : (K f)[X]}
    (h : jetDifference f p = X ^ d * W) (hW0 : W.coeff 0 = 0)
    (hW1 : W.coeff 1 ≠ 0) : FirstPositive f p (d + 1) := by
  have hd' : 0 < d + 1 := Nat.succ_pos d
  refine ⟨hd', ?_, ?_⟩
  · intro i hi hir
    rw [← jetDifference_coeff_pos f p hi, h, coeff_X_pow_mul']
    by_cases hid : i < d
    · rw [ite_eq_right hid.not_ge]
    · have : i = d := by omega
      rwa [this, ite_eq_left le_rfl, Nat.sub_self]
  · rw [← jetDifference_coeff_pos f p hd', h, Nat.add_comm d 1, coeff_X_pow_mul]
    exact hW1

private theorem firstPositive_two_odd_sorted {f : P} [IsDomain (K f)] [CharP (K f) 2]
    {A D c : ℕ} (hz : zeta f ≠ 0) (hAD : A < D) (hA : Odd A) (hD : Odd D) (hc : Even c) :
    FirstPositive f (trinomial A D c) (twoOddDegree f 1 A D c) := by
  classical
  let d := 2 ^ (D - A).factorization 2
  let b₀ := 2 ^ c.factorization 2
  have hd : 0 < d := Nat.two_pow_pos _
  have hb₀ : 0 < b₀ := Nat.two_pow_pos _
  by_cases hroot : zeta f ^ (D - A) = 1
  · obtain ⟨U, hU, hU0, hU1⟩ := two_odd_pair_factor hz hAD hA hD hroot
    have hU0' : U.coeff 0 ≠ 0 := fun h => by
      rw [h, zero_mul] at hU0
      exact (pow_ne_zero _ hz) hU0.symm
    have hdiff := jetDifference_trinomial_two_odd (c := c) hAD.le hroot
    rw [hU] at hdiff
    by_cases hc0 : c = 0
    · rw [hc0, pow_zero, pow_zero, C_1, sub_self, add_zero] at hdiff
      simpa [twoOddDegree, min_eq_left hAD.le, max_eq_right hAD.le, hroot, hc0, d] using
        firstPositive_of_factor hd hdiff hU0'
    · obtain ⟨V, hV, hV0, hV1⟩ := shifted_pow_dyadic_factor (zeta f) hc0
      rw [hV] at hdiff
      have hV0' : V.coeff 0 ≠ 0 := fun h => by
        rw [h, zero_mul] at hV0
        exact (pow_ne_zero _ hz) hV0.symm
      by_cases hdb : d = b₀
      · change U.coeff 0 * zeta f ^ d = zeta f ^ A at hU0
        change V.coeff 0 * zeta f ^ b₀ = zeta f ^ c at hV0
        change _ = X ^ d * U + X ^ b₀ * V at hdiff
        rw [← hdb, ← mul_add] at hdiff
        have hW0 : (U + V).coeff 0 * zeta f ^ d = zeta f ^ A + zeta f ^ c := by
          rw [coeff_add, add_mul, hU0, hdb, hV0]
        by_cases hval : zeta f ^ A = zeta f ^ c
        · have hW0' : (U + V).coeff 0 = 0 := by
            rw [hval, CharTwo.add_self_eq_zero] at hW0
            exact (mul_eq_zero.mp hW0).resolve_right (pow_ne_zero _ hz)
          have hbEven : Even b₀ := by
            have hk := Nat.prime_two.factorization_pos_of_dvd hc0 (even_iff_two_dvd.1 hc)
            exact even_iff_two_dvd.2 (dvd_pow_self 2 hk.ne')
          have hW1 : (U + V).coeff 1 ≠ 0 := by rw [coeff_add, hV1 hbEven, add_zero]; exact hU1
          simpa [twoOddDegree, min_eq_left hAD.le, max_eq_right hAD.le, hroot, hc0, d, b₀,
            hdb, hval] using firstPositive_of_factor_cancel hdiff hW0' hW1
        · have hW0' : (U + V).coeff 0 ≠ 0 := by
            intro hW
            rw [hW, zero_mul] at hW0
            apply hval
            have h := congrArg (fun v => v + zeta f ^ c) hW0
            simpa only [add_assoc, CharTwo.add_self_eq_zero, zero_add, add_zero] using h.symm
          simpa [twoOddDegree, min_eq_left hAD.le, max_eq_right hAD.le, hroot, hc0, d, b₀,
            hdb, hval] using firstPositive_of_factor hd hdiff hW0'
      · simpa [twoOddDegree, min_eq_left hAD.le, max_eq_right hAD.le, hroot, hc0, d, b₀,
          hdb] using firstPositive_of_two_factors hd hb₀ hdiff hU0' hV0' hdb
  · simpa [twoOddDegree, min_eq_left hAD.le, max_eq_right hAD.le, hroot] using
      firstPositive_two_odd_noncancel hz hAD.le hA hD hc hroot

end

noncomputable section

private theorem firstPositive_two_odd {f : P} [IsDomain (K f)] [CharP (K f) 2]
    {a b c : ℕ} (hz : zeta f ≠ 0) (hab : a ≠ b) (ha : Odd a) (hb : Odd b) (hc : Even c) :
    FirstPositive f (trinomial a b c) (twoOddDegree f 1 a b c) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact firstPositive_two_odd_sorted hz h ha hb hc
  · simpa only [trinomial, add_comm (X ^ b : P) (X ^ a), twoOddDegree,
      min_comm b a, max_comm b a] using firstPositive_two_odd_sorted hz h hb ha hc

private theorem twoOddDegree_mul (f : P) (s a b c : ℕ) :
    twoOddDegree f s a b c = s * twoOddDegree f 1 a b c := by
  unfold twoOddDegree
  split_ifs <;> simp

/-- After removing the common dyadic factor, at least one exponent is odd. -/
private theorem normalized_exponents {a b c : ℕ} (hab : a ≠ b) :
    let g := a.gcd (b.gcd c)
    let s := 2 ^ g.factorization 2
    s ∣ a ∧ s ∣ b ∧ s ∣ c ∧ (Odd (a / s) ∨ Odd (b / s) ∨ Odd (c / s)) := by
  dsimp only
  let g := a.gcd (b.gcd c)
  let s := 2 ^ g.factorization 2
  have hs : s ∣ g := dyadic_dvd g
  have ha : s ∣ a := hs.trans (Nat.gcd_dvd_left a _)
  have hb : s ∣ b := (hs.trans (Nat.gcd_dvd_right a _)).trans (Nat.gcd_dvd_left b c)
  have hc : s ∣ c := (hs.trans (Nat.gcd_dvd_right a _)).trans (Nat.gcd_dvd_right b c)
  refine ⟨ha, hb, hc, ?_⟩
  by_contra! h
  have hg : g ≠ 0 := by
    intro hg
    obtain ⟨ha0, hbc⟩ := Nat.gcd_eq_zero_iff.mp hg
    exact hab (ha0.trans (Nat.gcd_eq_zero_iff.mp hbc).1.symm)
  apply Nat.pow_succ_factorization_not_dvd hg Nat.prime_two
  rw [pow_succ]
  have hd {n : ℕ} (hsn : s ∣ n) (hn : ¬ Odd (n / s)) : s * 2 ∣ n := by
    calc
      s * 2 ∣ s * (n / s) :=
        Nat.mul_dvd_mul_left _ (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hn))
      _ = n := Nat.mul_div_cancel' hsn
  exact Nat.dvd_gcd (hd ha h.1) (Nat.dvd_gcd (hd hb h.2.1) (hd hc h.2.2))

private theorem firstPositive_scaled_trinomial {f : P} [IsDomain (K f)] [CharP (K f) 2]
    (hz : zeta f ≠ 0) {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hG : ¬ f ∣ trinomial a b c) :
    FirstPositive f (trinomial a b c) (preregisteredDegree f a b c) := by
  let k := (a.gcd (b.gcd c)).factorization 2
  let s := 2 ^ k
  let A := a / s
  let B := b / s
  let C₀ := c / s
  obtain ⟨hsa, hsb, hsc, hodd⟩ := normalized_exponents (c := c) hab
  change s ∣ a at hsa
  change s ∣ b at hsb
  change s ∣ c at hsc
  change Odd A ∨ Odd B ∨ Odd C₀ at hodd
  have hA : s * A = a := Nat.mul_div_cancel' hsa
  have hB : s * B = b := Nat.mul_div_cancel' hsb
  have hC : s * C₀ = c := Nat.mul_div_cancel' hsc
  have hAB : A ≠ B := fun h => hab (by rw [← hA, ← hB, h])
  have hAC : A ≠ C₀ := fun h => hac (by rw [← hA, ← hC, h])
  have hBC : B ≠ C₀ := fun h => hbc (by rw [← hB, ← hC, h])
  have hpow : trinomial A B C₀ ^ s = trinomial a b c := by
    change (X ^ A + X ^ B + X ^ C₀ : P) ^ (2 ^ k) = X ^ a + X ^ b + X ^ c
    simp only [add_pow_char_pow (p := 2), ← pow_mul]
    rw [mul_comm A, mul_comm B, mul_comm C₀, hA, hB, hC]
  have hG₀ : ¬ f ∣ trinomial A B C₀ := by
    intro h
    apply hG
    rw [← hpow]
    exact h.trans (dvd_pow_self _ (Nat.two_pow_pos k).ne')
  change FirstPositive f (trinomial a b c)
    (if Odd A ∧ Odd B ∧ Even C₀ then twoOddDegree f s A B C₀
     else if Odd A ∧ Odd C₀ ∧ Even B then twoOddDegree f s A C₀ B
     else if Odd B ∧ Odd C₀ ∧ Even A then twoOddDegree f s B C₀ A
     else s)
  rw [← hpow]
  by_cases ha : Odd A <;> by_cases hb : Odd B <;> by_cases hc : Odd C₀
  · simpa only [ha, hb, hc, ← Nat.not_odd_iff_even, not_true_eq_false, and_false,
      and_true, ite_false, mul_one] using
      firstPositive_pow (firstPositive_three_odd ha hb hc hG₀) k
  · have hc' := Nat.not_odd_iff_even.mp hc
    simpa [ha, hb, hc', twoOddDegree_mul f s A B C₀, s] using
      firstPositive_pow (firstPositive_two_odd hz hAB ha hb hc') k
  · have hb' := Nat.not_odd_iff_even.mp hb
    simpa [ha, hb, hc, hb', twoOddDegree_mul f s A C₀ B, s, trinomial, add_assoc,
      add_comm, add_left_comm] using
      firstPositive_pow (firstPositive_two_odd hz hAC ha hc hb') k
  · have hb' := Nat.not_odd_iff_even.mp hb
    have hc' := Nat.not_odd_iff_even.mp hc
    simpa [ha, hb, hc, s] using firstPositive_pow (firstPositive_one_odd hz ha hb' hc') k
  · have ha' := Nat.not_odd_iff_even.mp ha
    simpa [ha, hb, hc, ha', twoOddDegree_mul f s B C₀ A, s, trinomial, add_assoc,
      add_comm, add_left_comm] using
      firstPositive_pow (firstPositive_two_odd hz hBC hb hc ha') k
  · have ha' := Nat.not_odd_iff_even.mp ha
    have hc' := Nat.not_odd_iff_even.mp hc
    simpa [ha, hb, hc, s, trinomial, add_assoc, add_comm, add_left_comm] using
      firstPositive_pow (firstPositive_one_odd hz hb ha' hc') k
  · have ha' := Nat.not_odd_iff_even.mp ha
    have hb' := Nat.not_odd_iff_even.mp hb
    simpa [ha, hb, hc, s, trinomial, add_assoc, add_comm, add_left_comm] using
      firstPositive_pow (firstPositive_one_odd hz hc ha' hb') k
  · exact (hodd.elim ha fun h => h.elim hb hc).elim

/-- The preregistered degree supplies the first positive Taylor coefficient for every eligible factor. -/
private theorem piecewiseSupplier : PiecewiseSupplier := by
  intro q _ a b c f hq _ _ _ hab hac hbc _ hi hf hG
  let : Fact (Irreducible f) := ⟨hi⟩
  let : CharP (K f) 2 := CharP.of_ringHom_of_ne_zero (kMap f) 2 (by decide)
  have hroot : zeta f ^ q = 1 := project_X_pow hf
  have hz : zeta f ≠ 0 := by
    intro hz
    rw [hz, zero_pow hq.pos.ne'] at hroot
    exact zero_ne_one hroot
  exact firstPositive_scaled_trinomial hz hab hac hbc hG

end

/-- The complete three-distinct-offset cyclic local decomposition. -/
theorem piecewise_trinomial_interface
    {q m a b c : ℕ} {f : P}
    (hq : Odd q)
    (ha : a < 2 ^ m * q) (hb : b < 2 ^ m * q) (hc : c < 2 ^ m * q)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hm : f.Monic) (hi : Irreducible f) (hf : f ∣ cycle q)
    (hG : ¬ f ∣ trinomial a b c) :
    (∃! s : Local f m, IsSemisimplePart (f := f) (m := m)
      (project (f ^ (2 ^ m)) (trinomial a b c)) s) ∧
    ∀ (s : Local f m) (v : P),
      IsSemisimplePart (f := f) (m := m)
        (project (f ^ (2 ^ m)) (trinomial a b c)) s →
      project (f ^ (2 ^ m)) (trinomial a b c) =
        s * (1 + project (f ^ (2 ^ m)) v) →
      (∀ n : ℕ, n ≤ min (preregisteredDegree f a b c) (2 ^ m) ↔
        n ≤ 2 ^ m ∧ f ^ n ∣ v) ∧
      IsLeast
        {p : ℕ | (∃ k : ℕ, p = 2 ^ k) ∧
          2 ^ m ≤ preregisteredDegree f a b c * p}
        (orderOf (1 + project (f ^ (2 ^ m)) v)) := by
  have hr := piecewiseSupplier q m a b c f hq ha hb hc hab hac hbc hm hi hf hG
  exact trinomial_interface hq hm hi hf hG hr

end D5.S3.StatisticalMechanics.CellularAutomata.BojicThreeTerm
