/- GID: D5/S3/FiniteGroups/BajnokBeattyAllRegimes
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyAllRegimes
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal four-clause signed-radius classification for ZMod 2 times ZMod (2k). -/

/- Source: Bajnok--Beatty, arXiv:2406.04045v1, Section 4,
Conjecture 4.1 and Theorems 4.2--4.4. The order bound and low positive
regimes are literature-attested and carry no novelty claim.
Admission basis: open-problem-resolution; preregistration #25489.
The single public endpoint is the full original iff for every positive k,s.
All intermediate helpers are private and consumed by that endpoint.
Proof shape: content, through exact rectangle representatives and explicit
integer-cylinder covers; the top strip consumes the existing necessity
and sufficiency constructions. No new determinant result is claimed.
Direct frozen project dependencies: BajnokBeattyCayleyNecessity.top_strip_necessity
and BajnokBeattyCayleySufficiency.result.
-/

import D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
import D5.S3.FiniteGroups.BajnokBeattyCayleySufficiency
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! The original four-regime classification, using arbitrary-pair necessity
and the uniform sufficient construction in the top strip. -/

namespace D5.S3.FiniteGroups.BajnokBeattyAllRegimes

open NearSquareLatticeRigidity BajnokBeattyCayleyNecessity

set_option autoImplicit false
set_option relaxedAutoImplicit false

private def PairCovers (k s : ℕ) : Prop :=
  ∃ a b : Target k, a ≠ b ∧ ∀ g, ∃ x y : ℤ,
    g = x • a + y • b ∧ |x| + |y| ≤ (s : ℤ)

/- Actual finite quotient count. There is no assumed finite-index/counting
hypothesis: Fin n × Fin n explicitly surjects onto the additive quotient.
Nat.card_le_card_of_surjective requires only that the SOURCE is finite. -/
private theorem rectangle_index_le (L : Submodule ℤ Plane) (n : ℕ)
    (hc : RectangleCovers L (n : ℤ) (n : ℤ)) :
    L.toAddSubgroup.index ≤ n * n := by
  classical
  let π : Fin n × Fin n → Plane ⧸ L.toAddSubgroup :=
    fun p => QuotientAddGroup.mk' L.toAddSubgroup ![(p.1.val : ℤ), (p.2.val : ℤ)]
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L.toAddSubgroup q
    obtain ⟨x, y, hx0, hxn, hy0, hyn, hL⟩ := hc z
    have hx : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    have hy : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
    refine ⟨(⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩), ?_⟩
    change (QuotientAddGroup.mk' L.toAddSubgroup) ![(x.toNat : ℤ), (y.toNat : ℤ)] =
      (QuotientAddGroup.mk' L.toAddSubgroup) z
    rw [hx, hy]
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hL).symm
  change Nat.card (Plane ⧸ L.toAddSubgroup) ≤ n * n
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_surjective π hπ

/- Complement to the existing even-radius oddLattice_cover. At radius 2t+1
use the even coefficient-sum torsor, which becomes [-t,t]^2. -/
private theorem even_torsor_cover {k : ℕ} (f : Plane →+ Target k) {t : ℤ}
    (hcover : LeeCovers f (2*t+1)) :
    RectangleCovers (oddLattice f) (2*t+1) (2*t+1) := by
  have hf : Function.Surjective f := fun g => by
    obtain ⟨w, _, hw⟩ := hcover g
    exact ⟨w, hw⟩
  intro z
  let v : Plane := sumDiff (z - ![t, t])
  obtain ⟨w, hw, hfw⟩ := hcover (f v)
  have hker : f (w-v) = 0 := by rw [map_sub, hfw, sub_self]
  obtain ⟨h0, h1⟩ := kernel_even f hf hker
  change 2 ∣ w 0 - (z 0 - t + (z 1 - t)) at h0
  change 2 ∣ w 1 - (z 0 - t - (z 1 - t)) at h1
  let x := (w 0 + w 1) / 2
  let y := (w 0 - w 1) / 2
  have hs : w 0 + w 1 = 2*x := by dsimp [x]; omega
  have hd : w 0 - w 1 = 2*y := by dsimp [y]; omega
  have hw0 := le_abs_self (w 0)
  have hw1 := le_abs_self (w 1)
  have hw0' := neg_abs_le (w 0)
  have hw1' := neg_abs_le (w 1)
  have hx : -t ≤ x ∧ x ≤ t := by constructor <;> omega
  have hy : -t ≤ y ∧ y ≤ t := by constructor <;> omega
  refine ⟨x+t, y+t, by omega, by omega, by omega, by omega, ?_⟩
  change f (sumDiff (z - ![x+t, y+t])) = 0
  have he : sumDiff (z - ![x+t, y+t]) = v-w := by
    ext i
    fin_cases i
    · change z 0 - (x+t) + (z 1 - (y+t)) =
        (z 0 - t + (z 1 - t)) - w 0
      omega
    · change z 0 - (x+t) - (z 1 - (y+t)) =
        (z 0 - t - (z 1 - t)) - w 1
      omega
  rw [he, map_sub, hfw, sub_self]

private theorem hom_order_le {k s : ℕ} (hk : 0 < k)
    (f : Plane →+ Target k) (hc : LeeCovers f (s : ℤ)) : 2*k ≤ s^2 := by
  have hf : Function.Surjective f := fun g => by
    obtain ⟨z, _, hz⟩ := hc g
    exact ⟨z, hz⟩
  have hrect : RectangleCovers (oddLattice f) (s : ℤ) (s : ℤ) := by
    rcases Nat.even_or_odd s with he | ho
    · obtain ⟨t, ht⟩ := he
      have hs : (s : ℤ) = 2*(t : ℤ) := by exact_mod_cast (show s = 2*t by omega)
      have hc' : LeeCovers f (2*(t : ℤ)) := by simpa only [hs] using hc
      simpa only [hs] using oddLattice_cover f hc'
    · obtain ⟨t, ht⟩ := ho
      have hs : (s : ℤ) = 2*(t : ℤ)+1 := by
        exact_mod_cast (show s = 2*t+1 by omega)
      have hc' : LeeCovers f (2*(t : ℤ)+1) := by simpa only [hs] using hc
      simpa only [hs] using even_torsor_cover f hc'
  have hi := rectangle_index_le (oddLattice f) s hrect
  rw [oddLattice_index hk f hf] at hi
  simpa only [pow_two] using hi

private theorem pair_order_le {k s : ℕ} (hk : 0 < k)
    (hc : PairCovers k s) : 2*k ≤ s^2 := by
  obtain ⟨a, b, _, hc⟩ := hc
  let f : Plane →+ Target k := {
    toFun := fun z => z 0 • a + z 1 • b
    map_zero' := by simp
    map_add' := by intro z w; simp only [Pi.add_apply, add_zsmul]; abel }
  apply hom_order_le hk f
  intro g
  obtain ⟨x, y, he, hxy⟩ := hc g
  exact ⟨![x, y], hxy, he.symm⟩

private theorem lee_of_sum_diff (x y R : ℤ)
    (hs : -R ≤ x+y ∧ x+y ≤ R) (hd : -R ≤ x-y ∧ x-y ≤ R) :
    |x|+|y| ≤ R := by
  rcases le_total 0 x with hx | hx <;>
    rcases le_total 0 y with hy | hy <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hx, hy] <;> omega

/- Known odd positive regime (primary Theorem 4.3), proved constructively.
This includes t=0 as an integer-cylinder lemma; no positive finite k can
satisfy k ≤ 0, so no exceptional k=0 target is silently admitted. -/
private theorem odd_integer_cover (t : ℤ) (ht : 0 ≤ t)
    (ε : ZMod 2) (z : ℤ) (hz : |z| ≤ 2*t*(t+1)) :
    ∃ x y : ℤ, ((x+y : ℤ) : ZMod 2) = ε ∧
      t*x+(t+1)*y = z ∧ |x|+|y| ≤ 2*t+1 := by
  have hzlo := (abs_le.mp hz).1
  have hzhi := (abs_le.mp hz).2
  have hS : 0 < 2*t+1 := by omega
  rcases (show ε = 0 ∨ ε = 1 by fin_cases ε <;> first | exact Or.inl rfl | exact Or.inr rfl) with rfl | rfl
  · let q := (z+t)/(2*t+1)
    let w := (z+t)%(2*t+1)-t
    have hr0 := Int.emod_nonneg (z+t) (ne_of_gt hS)
    have hr1 := Int.emod_lt_of_pos (z+t) hS
    have hdiv := Int.emod_add_mul_ediv (z+t) (2*t+1)
    have hqw : z+t = (2*t+1)*q+(w+t) := by
      dsimp [q, w]
      nlinarith [hdiv]
    have hw : -t ≤ w ∧ w ≤ t := by dsimp [w]; omega
    have hq : -t ≤ q ∧ q ≤ t := by
      constructor
      · by_contra h
        have hmul := mul_le_mul_of_nonneg_left (show q ≤ -t-1 by omega) hS.le
        nlinarith [hqw, hw.2]
      · by_contra h
        have hmul := mul_le_mul_of_nonneg_left (show t+1 ≤ q by omega) hS.le
        nlinarith [hqw, hw.1]
    refine ⟨q-w, q+w, ?_, ?_, ?_⟩
    · rw [show q-w+(q+w) = 2*q by ring]
      exact ZMod.intCast_eq_zero_iff_even.mpr ⟨q, by ring⟩
    · nlinarith [hqw]
    · have hh := lee_of_sum_diff (q-w) (q+w) (2*t)
          (by constructor <;> linarith [hq.1, hq.2])
          (by constructor <;> linarith [hw.1, hw.2])
      omega
  · let q := z/(2*t+1)
    let r := z%(2*t+1)
    have hr0 : 0 ≤ r := Int.emod_nonneg z (ne_of_gt hS)
    have hr1 : r < 2*t+1 := Int.emod_lt_of_pos z hS
    have hdiv : z = (2*t+1)*q+r := by
      dsimp [q, r]
      nlinarith [Int.emod_add_mul_ediv z (2*t+1)]
    have hq : -t-1 ≤ q ∧ q ≤ t := by
      constructor
      · by_contra h
        have hmul := mul_le_mul_of_nonneg_left (show q ≤ -t-2 by omega) hS.le
        nlinarith
      · by_contra h
        have hmul := mul_le_mul_of_nonneg_left (show t+1 ≤ q by omega) hS.le
        nlinarith
    refine ⟨q+1-r+t, q+r-t, ?_, ?_, ?_⟩
    · rw [show q+1-r+t+(q+r-t) = 2*q+1 by ring]
      exact ZMod.intCast_eq_one_iff_odd.mpr ⟨q, by ring⟩
    · nlinarith [hdiv]
    · apply lee_of_sum_diff
      · constructor <;> linarith [hq.1, hq.2]
      · constructor <;> linarith

/- Known even-low regime (primary Theorem 4.4). The three CLOSED INTEGER
bands are adjacent when t ≤ 2B+1, including t=1, B=0. -/
private theorem even_integer_cover (t : ℤ) (ht : 1 ≤ t)
    (ε : ZMod 2) (z : ℤ) (hz : |z| ≤ 2*t^2-t) :
    ∃ x y : ℤ, ((x+y : ℤ) : ZMod 2) = ε ∧
      (t-1)*x+t*y = z ∧ |x|+|y| ≤ 2*t := by
  let B := 2*t*(t-1)
  have hB : 0 ≤ B := by dsimp [B]; exact mul_nonneg (by omega) (by omega)
  have hadj : t ≤ 2*B+1 := by
    have hh := mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ 4*t-1 by omega)
    dsimp [B]
    nlinarith
  have hbase : ∀ (η : ZMod 2) (w : ℤ), |w| ≤ B →
      ∃ x y : ℤ, ((x+y : ℤ) : ZMod 2) = η ∧
        (t-1)*x+t*y = w ∧ |x|+|y| ≤ 2*t-1 := by
    intro η w hw
    have hw' : |w| ≤ 2*(t-1)*((t-1)+1) := by dsimp [B] at hw; nlinarith [hw]
    obtain ⟨x, y, he, hz', hb⟩ := odd_integer_cover (t-1) (by omega) η w hw'
    exact ⟨x, y, he, by simpa only [sub_add_cancel] using hz', by omega⟩
  have hband : ∃ c : ℤ, (c = -1 ∨ c = 0 ∨ c = 1) ∧ |z-c*t| ≤ B := by
    have hzlo := (abs_le.mp hz).1
    have hzhi := (abs_le.mp hz).2
    by_cases hp : B < z
    · have hp' : B+1 ≤ z := by omega
      refine ⟨1, Or.inr (Or.inr rfl), abs_le.mpr ⟨?_, ?_⟩⟩ <;>
        dsimp [B] at * <;> nlinarith
    · by_cases hn : z < -B
      · have hn' : z ≤ -B-1 := by omega
        refine ⟨-1, Or.inl rfl, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
          dsimp [B] at * <;> nlinarith
      · exact ⟨0, Or.inr (Or.inl rfl), by simpa using (abs_le.mpr (by omega) : |z| ≤ B)⟩
  obtain ⟨c, hc, hzc⟩ := hband
  obtain ⟨x, y, he, hxy, hnorm⟩ := hbase (ε-(c : ZMod 2)) (z-c*t) hzc
  have hcabs : |c| ≤ 1 := by rcases hc with rfl | rfl | rfl <;> norm_num
  refine ⟨x, y+c, ?_, ?_, ?_⟩
  · calc
      (((x+(y+c) : ℤ)) : ZMod 2) = ((x+y : ℤ) : ZMod 2)+(c : ZMod 2) := by push_cast; ring
      _ = ε := by rw [he]; abel
  · nlinarith [hxy]
  · have hh := abs_add_le y c
    omega

/- Balanced lifts are REUSED from pinned Mathlib, not assumed or re-proved. -/
private theorem finite_cover (k : ℕ) (hk : 0 < k) (u v B R : ℤ)
    (hB : (k : ℤ) ≤ B)
    (hc : ∀ (ε : ZMod 2) (z : ℤ), |z| ≤ B → ∃ x y : ℤ,
      ((x+y : ℤ) : ZMod 2) = ε ∧ u*x+v*y = z ∧ |x|+|y| ≤ R) :
    ∀ g : Target k, ∃ x y : ℤ,
      g = x • (1, (u : ZMod (2*k))) + y • (1, (v : ZMod (2*k))) ∧
      |x|+|y| ≤ R := by
  letI : NeZero (2*k) := ⟨by omega⟩
  intro g
  let z := g.2.valMinAbs
  have hbal := g.2.valMinAbs_mem_Ioc
  have hz : |z| ≤ (k : ℤ) := by
    apply abs_le.mpr
    dsimp [z]
    constructor <;> push_cast at hbal <;> linarith [hbal.1, hbal.2]
  obtain ⟨x, y, hε, hxy, hnorm⟩ := hc g.1 z (hz.trans hB)
  refine ⟨x, y, ?_, hnorm⟩
  apply Prod.ext
  · change g.1 = x • (1 : ZMod 2)+y • (1 : ZMod 2)
    simpa only [zsmul_eq_mul, mul_one, Int.cast_add] using hε.symm
  · change g.2 = x • (u : ZMod (2*k))+y • (v : ZMod (2*k))
    rw [zsmul_eq_mul, zsmul_eq_mul]
    calc
      g.2 = (z : ZMod (2*k)) := g.2.coe_valMinAbs.symm
      _ = (u : ZMod (2*k))*(x : ZMod (2*k))+
          (v : ZMod (2*k))*(y : ZMod (2*k)) := by
        rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, hxy]
      _ = _ := by ring

private theorem consecutive_distinct (k : ℕ) (hk : 0 < k) (t : ℤ) :
    ((1 : ZMod 2), (t : ZMod (2*k))) ≠
      ((1 : ZMod 2), ((t+1 : ℤ) : ZMod (2*k))) := by
  intro h
  have hh : ((t+1 : ℤ) : ZMod (2*k)) = (t : ZMod (2*k)) :=
    (congrArg Prod.snd h).symm
  have hone : ((1 : ℤ) : ZMod (2*k)) = 0 := by
    have hh' := sub_eq_zero.mpr hh
    simpa only [← Int.cast_sub, show (t+1 : ℤ)-t=1 by ring] using hh'
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd 1 (2*k)).mp hone
  have hle : ((2*k : ℕ) : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hd
  omega

private theorem odd_positive (k t : ℕ) (hk : 0 < k)
    (hkt : (k : ℤ) ≤ 2*(t : ℤ)*((t : ℤ)+1)) : PairCovers k (2*t+1) := by
  refine ⟨(1, ((t : ℤ) : ZMod (2*k))),
    (1, (((t : ℤ)+1 : ℤ) : ZMod (2*k))), consecutive_distinct k hk t, ?_⟩
  have hh := finite_cover k hk t ((t : ℤ)+1) (2*(t : ℤ)*((t : ℤ)+1))
    (2*(t : ℤ)+1) hkt (odd_integer_cover t (by positivity))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh

private theorem even_positive (k t : ℕ) (hk : 0 < k) (ht : 1 ≤ t)
    (hkt : (k : ℤ) ≤ 2*(t : ℤ)^2-(t : ℤ)) : PairCovers k (2*t) := by
  refine ⟨(1, (((t : ℤ)-1 : ℤ) : ZMod (2*k))),
    (1, ((t : ℤ) : ZMod (2*k))), ?_, ?_⟩
  · simpa only [sub_add_cancel] using consecutive_distinct k hk ((t : ℤ)-1)
  · have hh := finite_cover k hk ((t : ℤ)-1) t (2*(t : ℤ)^2-(t : ℤ))
      (2*(t : ℤ)) hkt (even_integer_cover t (by exact_mod_cast ht))
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh

/- Arithmetic/transport consumer of the EXISTING uniform sufficient family.
Use j=t^2-k/2 only after producing the genuine half k=2u. The upper strip
forces 2j<t, hence j<t, and all Nat subtractions are justified by u≤t^2. -/
private theorem top_positive (k t : ℕ) (hk : 0 < k) (ht : 1 ≤ t)
    (hlo : (2*(t : ℤ))^2-2*(t : ℤ) < 2*(k : ℤ))
    (hhi : 2*(k : ℤ) ≤ (2*(t : ℤ))^2)
    (hke : Even k) (hpar : Even t ∨ (Odd t ∧ k%4=2)) : PairCovers k (2*t) := by
  obtain ⟨u, hu⟩ := hke
  have hk2 : k = 2*u := by omega
  have hu_le : u ≤ t^2 := by
    have he : (k : ℤ) = 2*(u : ℤ) := by exact_mod_cast hk2
    have hh : (u : ℤ) ≤ (t : ℤ)^2 := by nlinarith [he]
    exact_mod_cast hh
  let j := t^2-u
  have hju : u+j=t^2 := by dsimp [j]; omega
  have hjZ : (u : ℤ)+(j : ℤ)=(t : ℤ)^2 := by exact_mod_cast hju
  have hkZ : (k : ℤ)=2*(u : ℤ) := by exact_mod_cast hk2
  have hjt : j < t := by
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
    have hh : (j : ℤ) < (t : ℤ) := by nlinarith [hjZ, hkZ]
    exact_mod_cast hh
  have hfamily : Even t ∨ Even j := by
    rcases hpar with he | ⟨ho, hkmod⟩
    · exact Or.inl he
    · have htmod : t%2=1 := Nat.odd_iff.mp ho
      have ht2mod : t^2%2=1 := by simp [Nat.pow_mod, htmod]
      have huodd : u%2=1 := by omega
      have hjmod : j%2=0 := by omega
      exact Or.inr ⟨j/2, by omega⟩
  have hmodulus : 4*(t^2-j)=2*k := by omega
  have hh := BajnokBeattyCayleySufficiency.result t j ht hjt hfamily
  rw [hmodulus] at hh
  simpa only [PairCovers, Target, Nat.cast_mul, Nat.cast_ofNat] using hh

/-- The literal original Conjecture 4.1, including every positive k and s
and the strict lower edge of both even top-strip regimes. -/
theorem result (k s : ℕ) (hk : 0 < k) (hs : 0 < s) :
    (∃ a b : ZMod 2 × ZMod (2*k), a ≠ b ∧ ∀ g, ∃ x y : ℤ,
      g = x • a + y • b ∧ |x|+|y| ≤ (s : ℤ)) ↔
    (Odd s ∧ 2*k ≤ s^2-1) ∨
    (Even s ∧ 2*k ≤ s^2-s) ∨
    (s%4=0 ∧ Even k ∧ s^2-s < 2*k ∧ 2*k ≤ s^2) ∨
    (s%4=2 ∧ k%4=2 ∧ s^2-s < 2*k ∧ 2*k ≤ s^2) := by
  change PairCovers k s ↔ _
  have hss : s ≤ s^2 := le_self_pow (by omega) (by decide)
  have hsub : s^2-s+s=s^2 := Nat.sub_add_cancel hss
  constructor
  · intro hc
    have hupper := pair_order_le hk hc
    rcases Nat.even_or_odd s with hse | hso
    · by_cases hlow : 2*k ≤ s^2-s
      · exact Or.inr (Or.inl ⟨hse, hlow⟩)
      · obtain ⟨t, ht'⟩ := hse
        have hst : s=2*t := by omega
        have ht : 1 ≤ t := by omega
        let r : ℤ := 2*(t : ℤ)^2-(k : ℤ)
        have hstZ : (s : ℤ)=2*(t : ℤ) := by exact_mod_cast hst
        have hupperZ : 2*(k : ℤ) ≤ (s : ℤ)^2 := by exact_mod_cast hupper
        have hstripN : s^2 < 2*k+s := by omega
        have hstripZ : (s : ℤ)^2 < 2*(k : ℤ)+(s : ℤ) := by exact_mod_cast hstripN
        rw [hstZ] at hupperZ hstripZ
        have hr : 0 ≤ r := by dsimp [r]; nlinarith
        have hrt : r < (t : ℤ) := by dsimp [r]; nlinarith
        have hkrel : (k : ℤ)=2*(t : ℤ)^2-r := by dsimp [r]; ring
        obtain ⟨a, b, _, hcov⟩ := hc
        have hcov' : ∀ g : Target k, ∃ x y : ℤ,
            |x|+|y| ≤ 2*(t : ℤ) ∧ x • a+y • b=g := by
          intro g
          obtain ⟨x, y, he, hb⟩ := hcov g
          exact ⟨x, y, by simpa only [hstZ] using hb, he.symm⟩
        obtain ⟨hr2, hr4⟩ := top_strip_necessity
          (by exact_mod_cast ht) hr hrt hkrel a b hcov'
        obtain ⟨u, hu⟩ := hr2
        have hkeZ : Even (k : ℤ) := ⟨(t : ℤ)^2-u, by dsimp [r] at hu; linarith⟩
        have hke : Even k := by exact_mod_cast hkeZ
        rcases Nat.even_or_odd t with hte | hto
        · have hsmod : s%4=0 := by obtain ⟨v, hv⟩ := hte; omega
          exact Or.inr (Or.inr (Or.inl ⟨hsmod, hke, by omega, hupper⟩))
        · have hsmod : s%4=2 := by obtain ⟨v, hv⟩ := hto; omega
          have htoZ : Odd (t : ℤ) := by exact_mod_cast hto
          obtain ⟨v, hv⟩ := hr4 htoZ
          obtain ⟨p, hp⟩ := htoZ
          have hkform : (k : ℤ)=4*(2*p*(p+1)-v)+2 := by
            dsimp [r] at hv
            rw [hp] at hv
            nlinarith [hv]
          have hkmod : k%4=2 := by omega
          exact Or.inr (Or.inr (Or.inr ⟨hsmod, hkmod, by omega, hupper⟩))
    · have hsmod : s%2=1 := Nat.odd_iff.mp hso
      have hsqmod : s^2%2=1 := by simp [Nat.pow_mod, hsmod]
      exact Or.inl ⟨hso, by omega⟩
  · intro h
    rcases h with ⟨hso, hb⟩ | ⟨hse, hb⟩ | ⟨hsmod, hke, hlo, hhi⟩ |
      ⟨hsmod, hkmod, hlo, hhi⟩
    · obtain ⟨t, ht⟩ := hso
      have hst : s=2*t+1 := by omega
      have hstZ : (s : ℤ)=2*(t : ℤ)+1 := by exact_mod_cast hst
      have hbN : 2*k+1 ≤ s^2 := by omega
      have hbZ : 2*(k : ℤ)+1 ≤ (s : ℤ)^2 := by exact_mod_cast hbN
      rw [hstZ] at hbZ
      have hkt : (k : ℤ) ≤ 2*(t : ℤ)*((t : ℤ)+1) := by nlinarith
      simpa only [hst] using odd_positive k t hk hkt
    · obtain ⟨t, ht'⟩ := hse
      have hst : s=2*t := by omega
      have ht : 1 ≤ t := by omega
      have hstZ : (s : ℤ)=2*(t : ℤ) := by exact_mod_cast hst
      have hbN : 2*k+s ≤ s^2 := by omega
      have hbZ : 2*(k : ℤ)+(s : ℤ) ≤ (s : ℤ)^2 := by exact_mod_cast hbN
      rw [hstZ] at hbZ
      have hkt : (k : ℤ) ≤ 2*(t : ℤ)^2-(t : ℤ) := by nlinarith
      simpa only [hst] using even_positive k t hk ht hkt
    · let t := s/2
      have hst : s=2*t := by dsimp [t]; omega
      have ht : 1 ≤ t := by omega
      have hte : Even t := ⟨t/2, by dsimp [t] at *; omega⟩
      have hstZ : (s : ℤ)=2*(t : ℤ) := by exact_mod_cast hst
      have hloN : s^2 < 2*k+s := by omega
      have hloZ : (s : ℤ)^2 < 2*(k : ℤ)+(s : ℤ) := by exact_mod_cast hloN
      have hhiZ : 2*(k : ℤ) ≤ (s : ℤ)^2 := by exact_mod_cast hhi
      rw [hstZ] at hloZ hhiZ
      have hh := top_positive k t hk ht (by nlinarith)
        (by nlinarith) hke (Or.inl hte)
      simpa only [hst] using hh
    · let t := s/2
      have hst : s=2*t := by dsimp [t]; omega
      have ht : 1 ≤ t := by omega
      have hto : Odd t := ⟨t/2, by dsimp [t] at *; omega⟩
      have hke : Even k := ⟨k/2, by omega⟩
      have hstZ : (s : ℤ)=2*(t : ℤ) := by exact_mod_cast hst
      have hloN : s^2 < 2*k+s := by omega
      have hloZ : (s : ℤ)^2 < 2*(k : ℤ)+(s : ℤ) := by exact_mod_cast hloN
      have hhiZ : 2*(k : ℤ) ≤ (s : ℤ)^2 := by exact_mod_cast hhi
      rw [hstZ] at hloZ hhiZ
      have hh := top_positive k t hk ht (by nlinarith)
        (by nlinarith) hke (Or.inr ⟨hto, hkmod⟩)
      simpa only [hst] using hh

end D5.S3.FiniteGroups.BajnokBeattyAllRegimes
