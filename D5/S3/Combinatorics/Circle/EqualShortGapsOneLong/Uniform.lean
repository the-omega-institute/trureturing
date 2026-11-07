/- GID: D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Uniform
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/EqualShortGapsOneLong/Uniform
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: One literal joint physical order for every number of equal short gaps and one long gap. -/
import D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Arithmetic
import D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.PacketStrip
import D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Physical
import D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Boundary
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private radix_ge geom_left seed_bound native_pair native_fresh long_charge_zero
  negative_charge positive_data packet_drift valley_drift negative_nonpos
  from D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Arithmetic
open private descending_packets_strip charged_strip inStrip_shift inStrip_congr
  from D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.PacketStrip
open private raw_inventory ascending_physical initialWord reserveWord middleWord
  middle_range initial_inventory physical_decomposition raw_last preWord pre_length
  lift_last_joint unit_physical unit_cut
  from D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Physical
open private ascending_unit periodic_ascending
  from D5.S3.Combinatorics.Circle.EqualShortGapsOneLong.Boundary
open private ladder_sum from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource
open private sum_linear from D5.S3.Combinatorics.Circle.PeriodicShortening

private theorem nonperiodic_joint (a p d : ℕ) (ha : 2 ≤ a) (hp : 2 ≤ p)
    (hd : a + 1 ≤ d) :
    OriginalOrder (size a p d) (geom a p) (physicalWord a p d (by dsimp [size]; omega)) ∧
    OriginalOrder (size a p d + 1) (2 * geom a p)
      (earWord (size a p d) (physicalWord a p d (by dsimp [size]; omega)) (cut a p d)) := by
  let k := size a p d
  let E : ℕ := geom a p
  let q : ℤ := 2 ^ (a - 1)
  let R : ℤ := 2 ^ a
  let l : ℤ := 2 ^ (d - a - 1)
  let A : ℤ := geom a (p - 1)
  let M : ℤ := R ^ (p - 1)
  let B : ℤ := 2 ^ (k - 1)
  let T : ℤ := q * A + 1
  let P : ℤ := A + 2 * l * M
  let delta : ℤ := if d ≤ a + 1 then 0 else l * E
  let f : ℕ → ℤ := fun i => centered (modulus k) ((2 : ℤ) ^ i * E)
  let g : ℕ → ℤ := fun i => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * E))
  let c : ℕ → ℤ := fun i =>
    let z := (E : ℤ) / (2 : ℤ) ^ (k - 1 - i)
    z / 2 + z % 2
  let U := initialWord a d
  let W := middleWord a p d
  let S := reserveWord a d
  let Z := List.range' (k - a) (a - 1)
  let H := B - 1
  let N := 2 * B - 1
  have hk : 2 ≤ k := by dsimp [k, size]; omega
  have hR := radix_ge a ha
  change 4 ≤ R at hR
  have hq : 1 ≤ q := by dsimp [q]; exact one_le_pow₀ (by norm_num)
  have hl : 1 ≤ l := by dsimp [l]; exact one_le_pow₀ (by norm_num)
  have hRtwo : R = 2 * q := by
    dsimp [R, q]
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hD : (2 : ℤ) ^ d = 2 * R * l := by
    dsimp [R, l]
    calc
      (2 : ℤ) ^ d = 2 ^ (a + (d - a - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ a * 2 ^ (d - a - 1) := by rw [pow_succ, pow_add]; ring
  have hB : B = R * l * M := by
    dsimp [B, M, k, size]
    rw [show d + a * (p - 1) - 1 = a + (d - a - 1) + a * (p - 1) by omega,
      pow_add, pow_add, pow_mul]
    rfl
  have hE : (E : ℤ) = R * A + 1 := by
    simpa only [show p - 1 + 1 = p by omega] using geom_left a (p - 1) (by omega)
  have hM : M = (R - 1) * A + 1 := by
    have h := geom_mul a (p - 1) (by omega)
    change (R - 1) * A = M - 1 at h
    omega
  have hA : 0 ≤ A := Int.natCast_nonneg _
  have hEpos : 1 ≤ (E : ℤ) := by nlinarith
  have hBpos : 1 ≤ B := by dsimp [B]; exact one_le_pow₀ (by norm_num)
  have hEB : (E : ℤ) ≤ B - 1 := by
    have hb := seed_bound a p d ha (by omega) (by omega)
    have hb' : geom a p + 1 ≤ 2 ^ (width a p d - 1) := by
      have := Nat.one_le_two_pow (n := width a p d - 1)
      omega
    have hb'' : (geom a p : ℤ) + 1 ≤ (2 : ℤ) ^ (width a p d - 1) := by exact_mod_cast hb'
    change (geom a p : ℤ) ≤ (2 : ℤ) ^ (width a p d - 1) - 1
    omega
  have hhalf : modulus k / 2 = H := by
    have he : (2 : ℤ) ^ k = 2 * B := by
      dsimp [B]
      calc
        (2 : ℤ) ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; ring
    dsimp [modulus, H]
    rw [he]
    omega
  have hhalf' : modulus (k + 1) / 2 = N := by
    have he : (2 : ℤ) ^ (k + 1) = 4 * B := by
      dsimp [B]
      rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
      ring
    dsimp [modulus, N]
    rw [he]
    omega
  have pair (i : ℕ) (hi : i < k) :
      0 ≤ c i ∧ f i = (2 : ℤ) ^ i * E - ((2 : ℤ) ^ k - 1) * c i ∧
        g i = 2 * f i - c i := by
    simpa only [actualSource, charge, Fin.val_mk, Fin.val_castSucc,
      Nat.cast_mul, Nat.cast_ofNat] using
      native_pair a p d ha (by omega) (by omega) ⟨i, hi⟩
  have fresh : g k = (E : ℤ) := by
    simpa only [actualSource, Fin.val_last, Nat.cast_mul, Nat.cast_ofNat] using
      native_fresh a p d ha (by omega) (by omega)
  have long (i : ℕ) (hi : i < d - 1) : c i = 0 ∧
      f i = (2 : ℤ) ^ i * E ∧ g i = (2 : ℤ) ^ i * (2 * E) := by
    have hik : i < k := by dsimp [k, size]; omega
    have hc := long_charge_zero a p d ha (by omega) (by omega) ⟨i, hik⟩ hi
    change c i = 0 at hc
    have hv := pair i hik
    refine ⟨hc, ?_, ?_⟩
    · rw [hc] at hv
      simpa only [mul_zero, sub_zero] using hv.2.1
    · rw [hv.2.2, hc, sub_zero, hv.2.1, hc]
      ring
  have neg_bound (j : ℕ) (hj : j < p) : d - 1 + a * j < k := by
    have hja := Nat.mul_le_mul_left a (show j ≤ p - 1 by omega)
    dsimp [k, size]
    omega
  have pos_bound (j u : ℕ) (hj : j + 1 < p) (hu : u < a - 1) : d + a * j + u < k := by
    have hja := Nat.mul_le_mul_left a (show j + 1 ≤ p - 1 by omega)
    dsimp [k, size]
    rw [Nat.mul_add] at hja
    omega
  have pos (j u : ℕ) (hj : j + 1 < p) (hu : u < a - 1) :
      c (d + a * j + u) = (2 : ℤ) ^ u * geom a (j + 1) ∧
      f (d + a * j + u) = (2 : ℤ) ^ u * packetBase a p d j ∧
      g (d + a * j + u) = (2 : ℤ) ^ u *
        (2 * packetBase a p d j - (geom a (j + 1) : ℤ)) ∧
      0 < packetBase a p d j ∧
      0 < 2 * packetBase a p d j - (geom a (j + 1) : ℤ) := by
    simpa only [actualSource, charge, Fin.val_mk, Fin.val_castSucc,
      Nat.cast_mul, Nat.cast_ofNat] using
      positive_data a p d j u ha (by omega) (by omega) hj hu (pos_bound j u hj hu)
  have hlastlabel : d - 1 + a * (p - 1) = k - 1 := by dsimp [k, size]; omega
  have last : c (k - 1) = T ∧ f (k - 1) = -B + T ∧ g (k - 1) = -2 * B + T := by
    have hc := (negative_charge a p d (p - 1) ha (by omega) (by omega)
      (by omega) (neg_bound (p - 1) (by omega))).2
    change 2 * c (d - 1 + a * (p - 1)) = (geom a (p - 1 + 1) : ℤ) + 1 at hc
    rw [hlastlabel, show p - 1 + 1 = p by omega] at hc
    have hcT : c (k - 1) = T := by
      dsimp [T]
      rw [hE, hRtwo] at hc
      nlinarith
    have hET : (E : ℤ) = 2 * T - 1 := by omega
    have hv := pair (k - 1) (by omega)
    have hpow : (2 : ℤ) ^ k = 2 * B := by
      dsimp [B]
      calc
        (2 : ℤ) ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; ring
    have hvf := hv.2.1
    change f (k - 1) = B * E - ((2 : ℤ) ^ k - 1) * c (k - 1) at hvf
    refine ⟨hcT, ?_, ?_⟩
    · rw [hpow, hcT, hET] at hvf
      nlinarith
    · rw [hv.2.2, hcT]
      rw [hpow, hcT, hET] at hvf
      nlinarith
  have hT : 1 ≤ T ∧ T ≤ (E : ℤ) := by
    have hqa : 0 ≤ q * A := mul_nonneg (by omega) hA
    dsimp [T]
    rw [hE, hRtwo]
    constructor <;> nlinarith
  have hbase : packetBase a p d (p - 2) = P := by
    have hg1 : geom a 1 = 1 := by
      have h := geom_mul a 1 (by omega)
      norm_num only [pow_one] at h
      have he : (geom a 1 : ℤ) = 1 := by nlinarith
      exact_mod_cast he
    dsimp [packetBase, P]
    rw [show p - 2 + 1 = p - 1 by omega, show p - 1 - (p - 2) = 1 by omega, hg1,
      Int.natCast_one, mul_one, hD]
    have hm : M = R * R ^ (p - 2) := by
      dsimp [M]
      rw [show p - 1 = (p - 2) + 1 by omega, pow_succ]
      ring
    rw [hm]
    ring
  have hoff : k - a = d + a * (p - 2) := by
    dsimp [k, size]
    rw [show p - 1 = (p - 2) + 1 by omega, Nat.mul_add]
    omega
  have zdata (u : ℕ) (hu : u < a - 1) :
      c (k - a + u) = (2 : ℤ) ^ u * A ∧
      f (k - a + u) = (2 : ℤ) ^ u * P ∧
      g (k - a + u) = (2 : ℤ) ^ u * (2 * P - A) := by
    have h := pos (p - 2) u (by omega) hu
    simpa only [hoff, show p - 2 + 1 = p - 1 by omega, hbase] using
      And.intro h.1 (And.intro h.2.1 h.2.2.1)
  have zmass : (Z.map f).sum = (q - 1) * P ∧ (Z.map c).sum = (q - 1) * A :=
    ⟨ladder_sum f (k - a) (a - 1) P (by intro u hu; exact (zdata u hu).2.1),
      ladder_sum c (k - a) (a - 1) A (by intro u hu; exact (zdata u hu).1)⟩
  have hS : (S.map f).sum = delta ∧ (S.map c).sum = 0 ∧
      (∀ i ∈ S, 0 ≤ f i ∧ 0 ≤ g i) := by
    dsimp [S, reserveWord, delta]
    split_ifs with h
    · simp
    · have ht : d - a - 1 < d - 1 := by omega
      have hx := long (d - a - 1) ht
      simp only [List.map_singleton, List.sum_singleton, hx.1, hx.2.1]
      refine ⟨rfl, rfl, ?_⟩
      intro i hi
      have he := List.mem_singleton.mp hi
      subst i
      rw [hx.2.1, hx.2.2]
      constructor <;> positivity
  have hinit := initial_inventory a d ha (by omega)
  have u_bound (i : ℕ) (hi : i ∈ U) : i < d - 1 :=
    List.mem_range.mp (hinit.mem_iff.mp (List.mem_append_left S hi))
  have u_positive : ∀ i ∈ U, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    rw [(long i (u_bound i hi)).2.1, (long i (u_bound i hi)).2.2]
    constructor <;> positivity
  have u_charge : (U.map c).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (long i (u_bound i hi)).1
  have umass : (U.map f).sum = (R * l - 1) * E - delta := by
    have hs := (hinit.map f).sum_eq
    rw [List.map_append, List.sum_append, hS.1] at hs
    have hf := ladder_sum f 0 (d - 1) E (by intro i hi; simpa using (long i hi).2.1)
    rw [← List.range_eq_range'] at hf
    have hdhalf : (2 : ℤ) ^ (d - 1) = R * l := by
      have he : d - 1 = a + (d - a - 1) := by omega
      dsimp [R, l]
      rw [he, pow_add]
    rw [hf, hdhalf] at hs
    omega
  have hraw := physical_decomposition a p d ha hp (by omega)
  have total_f : (U.map f).sum + (W.map f).sum + (S.map f).sum +
      (Z.map f).sum + f (k - 1) = 0 := by
    have hz := (ZeroSumSubsets.source_cycle (show 0 < k by omega) E).2.1
    have he := ((raw_inventory a p d ha (by omega) (by omega)).map f).sum_eq
    rw [hraw] at he
    rw [Fin.sum_univ_eq_sum_range] at hz
    have hz' : ((List.range k).map f).sum = 0 := by
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
      simpa only [actualSource, f] using hz
    rw [hz'] at he
    simpa only [List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, U, W, S, Z] using he
  have total_c : (U.map c).sum + (W.map c).sum + (S.map c).sum +
      (Z.map c).sum + c (k - 1) = (E : ℤ) := by
    have hz := charge_sum k E hk (seed_bound a p d ha (by omega) (by omega))
    have he := ((raw_inventory a p d ha (by omega) (by omega)).map c).sum_eq
    rw [hraw] at he
    rw [Fin.sum_univ_eq_sum_range] at hz
    have hz' : ((List.range k).map c).sum = (E : ℤ) := by
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
      simpa only [charge, c] using hz
    rw [hz'] at he
    simpa only [List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, U, W, S, Z] using he
  let F := (U.map f).sum
  let V := F + (W.map f).sum
  have hCmid : (W.map c).sum = A := by
    rw [u_charge, hS.2.1, zmass.2, last.1] at total_c
    dsimp [T] at total_c
    nlinarith [total_c, hE, hRtwo]
  have hV : V = (2 * l - 1) * M - delta := by
    rw [hS.1, zmass.1, last.2.1] at total_f
    change V + delta + (q - 1) * P + (-B + T) = 0 at total_f
    dsimp [P, T] at total_f
    rw [hB, hRtwo] at total_f
    have hm : M = (2 * q - 1) * A + 1 := by rw [← hRtwo]; exact hM
    nlinarith [hm]
  have hF : F ≤ H ∧ A ≤ V := by
    change (U.map f).sum ≤ B - 1 ∧ A ≤ V
    rw [umass, hV]
    by_cases hsmall : d ≤ a + 1
    · have hd' : d = a + 1 := by omega
      have hl' : l = 1 := by dsimp [l]; rw [hd']; norm_num
      simp only [delta, hsmall, ite_true, hl']
      have hp0 : (R - 1) * (E : ℤ) = B - 1 := by
        rw [hE, hB, hl', hM]
        ring
      constructor
      · simpa only [mul_one, sub_zero] using le_of_eq hp0
      · nlinarith [hM]
    · have hl' : 2 ≤ l := by
        dsimp [l]
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show 1 ≤ d - a - 1 by omega)
      simp only [delta, hsmall, ite_false]
      have hpoly : 0 ≤ ((l - 2) * (R - 2)) * A := by
        exact mul_nonneg (mul_nonneg (by omega) (by omega)) hA
      have hp0 : (R * l - 1) * (E : ℤ) - l * E = B - E - l := by
        rw [hE, hB, hM]
        ring
      constructor
      · rw [hp0]
        linarith
      · rw [hM]
        nlinarith [hpoly]
  have middle_bound (i : ℕ) (hi : i ∈ W) : i < k := by
    have hb : i ∈ rawWord a p d := by
      rw [hraw]
      simp only [List.mem_append, List.mem_singleton]
      tauto
    exact List.mem_range.mp ((raw_inventory a p d ha (by omega) (by omega)).mem_iff.mp hb)
  have middle_old : InStrip f (H - A) (F - A) W := by
    have h := descending_packets_strip f (fun j => d - 1 + a * j)
      (fun j => List.range' (d + a * j) (a - 1)) A H F 0 (p - 2)
    apply h
    · intro j hj hj'
      simpa only [actualSource, Fin.val_mk] using
        (negative_nonpos a p d j ha (by omega) (by omega) (by omega) (neg_bound j (by omega))).1
    · intro j hj hj' i hi
      have hb := List.mem_range'.mp hi
      have he : i = d + a * j + (i - (d + a * j)) := by omega
      rw [he, (pos j (i - (d + a * j)) (by omega) (by omega)).2.1]
      have hP := (pos j 0 (by omega) (by omega)).2.2.2.1
      positivity
    · intro j hj hj'
      have hdif := packet_drift a p d j ha (by omega) (by omega) (by omega) (neg_bound j (by omega))
      have hm := ladder_sum f (d + a * j) (a - 1) (packetBase a p d j)
        (by intro u hu; exact (pos j u (by omega) hu).2.1)
      have hRD := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a ≤ d by omega)
      have hs : 0 ≤ ((2 : ℤ) ^ a) ^ j := by positivity
      have hh : ((2 : ℤ) ^ a) ^ j * ((2 : ℤ) ^ a - 2 ^ d) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs (by omega)
      rw [hm]
      change 2 * (f (d - 1 + a * j) + (q - 1) * packetBase a p d j) = _ at hdif
      linarith
    · intro j hj hj'
      have hdif := valley_drift a p d j ha (by omega) (by omega) (by omega) (neg_bound (j + 1) (by omega))
      have hm := ladder_sum f (d + a * j) (a - 1) (packetBase a p d j)
        (by intro u hu; exact (pos j u (by omega) hu).2.1)
      have hRD := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a ≤ d by omega)
      have hs : 0 ≤ ((2 : ℤ) ^ a) ^ j := by positivity
      have hh : ((2 : ℤ) ^ a) ^ j * ((2 : ℤ) ^ a - 2 ^ d) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs (by omega)
      rw [hm]
      change (q - 1) * packetBase a p d j + f (d - 1 + a * (j + 1)) = _ at hdif
      linarith
    · exact hF.1
    · simpa only [← List.range_eq_range', Nat.zero_add, middleWord, W, V] using hF.2
  have middle_new : InStrip g N (2 * F) W := by
    have h := charged_strip W f c A H F 0 A N middle_old
      (by intro i hi; exact (pair i (middle_bound i hi)).1)
      (by norm_num) (by rw [hCmid]; omega) (by omega) (by dsimp [H, N]; omega)
    exact inStrip_congr (fun i => 2 * f i - c i) g N (2 * F) W
      (by intro i hi; exact (pair i (middle_bound i hi)).2.2.symm) (by simpa using h)
  have oldU : InStrip f H 0 U :=
    positive_block_strip (by intro i hi; exact (u_positive i hi).1) (by norm_num) (by simpa [F] using hF.1)
  have newU : InStrip g N 0 U := by
    apply positive_block_strip (by intro i hi; exact (u_positive i hi).2) (by norm_num)
    have hg : (U.map g).sum = 2 * F := by
      have he : U.map g = U.map (fun i => 2 * f i - c i) :=
        List.map_congr_left (by intro i hi; exact (pair i (by have := u_bound i hi; dsimp [k, size]; omega)).2.2)
      rw [he]
      have hs := sum_linear U f c 2 (-1)
      simpa only [sub_eq_add_neg, neg_mul, one_mul, u_charge, mul_zero, add_zero] using hs
    rw [hg]
    dsimp [N, H] at *
    omega
  have zpositive : ∀ i ∈ Z, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hb := List.mem_range'.mp hi
    have he : i = k - a + (i - (k - a)) := by omega
    rw [he, (zdata _ (by omega)).2.1, (zdata _ (by omega)).2.2]
    have h := pos (p - 2) 0 (by omega) (by omega)
    rw [hbase] at h
    constructor <;> positivity
  have oldtail : InStrip f H V (S ++ Z) := by
    apply positive_block_strip
      (by intro i hi; rcases List.mem_append.mp hi with hi | hi
          · exact (hS.2.2 i hi).1
          · exact (zpositive i hi).1)
      (by linarith [hF.2, hA])
    rw [List.map_append, List.sum_append, hS.1, zmass.1]
    rw [last.2.1] at total_f
    dsimp [V, F, H]
    linarith [hT.1]
  have newtail : InStrip g N (2 * V - A) (S ++ Z) := by
    apply positive_block_strip
      (by intro i hi; rcases List.mem_append.mp hi with hi | hi
          · exact (hS.2.2 i hi).2
          · exact (zpositive i hi).2)
      (by linarith [hF.2, hA])
    have tail_bound (i : ℕ) (hi : i ∈ S ++ Z) : i < k := by
      have hb : i ∈ rawWord a p d := by rw [hraw]; simp only [List.mem_append, List.mem_singleton] at *; tauto
      exact List.mem_range.mp ((raw_inventory a p d ha (by omega) (by omega)).mem_iff.mp hb)
    have he : ((S ++ Z).map g).sum = 2 * ((S ++ Z).map f).sum - ((S ++ Z).map c).sum := by
      rw [List.map_congr_left (by intro i hi; exact (pair i (tail_bound i hi)).2.2)]
      simpa only [sub_eq_add_neg, neg_mul, one_mul] using sum_linear (S ++ Z) f c 2 (-1)
    rw [he, List.map_append, List.sum_append, List.map_append, List.sum_append,
      hS.1, hS.2.1, zmass.1, zmass.2]
    rw [last.2.1] at total_f
    dsimp [V, F, N]
    nlinarith [total_f, hE, hRtwo, hT.1]
  have oldall : InStrip f H 0 (rawWord a p d) := by
    rw [hraw]
    have hm := inStrip_shift f A H F W hA middle_old
    have huwm := inStrip_append oldU (by simpa only [zero_add, F] using hm)
    have huwt := inStrip_append huwm (by simpa only [List.map_append, List.sum_append, zero_add, V, F] using oldtail)
    have hfinal : InStrip f H (B - T) [k - 1] := by
      simp only [InStrip, last.2.1]
      dsimp [H]
      constructor
      · linarith [hT.2, hEB]
      · constructor
        · linarith [hT.1]
        · constructor <;> linarith [hEB, hEpos]
    have hh : (U.map f).sum + (W.map f).sum + ((S ++ Z).map f).sum = B - T := by
      rw [last.2.1] at total_f
      linarith
    simpa only [List.append_assoc] using inStrip_append huwt (by
      simpa only [List.map_append, List.sum_append, zero_add, hh] using hfinal)
  have newall : InStrip g N 0 (preWord a p d ++ [k, k - 1]) := by
    have pre_eq : preWord a p d = U ++ W ++ S ++ Z := by
      apply List.append_cancel_right (l₂ := [k - 1])
      simpa only [← raw_last a p d ha (by omega) (by omega), U, W, S, Z] using hraw
    rw [pre_eq]
    have hgU : (U.map g).sum = 2 * F := by
      have he : U.map g = U.map (fun i => 2 * f i - c i) :=
        List.map_congr_left (by intro i hi; exact (pair i (by have := u_bound i hi; dsimp [k, size]; omega)).2.2)
      rw [he]
      simpa only [sub_eq_add_neg, neg_mul, one_mul, u_charge, mul_zero, add_zero] using
        sum_linear U f c 2 (-1)
    have hgW : (W.map g).sum = 2 * (W.map f).sum - A := by
      have he : W.map g = W.map (fun i => 2 * f i - c i) :=
        List.map_congr_left (by intro i hi; exact (pair i (middle_bound i hi)).2.2)
      rw [he]
      simpa only [sub_eq_add_neg, neg_mul, one_mul, hCmid] using sum_linear W f c 2 (-1)
    have huwm := inStrip_append newU (by simpa only [zero_add, hgU] using middle_new)
    have huwt := inStrip_append huwm (by
      simpa only [List.map_append, List.sum_append, zero_add, hgU, hgW, V, F,
        mul_add, sub_eq_add_neg, add_assoc] using newtail)
    have before : ((U ++ W ++ S ++ Z).map g).sum = 2 * B - E - T := by
      have hgraw := (ZeroSumSubsets.source_cycle (show 0 < k + 1 by omega) (2 * E)).2.1
      have he : ((rawWord a p d).map g).sum = -(E : ℤ) := by
        have inv : (rawWord a p d ++ [k]).Perm (List.range (k + 1)) := by
          simpa only [List.range_succ] using (raw_inventory a p d ha (by omega) (by omega)).append_right [k]
        have hs := (inv.map g).sum_eq
        rw [Fin.sum_univ_eq_sum_range] at hgraw
        have hz : ((List.range (k + 1)).map g).sum = 0 := by
          rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
          simpa only [actualSource, g, Nat.cast_mul, Nat.cast_ofNat] using hgraw
        rw [hz, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, fresh] at hs
        omega
      rw [hraw, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, last.2.2] at he
      simpa only [U, W, S, Z] using (show ((U ++ W ++ S ++ Z).map g).sum = 2 * B - E - T by omega)
    have hfinal : InStrip g N (2 * B - E - T) [k, k - 1] := by
      simp only [InStrip, fresh, last.2.2]
      dsimp [N]
      constructor
      · linarith [hT.2, hEB]
      · constructor
        · linarith [hEpos, hT.1]
        · constructor
          · linarith [hT.2, hEB]
          · constructor
            · linarith [hT.1]
            · constructor <;> linarith [hEB, hEpos]
    simpa only [List.append_assoc] using inStrip_append huwt (by
      simpa only [zero_add, before] using hfinal)
  exact lift_last_joint a p d E ha (by omega) (by omega) (by omega)
    (by simpa only [hhalf] using oldall) (by simpa only [hhalf'] using newall)

/-- A single explicit physical word works in both native coordinates, uniformly
in the number and length of the equal short gaps and in the long gap. -/
theorem actualSource_uniform_one_long_joint (a p d : ℕ)
    (ha : 2 ≤ a) (hp : 1 ≤ p) (hd : a ≤ d) :
    OriginalOrder (size a p d) (geom a p)
      (physicalWord a p d (by dsimp [size]; omega)) ∧
    OriginalOrder (size a p d + 1) (2 * geom a p)
      (earWord (size a p d) (physicalWord a p d (by dsimp [size]; omega)) (cut a p d)) := by
  by_cases hp1 : p = 1
  · subst p
    have hg1 : geom a 1 = 1 := by
      have h := geom_mul a 1 (by omega)
      norm_num only [pow_one] at h
      have hR := radix_ge a ha
      have he : (geom a 1 : ℤ) = 1 := by nlinarith
      exact_mod_cast he
    simpa only [unit_physical a d ha hd, unit_cut, size, Nat.sub_self,
      Nat.mul_zero, Nat.add_zero, hg1] using ascending_unit d (by omega)
  · by_cases hda : d = a
    · subst d
      have he : size a p a = a * p := by
        dsimp [size]
        have hp' : a * p = a * (p - 1) + a := by
          calc
            a * p = a * ((p - 1) + 1) := by congr 1; omega
            _ = a * (p - 1) + a := by ring
        omega
      simpa only [ascending_physical a p a (by dsimp [size]; omega) (by omega),
        cut, ite_true, he] using periodic_ascending a p ha (by omega)
    · exact nonperiodic_joint a p d ha (by omega) (by omega)

end D5.S3.Combinatorics.Circle.EqualShortGapsOneLong
