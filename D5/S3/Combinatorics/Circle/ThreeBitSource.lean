/- GID: D5/S3/Combinatorics/Circle/ThreeBitSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeBitSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex]
   utility: none
   digest: Exact labelled half-modulus schedules for all three-bit centered sources. -/
module
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.FinRange
import all D5.S3.Combinatorics.Circle.ThreeBitSourceResidual
import all D5.S3.Combinatorics.Circle.ThreeBitSourcePackets
public import D5.S3.Combinatorics.Circle.SourceWidth
public import D5.S3.Combinatorics.Circle.DyadicPrefix

/-! Exact unused-bit windows and physical three-ladder schedules. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeBitSource

open SourceWidth

/-- Exact floors determine the canonical first mask and its complementary mass. -/
private theorem first_packet (u v r C A : ℤ) (hu : 1 ≤ u) (hvu : u ≤ v)
    (hvodd : v % 2 = 1) (hC : C = r * u - (v + 1) / 2)
    (hA : A = C - (v - 1) / 2) (hA0 : 0 ≤ A) :
    let m := C / u
    let n := r - 1 - m
    0 ≤ m ∧ 0 ≤ n ∧ m + n = r - 1 ∧
      n = (v - 1) / (2 * u) ∧ A ≤ m * u ∧ m * u ≤ C ∧
      m * u - A = v - (n + 1) * u := by
  dsimp only
  let m := C / u
  let d := (v - 1) / 2
  let f := d / u
  change 0 ≤ m ∧ 0 ≤ r - 1 - m ∧ m + (r - 1 - m) = r - 1 ∧
    r - 1 - m = (v - 1) / (2 * u) ∧ A ≤ m * u ∧ m * u ≤ C ∧
    m * u - A = v - (r - 1 - m + 1) * u
  have hd : 2 * d = v - 1 := by dsimp [d]; omega
  have hv2 : (v + 1) / 2 = d + 1 := by omega
  rw [hv2] at hC
  change A = C - d at hA
  have hd0 : 0 ≤ d := by omega
  have he0 := Int.emod_nonneg d (by omega : u ≠ 0)
  have he1 := Int.emod_lt_of_pos d (by omega : 0 < u)
  have he := Int.emod_add_mul_ediv d u
  change d % u + u * f = d at he
  have hf0 : 0 ≤ f := Int.ediv_nonneg hd0 (by omega)
  have hC0 : 0 ≤ C := by omega
  have hm0 : 0 ≤ m := Int.ediv_nonneg hC0 (by omega)
  have hmrem0 := Int.emod_nonneg C (by omega : u ≠ 0)
  have hmrem1 := Int.emod_lt_of_pos C (by omega : 0 < u)
  have hme := Int.emod_add_mul_ediv C u
  change C % u + u * m = C at hme
  have hsum : m + f = r - 1 := by
    have hc : C = (r - 1) * u + u - d - 1 := by nlinarith only [hC]
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · have hm := mul_le_mul_of_nonneg_left (show m + f ≤ r - 2 by omega) (by omega : 0 ≤ u)
      nlinarith
    · have hm := mul_le_mul_of_nonneg_left (show r ≤ m + f by omega) (by omega : 0 ≤ u)
      nlinarith
  have hnf : r - 1 - m = f := by omega
  have hquot : f = (v - 1) / (2 * u) := by
    dsimp only [f, d]
    rw [Int.ediv_ediv]
    norm_num
  have hmass0 : 0 ≤ v - (f + 1) * u := by
    by_cases hf : f = 0
    · rw [hf]; omega
    · have hmul := mul_le_mul_of_nonneg_right (show f + 1 ≤ 2 * f by omega) (by omega : 0 ≤ u)
      nlinarith
  have hmul := congrArg (fun z : ℤ => z * u) hsum
  have hend : m * u - A = v - (f + 1) * u := by nlinarith only [hmul, hC, hA, hd]
  refine ⟨hm0, by omega, by omega, by rw [hnf]; exact hquot,
    by omega, by nlinarith only [hme, hmrem0], ?_⟩
  rw [hnf]
  exact hend

private theorem modulus_half (k : ℕ) (hk : 3 ≤ k) :
    1 < modulus k ∧ modulus k % 2 = 1 ∧
      modulus k = 2 * ((2 : ℤ) ^ (k - 1) - 1) + 1 := by
  have hp : (4 : ℤ) ≤ 2 ^ (k - 1) := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 2 ≤ k - 1 by omega)
    norm_num at this; exact this
  have he : modulus k = 2 * ((2 : ℤ) ^ (k - 1) - 1) + 1 := by
    unfold modulus
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  exact ⟨by omega, by omega, he⟩

/-- Reducing a physical index preserves the actual centered source. -/
private theorem centered_index_mod (k t i : ℕ) (hk : 3 ≤ k) :
    centered (modulus k) ((2 : ℤ) ^ (i % k) * t) =
      centered (modulus k) ((2 : ℤ) ^ i * t) := by
  obtain ⟨hN, hodd, _⟩ := modulus_half k hk
  have hpowk : (2 : ℤ) ^ k % modulus k = 1 := by
    rw [show (2 : ℤ) ^ k = modulus k + 1 by unfold modulus; ring,
      add_comm (modulus k) 1, Int.add_emod_right, Int.emod_eq_of_lt (by decide) hN]
  have hkmod : (2 : ℤ) ^ k ≡ 1 [ZMOD modulus k] := by
    change (2 : ℤ) ^ k % modulus k = 1 % modulus k
    rw [hpowk, Int.emod_eq_of_lt (by decide) hN]
  have hp : ((2 : ℤ) ^ k) ^ (i / k) % modulus k = 1 % modulus k := by
    have hp := hkmod.pow (i / k)
    change ((2 : ℤ) ^ k) ^ (i / k) % modulus k = (1 : ℤ) ^ (i / k) % modulus k at hp
    simpa only [one_pow] using hp
  have hpow : (2 : ℤ) ^ i % modulus k = (2 : ℤ) ^ (i % k) % modulus k := by
    conv_lhs => rw [← Nat.mod_add_div i k, pow_add, pow_mul]
    rw [Int.mul_emod, hp, Int.emod_eq_of_lt (by decide) hN, mul_one, Int.emod_emod]
  apply centered_unique (by omega) hodd (centered_bounds (by omega) hodd _)
    (centered_bounds (by omega) hodd _)
  rw [centered_mod, centered_mod]
  calc
    ((2 : ℤ) ^ (i % k) * t) % modulus k =
        ((2 : ℤ) ^ (i % k) % modulus k * ((t : ℤ) % modulus k)) % modulus k :=
      Int.mul_emod _ _ _
    _ = ((2 : ℤ) ^ i % modulus k * ((t : ℤ) % modulus k)) % modulus k := by rw [hpow]
    _ = ((2 : ℤ) ^ i * t) % modulus k := (Int.mul_emod _ _ _).symm

/-- The actual physical cycle has integer total zero, including repeated values. -/
private theorem source_zero (k t : ℕ) (hk : 3 ≤ k) :
    ((List.range k).map (fun i => centered (modulus k) ((2 : ℤ) ^ i * t))).sum = 0 := by
  let N := modulus k
  let v := fun i : ℕ => centered N ((2 : ℤ) ^ i * t)
  let U := fun i : ℕ => v i + if v i < 0 then N else 0
  change ((List.range k).map v).sum = 0
  obtain ⟨hN, hodd, _⟩ := modulus_half k hk
  have hstep (i : ℕ) : v (i + 1) = doubleStep N (v i) := by
    dsimp [v]
    rw [show (2 : ℤ) ^ (i + 1) * t = 2 * (2 ^ i * t) by rw [pow_succ]; ring]
    exact centered_double (by exact lt_trans (by decide : (0 : ℤ) < 1) hN) hodd _
  have hpot (i : ℕ) : U (i + 1) - U i = v i := by
    dsimp only [U]
    rw [hstep]
    exact unsigned_step (by omega) hodd (centered_bounds (by omega) hodd _)
  have hperiod : v k = v 0 := by
    simpa only [v, N, pow_zero, one_mul] using centered_full_period k t
  have hU : U k = U 0 := by simp only [U, hperiod]
  have hf : v = fun i => U (i + 1) - U i := funext (fun i => (hpot i).symm)
  rw [hf]
  simpa only [hU, sub_self] using List.sum_range_sub k U

/-- One cyclic three-bit rotation is an exact source congruence. -/
private theorem source_rotation (x y z i : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    centered (modulus (x + y + z)) ((2 : ℤ) ^ (i + z) * (1 + 2 ^ x + 2 ^ (x + y))) =
      centered (modulus (x + y + z)) ((2 : ℤ) ^ i * (1 + 2 ^ z + 2 ^ (z + x))) := by
  obtain ⟨hN, hodd, _⟩ := modulus_half (x + y + z) (by omega)
  apply centered_unique (by omega) hodd (centered_bounds (by omega) hodd _)
    (centered_bounds (by omega) hodd _)
  rw [centered_mod, centered_mod]
  have he : (2 : ℤ) ^ (i + z) * (1 + 2 ^ x + 2 ^ (x + y)) =
      2 ^ i * (1 + 2 ^ z + 2 ^ (z + x)) + 2 ^ i * modulus (x + y + z) := by
    simp only [modulus, pow_add]; ring
  rw [he, Int.add_mul_emod_self_right]

/-- Exact representatives for a full positive ladder and its following negative label. -/
private theorem centered_ladder (N u v : ℤ) (z e : ℕ)
    (hN : 0 < N) (hodd : N % 2 = 1) (hu : 0 < u)
    (hv : 1 ≤ v ∧ v ≤ N) (he : e < z)
    (hrel : (2 : ℤ) ^ z * u = N + v) :
    centered N ((2 : ℤ) ^ e * u) =
      if e + 1 < z then (2 : ℤ) ^ e * u else -(N - v) / 2 := by
  have hhalf := Int.emod_add_mul_ediv N 2
  by_cases hez : e + 1 < z
  · rw [ite_eq_left hez]
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show e + 2 ≤ z by omega)
    rw [pow_add] at hp
    norm_num at hp
    have hm := mul_le_mul_of_nonneg_right hp (le_of_lt hu)
    apply centered_unique hN hodd (centered_bounds hN hodd _) ?_ (centered_mod N _)
    have hx0 : 0 ≤ (2 : ℤ) ^ e * u := by positivity
    have hn0 : 0 ≤ N / 2 := Int.ediv_nonneg (le_of_lt hN) (by decide)
    exact ⟨by omega, by nlinarith⟩
  · rw [ite_eq_right hez]
    have hexp : z = e + 1 := by omega
    have hp : 2 * ((2 : ℤ) ^ e * u) = N + v := by rw [hexp, pow_succ] at hrel; nlinarith
    have hval : -(N - v) / 2 = (2 : ℤ) ^ e * u - N := by omega
    rw [hval]
    apply centered_unique hN hodd (centered_bounds hN hodd _) ?_ ?_
    · constructor <;> omega
    · rw [centered_mod, Int.sub_emod_right]

/-- Minimum choice retains all ties and forces the long final support gap. -/
private theorem minimum_gaps (x y z : ℕ) (hx : 0 < x) (hz : 0 < z)
    (hk : 4 ≤ x + y + z)
    (hv : (1 : ℤ) + 2 ^ x + 2 ^ (x + y) ≤ 1 + 2 ^ z + 2 ^ (z + x))
    (hw : (1 : ℤ) + 2 ^ x + 2 ^ (x + y) ≤ 1 + 2 ^ y + 2 ^ (y + z)) :
    x ≤ z ∧ y ≤ z ∧ (z = x → x = y ∧ y = z) ∧ 2 ≤ z := by
  have hx0 : (0 : ℤ) ≤ 2 ^ x := by positivity
  have hyz : y ≤ z := by
    by_contra h
    have htop := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show z + x + 1 ≤ x + y by omega)
    rw [pow_succ] at htop
    have hsmall := pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (show z < z + x by omega)
    nlinarith
  have hxz : x ≤ z := by
    by_contra h
    have htop := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show y + z + 1 ≤ x + y by omega)
    rw [pow_succ] at htop
    have hsmall := pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (show y < y + z by omega)
    nlinarith
  have htie : z = x → x = y ∧ y = z := by
    intro hzx
    have hp : (2 : ℤ) ^ x ≤ 2 ^ y := by
      rw [hzx, Nat.add_comm y x] at hw
      linarith
    have hxy : x ≤ y := by
      by_contra h
      have hh := pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (show y < x by omega)
      omega
    omega
  exact ⟨hxz, hyz, htie, by omega⟩

/-- The three complete physical blocks are derived from the original centered source. -/
private theorem actual_source_chains (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 2 ≤ z) :
    let P : ℤ := 2 ^ x
    let Q : ℤ := 2 ^ y
    let R : ℤ := 2 ^ z
    let N := modulus (x + y + z)
    let u := 1 + P + P * Q
    let v := 1 + R + R * P
    let w := 1 + Q + Q * R
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
    (1 ≤ u ∧ u < N) ∧ (1 ≤ v ∧ v < N) ∧ (1 ≤ w ∧ w < N) ∧
      (R * u = N + v ∧ Q * v = N + w ∧ P * w = N + u) ∧
      (∀ e < z, f e = if e + 1 < z then (2 : ℤ) ^ e * u else -(N - v) / 2) ∧
      (∀ e < y, f (z + e) = if e + 1 < y then (2 : ℤ) ^ e * v else -(N - w) / 2) ∧
      (∀ e < x, f (z + y + e) = if e + 1 < x then (2 : ℤ) ^ e * w else -(N - u) / 2) := by
  dsimp only
  let P : ℤ := 2 ^ x
  let Q : ℤ := 2 ^ y
  let R : ℤ := 2 ^ z
  let N := modulus (x + y + z)
  let u := 1 + P + P * Q
  let v := 1 + R + R * P
  let w := 1 + Q + Q * R
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
  change (1 ≤ u ∧ u < N) ∧ (1 ≤ v ∧ v < N) ∧ (1 ≤ w ∧ w < N) ∧
    (R * u = N + v ∧ Q * v = N + w ∧ P * w = N + u) ∧
    (∀ e < z, f e = if e + 1 < z then (2 : ℤ) ^ e * u else -(N - v) / 2) ∧
    (∀ e < y, f (z + e) = if e + 1 < y then (2 : ℤ) ^ e * v else -(N - w) / 2) ∧
    (∀ e < x, f (z + y + e) = if e + 1 < x then (2 : ℤ) ^ e * w else -(N - u) / 2)
  have hP : 2 ≤ P := by
    simpa [P] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hx
  have hQ : 2 ≤ Q := by
    simpa [Q] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hy
  have hR : 4 ≤ R := by
    simpa [R] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hz
  have hNprod : N = P * Q * R - 1 := by simp [N, modulus, P, Q, R, pow_add]
  have hU : 1 ≤ u ∧ u < N := by
    have h1 := mul_le_mul_of_nonneg_left hR (show 0 ≤ P * Q by positivity)
    have h2 := mul_le_mul_of_nonneg_left hQ (show 0 ≤ P by omega)
    dsimp [u]; constructor <;> nlinarith
  have hV : 1 ≤ v ∧ v < N := by
    have h1 := mul_le_mul_of_nonneg_left hQ (show 0 ≤ P * R by positivity)
    have h2 := mul_le_mul_of_nonneg_left hP (show 0 ≤ R by omega)
    dsimp [v]; constructor <;> nlinarith
  have hW : 1 ≤ w ∧ w < N := by
    have h1 := mul_le_mul_of_nonneg_left hP (show 0 ≤ Q * R by positivity)
    have h2 := mul_le_mul_of_nonneg_left hR (show 0 ≤ Q by omega)
    dsimp [w]; constructor <;> nlinarith
  have hrel : R * u = N + v ∧ Q * v = N + w ∧ P * w = N + u := by
    rw [hNprod]; dsimp [u, v, w]; refine ⟨?_, ?_, ?_⟩ <;> ring
  obtain ⟨hN, hodd, _⟩ := modulus_half (x + y + z) (by omega)
  have hvrot (e : ℕ) : f (z + e) = centered N ((2 : ℤ) ^ e * v) := by
    dsimp [f, N, u, v, P, Q, R]
    simpa only [pow_add, mul_comm, mul_left_comm, mul_assoc] using
      source_rotation x y z e hx hy (by omega)
  refine ⟨hU, hV, hW, hrel, ?_, ?_, ?_⟩
  · intro e he
    exact centered_ladder N u v z e (by omega) hodd (by omega) ⟨hV.1, by omega⟩
      he hrel.1
  · intro e he
    rw [hvrot]
    exact centered_ladder N v w y e (by omega) hodd (by omega) ⟨hW.1, by omega⟩
      he hrel.2.1
  · intro e he
    rw [show z + y + e = z + (y + e) by omega, hvrot]
    have hwrot : centered N ((2 : ℤ) ^ (y + e) * v) = centered N ((2 : ℤ) ^ e * w) := by
      dsimp [N, v, w, P, Q, R]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        pow_add, mul_comm, mul_left_comm, mul_assoc] using source_rotation z x y e (by omega) hx hy
    rw [hwrot]
    exact centered_ladder N w u x e (by omega) hodd (by omega) ⟨hU.1, by omega⟩
      he hrel.2.2

/-- The complementary first coefficient is exactly the complementary bit support. -/
private theorem mask_complement (u m n : ℕ) (h : m + n = 2 ^ u - 1) :
    Disjoint m.bitIndices.toFinset n.bitIndices.toFinset ∧
      m.bitIndices.toFinset ∪ n.bitIndices.toFinset = Finset.range u := by
  classical
  have hm : m < 2 ^ u := by
    have hp : 0 < 2 ^ u := by positivity
    omega
  have hsub : m.bitIndices.toFinset ⊆ Finset.range u := by
    intro i hi
    have hpow := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
    apply Finset.mem_range.mpr
    by_contra h'
    have hle := Nat.pow_le_pow_right (by decide : 0 < 2) (show u ≤ i by omega)
    omega
  let A := Finset.range u \ m.bitIndices.toFinset
  have hdis : Disjoint A m.bitIndices.toFinset := Finset.disjoint_left.mpr
    (fun i hi hmi => (Finset.mem_sdiff.mp hi).2 hmi)
  have hfull : A ∪ m.bitIndices.toFinset = Finset.range u := Finset.sdiff_union_of_subset hsub
  have hs := Finset.sum_union hdis (f := fun i : ℕ => 2 ^ i)
  have hsum : ∑ i ∈ Finset.range u, 2 ^ i = 2 ^ u - 1 := by
    simpa using Nat.geomSum_eq (by decide : 2 ≤ 2) u
  rw [hfull, Finset.sum_toFinset_bitIndices_two_pow, hsum] at hs
  have hA : n.bitIndices.toFinset = A := by
    apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
    dsimp only
    rw [Finset.sum_toFinset_bitIndices_two_pow]
    omega
  rw [hA]
  exact ⟨hdis.symm, by simpa only [Finset.union_comm] using hfull⟩

private theorem positive_block_strip {α : Type*} {f : α → ℤ} {C h : ℤ} {l : List α}
    (hp : ∀ i ∈ l, 0 ≤ f i) (hh : 0 ≤ h) (hend : h + (l.map f).sum ≤ C) :
    InStrip f C h l := by
  apply inStrip_reflect
  apply inStrip_nonpos
  · intro i hi; have := hp i hi; omega
  · omega
  · rw [sum_neg_map]; omega

/-- The six physical blocks give every prefix once all seven seams are controlled. -/
private theorem physical_schedule {α : Type*} (f : α → ℤ) (labels F Q G : List α)
    (av aw au : α) (Av Aw Au C : ℤ)
    (hperm : (F ++ av :: Q ++ aw :: G ++ [au]).Perm labels)
    (hAv : f av = -Av) (hAw : f aw = -Aw) (hAu : f au = -Au)
    (hAv0 : 0 ≤ Av) (hAw0 : 0 ≤ Aw) (hAuC : 0 ≤ Au ∧ Au ≤ C)
    (hFpos : ∀ i ∈ F, 0 ≤ f i) (hQpos : ∀ i ∈ Q, 0 ≤ f i)
    (hGpos : ∀ i ∈ G, 0 ≤ f i)
    (hFmass : Av ≤ (F.map f).sum ∧ (F.map f).sum ≤ C)
    (hQmass : Aw ≤ (F.map f).sum - Av + (Q.map f).sum ∧
      (F.map f).sum - Av + (Q.map f).sum ≤ C)
    (htotal : (labels.map f).sum = 0) :
    InStrip f C 0 (F ++ av :: Q ++ aw :: G ++ [au]) := by
  have hs := (hperm.map f).sum_eq
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, add_zero, hAv, hAw, hAu, htotal] at hs
  have hlast : (F.map f).sum - Av + (Q.map f).sum - Aw + (G.map f).sum = Au := by omega
  have hg : InStrip f C ((F.map f).sum - Av + (Q.map f).sum - Aw) (G ++ [au]) := by
    apply inStrip_append (positive_block_strip hGpos (by omega) (by omega))
    simp only [InStrip, hAu]
    omega
  have hq : InStrip f C ((F.map f).sum - Av) (Q ++ aw :: G ++ [au]) := by
    simp only [List.append_assoc]
    apply inStrip_append (l := Q) (r := aw :: (G ++ [au]))
      (positive_block_strip hQpos (by omega) hQmass.2)
    change 0 ≤ (F.map f).sum - Av + (Q.map f).sum ∧
      (F.map f).sum - Av + (Q.map f).sum ≤ C ∧ _
    refine ⟨by omega, hQmass.2, ?_⟩
    simpa only [hAw, ← sub_eq_add_neg] using hg
  simp only [List.append_assoc]
  apply inStrip_append (l := F) (r := av :: (Q ++ (aw :: (G ++ [au]))))
    (positive_block_strip hFpos (le_refl 0) (by simpa using hFmass.2))
  change 0 ≤ 0 + (F.map f).sum ∧ 0 + (F.map f).sum ≤ C ∧ _
  refine ⟨by omega, by omega, ?_⟩
  simpa only [zero_add, hAv, ← sub_eq_add_neg, List.append_assoc, List.cons_append] using hq

/-- Masks select original ladder positions through the existing bounded decoder. -/
private def mask_labels (len off x : ℕ) (hx : x < 2 ^ len) : Finset ℕ :=
  (DyadicPrefix.bitSubset len x hx).image (fun i => off + i.val)

private theorem mask_labels_mem (len off x i : ℕ) (hx : x < 2 ^ len) :
    i ∈ mask_labels len off x hx ↔
      ∃ e : ℕ, e < len ∧ x.testBit e = true ∧ off + e = i := by
  classical
  constructor
  · intro hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨e, e.isLt, (DyadicPrefix.bit_subset_mem hx).mp he, rfl⟩
  · rintro ⟨e, he, hb, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨e, he⟩, (DyadicPrefix.bit_subset_mem hx).mpr hb, rfl⟩

private theorem mask_labels_bound {len off x i : ℕ} {hx : x < 2 ^ len}
    (hi : i ∈ mask_labels len off x hx) : off ≤ i ∧ i < off + len := by
  obtain ⟨e, he, _, hi⟩ := (mask_labels_mem len off x i hx).mp hi
  omega

private theorem mask_labels_disjoint {len off x y : ℕ}
    {hx : x < 2 ^ len} {hy : y < 2 ^ len}
    (hxy : Disjoint x.bitIndices.toFinset y.bitIndices.toFinset) :
    Disjoint (mask_labels len off x hx) (mask_labels len off y hy) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨e, he, hb, hei⟩ := (mask_labels_mem len off x i hx).mp hi
  obtain ⟨e', he', hb', he'i⟩ := (mask_labels_mem len off y i hy).mp hj
  have heq : e' = e := by omega
  subst e'
  exact Finset.disjoint_left.mp hxy (by simpa using Nat.mem_bitIndices.mpr hb)
    (by simpa using Nat.mem_bitIndices.mpr hb')

private theorem mask_labels_sum (len off x : ℕ) (hx : x < 2 ^ len)
    (f : ℕ → ℤ) (A : ℤ) (hf : ∀ e < len, f (off + e) = (2 : ℤ) ^ e * A) :
    ∑ i ∈ mask_labels len off x hx, f i = (x : ℤ) * A := by
  classical
  have hinj : Function.Injective (fun i : Fin len => off + i.val) := by
    intro i j hij
    apply Fin.ext
    change off + i.val = off + j.val at hij
    omega
  unfold mask_labels
  rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
  simp_rw [hf _ (Fin.isLt _)]
  rw [← Finset.sum_mul]
  have hs : (∑ i ∈ DyadicPrefix.bitSubset len x hx, (2 : ℤ) ^ i.val) = (x : ℤ) := by
    exact_mod_cast DyadicPrefix.bit_subset_sum hx
  rw [hs]

/-- Disjoint physical supports, including three separate event labels, exhaust the whole word. -/
private theorem labelled_permutation (k av aw au : ℕ) (F Q : Finset ℕ)
    (hF : F ⊆ Finset.range k) (hQ : Q ⊆ Finset.range k)
    (hFQ : Disjoint F Q)
    (hne : av ≠ aw ∧ av ≠ au ∧ aw ≠ au)
    (hneg : av < k ∧ aw < k ∧ au < k)
    (hFn : ∀ i ∈ F, i ≠ av ∧ i ≠ aw ∧ i ≠ au)
    (hQn : ∀ i ∈ Q, i ≠ av ∧ i ≠ aw ∧ i ≠ au) :
    let G := Finset.range k \ (F ∪ Q ∪ {av, aw, au})
    (F.toList ++ av :: Q.toList ++ aw :: G.toList ++ [au]).Perm (List.range k) := by
  classical
  let E : Finset ℕ := ⟨(([av, aw, au] : List ℕ) : Multiset ℕ), by
    simpa using (show ([av, aw, au] : List ℕ).Nodup by simp [hne.1, hne.2.1, hne.2.2])⟩
  have hE (i : ℕ) : i ∈ E ↔ i = av ∨ i = aw ∨ i = au := by simp [E]
  have hEs : E = {av, aw, au} := by ext i; simp [hE]
  let G := Finset.range k \ (F ∪ Q ∪ E)
  have hG : G = Finset.range k \ (F ∪ Q ∪ {av, aw, au}) := by dsimp only [G]; rw [hEs]
  have hFG : Disjoint (F.disjUnion Q hFQ) G := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' : i ∈ F ∪ Q ∪ E := by
      simp only [Finset.mem_union]
      have hh := Finset.mem_disjUnion.mp hi
      tauto
    exact (Finset.mem_sdiff.mp hj).2 hi'
  have hNE : Disjoint ((F.disjUnion Q hFQ).disjUnion G hFG) E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have he := (hE i).mp hj
    simp only [Finset.mem_disjUnion] at hi
    rcases hi with (hi | hi) | hi
    · obtain ⟨ha, hb, hc⟩ := hFn i hi
      tauto
    · obtain ⟨ha, hb, hc⟩ := hQn i hi
      tauto
    · exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_right _ hj)
  let T := ((F.disjUnion Q hFQ).disjUnion G hFG).disjUnion E hNE
  have hT : T = Finset.range k := by
    ext i
    have hFi : i ∈ F → i ∈ Finset.range k := fun hi => hF hi
    have hQi : i ∈ Q → i ∈ Finset.range k := fun hi => hQ hi
    have hEi : i ∈ E → i ∈ Finset.range k := by
      intro hi
      rcases (hE i).mp hi with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    simp only [T, G, Finset.mem_disjUnion, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [← hG]
  apply Multiset.coe_eq_coe.mp
  have hs :
      ((F.toList ++ av :: Q.toList ++ aw :: G.toList ++ [au] : List ℕ) : Multiset ℕ) =
        T.val := by
    change (F.toList : Multiset ℕ) + ({av} + (Q.toList : Multiset ℕ)) +
      ({aw} + (G.toList : Multiset ℕ)) + {au} =
        F.val + Q.val + G.val + ({av} + {aw} + {au})
    simp only [Finset.coe_toList]
    ac_rfl
  rw [hs, hT]
  rfl

/-- The three bounded masks are assembled without identifying equal source values. -/
private theorem masked_schedule (x y z m n c dV dW : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 2 ≤ z)
    (f : ℕ → ℤ) (u v w Av Aw Au C : ℤ)
    (hU : ∀ e < z - 1, f e = (2 : ℤ) ^ e * u)
    (hV : ∀ e < y - 1, f (z + e) = (2 : ℤ) ^ e * v)
    (hW : ∀ e < x - 1, f (z + y + e) = (2 : ℤ) ^ e * w)
    (hAv : f (z - 1) = -Av) (hAw : f (z + y - 1) = -Aw)
    (hAu : f (x + y + z - 1) = -Au)
    (hpos : ∀ i < x + y + z,
      i ≠ z - 1 → i ≠ z + y - 1 → i ≠ x + y + z - 1 → 0 ≤ f i)
    (hAv0 : 0 ≤ Av) (hAw0 : 0 ≤ Aw) (hAuC : 0 ≤ Au ∧ Au ≤ C)
    (hcomp : m + n = 2 ^ (z - 1) - 1)
    (hc : c.bitIndices.toFinset ⊆ n.bitIndices.toFinset)
    (hdV : dV < 2 ^ (y - 1)) (hdW : dW < 2 ^ (x - 1))
    (hFmass : Av ≤ (m : ℤ) * u ∧ (m : ℤ) * u ≤ C)
    (hQmass : Aw ≤ (m : ℤ) * u - Av + (c : ℤ) * u + dV * v + dW * w ∧
      (m : ℤ) * u - Av + (c : ℤ) * u + dV * v + dW * w ≤ C)
    (htotal : ((List.range (x + y + z)).map f).sum = 0) :
    ∃ word : List ℕ, word.Perm (List.range (x + y + z)) ∧ InStrip f C 0 word := by
  classical
  have hp : 0 < 2 ^ (z - 1) := by positivity
  have hmB : m < 2 ^ (z - 1) := by omega
  have hnB : n < 2 ^ (z - 1) := by omega
  have hcn : c ≤ n := by
    have hs := Finset.sum_le_sum_of_subset (f := fun i : ℕ => 2 ^ i) hc
    simpa only [Finset.sum_toFinset_bitIndices_two_pow] using hs
  have hcB : c < 2 ^ (z - 1) := by omega
  let F := mask_labels (z - 1) 0 m hmB
  let A := mask_labels (z - 1) 0 c hcB
  let V := mask_labels (y - 1) z dV hdV
  let W := mask_labels (x - 1) (z + y) dW hdW
  let Q := A ∪ V ∪ W
  let G := Finset.range (x + y + z) \ (F ∪ Q ∪ {z - 1, z + y - 1, x + y + z - 1})
  have hinterval (i : ℕ)
      (hi : i < z - 1 ∨ (z ≤ i ∧ i < z + y - 1) ∨
        (z + y ≤ i ∧ i < z + y + x - 1)) :
      i < x + y + z ∧ i ≠ z - 1 ∧ i ≠ z + y - 1 ∧ i ≠ x + y + z - 1 := by omega
  have hFgood (i : ℕ) (hi : i ∈ F) :
      i < x + y + z ∧ i ≠ z - 1 ∧ i ≠ z + y - 1 ∧ i ≠ x + y + z - 1 := by
    have hb := mask_labels_bound hi
    exact hinterval i (Or.inl (by omega))
  have hQgood (i : ℕ) (hi : i ∈ Q) :
      i < x + y + z ∧ i ≠ z - 1 ∧ i ≠ z + y - 1 ∧ i ≠ x + y + z - 1 := by
    simp only [Q, Finset.mem_union] at hi
    rcases hi with (hi | hi) | hi
    · have hb := mask_labels_bound hi
      exact hinterval i (Or.inl (by omega))
    · have hb := mask_labels_bound hi
      exact hinterval i (Or.inr (Or.inl (by omega)))
    · have hb := mask_labels_bound hi
      exact hinterval i (Or.inr (Or.inr (by omega)))
  have hmc := (mask_complement (z - 1) m n hcomp).1
  have hMA : Disjoint F A := by
    apply mask_labels_disjoint
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hmc hi (hc hj)
  have hFQ : Disjoint F Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hb := mask_labels_bound hi
    simp only [Q, Finset.mem_union] at hj
    rcases hj with (hj | hj) | hj
    · exact Finset.disjoint_left.mp hMA hi hj
    · have hb' := mask_labels_bound hj; omega
    · have hb' := mask_labels_bound hj; omega
  have hAV : Disjoint A V := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hb := mask_labels_bound hi
    have hb' := mask_labels_bound hj
    omega
  have hAVW : Disjoint (A ∪ V) W := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hb := mask_labels_bound hj
    rcases Finset.mem_union.mp hi with hi | hi <;>
      have hb' := mask_labels_bound hi <;> omega
  have hperm := labelled_permutation (x + y + z) (z - 1) (z + y - 1)
    (x + y + z - 1) F Q (fun i hi => Finset.mem_range.mpr (hFgood i hi).1)
    (fun i hi => Finset.mem_range.mpr (hQgood i hi).1) hFQ
    ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
    (fun i hi => (hFgood i hi).2) (fun i hi => (hQgood i hi).2)
  change (F.toList ++ (z - 1) :: Q.toList ++ (z + y - 1) :: G.toList ++
    [x + y + z - 1]).Perm _ at hperm
  have hsum (S : Finset ℕ) : (S.toList.map f).sum = ∑ i ∈ S, f i := by
    change ((S.toList : Multiset ℕ).map f).sum = _
    rw [Finset.coe_toList]
    rfl
  have hFs : (F.toList.map f).sum = (m : ℤ) * u := by
    rw [hsum]
    exact mask_labels_sum (z - 1) 0 m hmB f u (fun e he => by simpa using hU e he)
  have hQs : (Q.toList.map f).sum = (c : ℤ) * u + dV * v + dW * w := by
    rw [hsum, Finset.sum_union hAVW, Finset.sum_union hAV]
    rw [mask_labels_sum (z - 1) 0 c hcB f u (fun e he => by simpa using hU e he),
      mask_labels_sum (y - 1) z dV hdV f v hV,
      mask_labels_sum (x - 1) (z + y) dW hdW f w hW]
  refine ⟨_, hperm, physical_schedule f (List.range (x + y + z)) F.toList
    Q.toList G.toList (z - 1) (z + y - 1) (x + y + z - 1) Av Aw Au C
    hperm hAv hAw hAu hAv0 hAw0 hAuC ?_ ?_ ?_ ?_ ?_ htotal⟩
  · intro i hi
    have hh := hFgood i (Finset.mem_toList.mp hi)
    exact hpos i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  · intro i hi
    have hh := hQgood i (Finset.mem_toList.mp hi)
    exact hpos i hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  · intro i hi
    have hh := Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)
    have hn : i ≠ z - 1 ∧ i ≠ z + y - 1 ∧ i ≠ x + y + z - 1 := by
      have hn0 : i ∉ {z - 1, z + y - 1, x + y + z - 1} :=
        fun h => hh.2 (Finset.mem_union_right _ h)
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hn0
    exact hpos i (Finset.mem_range.mp hh.1) hn.1 hn.2.1 hn.2.2
  · simpa only [hFs] using hFmass
  · simpa only [hFs, hQs, add_assoc] using hQmass


set_option maxHeartbeats 1000000 in
-- The source-to-mask composition combines several exact integer quotients.
/-- A minimum cyclic orientation yields a schedule of all its physical positions. -/
private theorem normalized_order (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 4 ≤ x + y + z) :
    let N := modulus (x + y + z)
    let P : ℤ := 2 ^ x
    let Q : ℤ := 2 ^ y
    let R : ℤ := 2 ^ z
    let u := 1 + P + P * Q
    let v := 1 + R + R * P
    let w := 1 + Q + Q * R
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
    let C := (2 : ℤ) ^ (x + y + z - 1) - 1
    u ≤ v → u ≤ w →
      ∃ word : List ℕ, word.Perm (List.range (x + y + z)) ∧
        InStrip f C 0 word ∧ (word.map f).sum = 0 := by
  dsimp only
  let N := modulus (x + y + z)
  let P : ℤ := 2 ^ x
  let Q : ℤ := 2 ^ y
  let R : ℤ := 2 ^ z
  let u := 1 + P + P * Q
  let v := 1 + R + R * P
  let w := 1 + Q + Q * R
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * u)
  let C := (2 : ℤ) ^ (x + y + z - 1) - 1
  change u ≤ v → u ≤ w → _
  intro huv huw
  obtain ⟨hxz, hyz, _, hz2⟩ := minimum_gaps x y z hx hz hk
    (by simpa only [u, v, P, Q, R, pow_add] using huv)
    (by simpa only [u, w, P, Q, R, pow_add] using huw)
  obtain ⟨hu, hv, hw, hrel, hU, hV, hW⟩ := actual_source_chains x y z hx hy hz2
  change 1 ≤ u ∧ u < N at hu
  change 1 ≤ v ∧ v < N at hv
  change 1 ≤ w ∧ w < N at hw
  change R * u = N + v ∧ Q * v = N + w ∧ P * w = N + u at hrel
  change ∀ e < z, f e = if e + 1 < z then (2 : ℤ) ^ e * u else -(N - v) / 2 at hU
  change ∀ e < y, f (z + e) = if e + 1 < y then (2 : ℤ) ^ e * v else -(N - w) / 2 at hV
  change ∀ e < x, f (z + y + e) = if e + 1 < x then (2 : ℤ) ^ e * w else -(N - u) / 2 at hW
  obtain ⟨hN1, hNe, hNC⟩ := modulus_half (x + y + z) (by omega)
  change N = 2 * C + 1 at hNC
  change N % 2 = 1 at hNe
  have hPe : P % 2 = 0 := by
    dsimp [P]
    rw [show x = (x - 1) + 1 by omega, pow_succ, Int.mul_emod]
    norm_num
  have hQe : Q % 2 = 0 := by
    dsimp [Q]
    rw [show y = (y - 1) + 1 by omega, pow_succ, Int.mul_emod]
    norm_num
  have hRe : R % 2 = 0 := by
    dsimp [R]
    rw [show z = (z - 1) + 1 by omega, pow_succ, Int.mul_emod]
    norm_num
  have hue : u % 2 = 1 := by simp [u, Int.add_emod, Int.mul_emod, hPe, hQe]
  have hve : v % 2 = 1 := by simp [v, Int.add_emod, Int.mul_emod, hRe]
  have hwe : w % 2 = 1 := by simp [w, Int.add_emod, Int.mul_emod, hQe]
  let Av := (N - v) / 2
  let Aw := (N - w) / 2
  let Au := (N - u) / 2
  have hAv0 : 0 ≤ Av := by dsimp only [Av]; clear * - hv; omega
  have hAw0 : 0 ≤ Aw := by dsimp only [Aw]; clear * - hw; omega
  have hAuC : 0 ≤ Au ∧ Au ≤ C := by dsimp only [Au]; clear * - hu hNC; constructor <;> omega
  let r : ℤ := 2 ^ (z - 1)
  have hRr : R = 2 * r := by
    dsimp [R, r]
    conv_lhs => rw [show z = (z - 1) + 1 by omega, pow_succ]
    ring
  have hCF : C = r * u - (v + 1) / 2 := by
    have ht : 2 * (r * u) = N + v := by
      nlinarith only [hrel.1, congrArg (fun t : ℤ => t * u) hRr]
    have hd : 2 * ((v + 1) / 2) = v + 1 := by clear * - hve; omega
    nlinarith only [ht, hd, hNC]
  have hAF : Av = C - (v - 1) / 2 := by dsimp only [Av]; clear * - hNC hve; omega
  obtain ⟨hm0, hn0, hmn, hnquot, hmAv, hmC, hheight⟩ :=
    first_packet u v r C Av hu.1 huv hve hCF hAF hAv0
  let m := (C / u).toNat
  let n : ℕ := 2 ^ z * (2 ^ x + 1) / (2 * (1 + 2 ^ x + 2 ^ x * 2 ^ y))
  have hmCast : (m : ℤ) = C / u := Int.toNat_of_nonneg hm0
  have hnCast : (n : ℤ) = (v - 1) / (2 * u) := by
    dsimp only [n]
    rw [Int.natCast_div]
    push_cast
    congr 1; dsimp [u, v, P, Q, R]; ring
  have hnI : (n : ℤ) = r - 1 - C / u := by rw [hnCast]; exact hnquot.symm
  have hcompI : (m : ℤ) + n = r - 1 := by rw [hmCast, hnI]; ring
  have hcomp : m + n = 2 ^ (z - 1) - 1 := by
    have hrN : 1 ≤ (2 ^ (z - 1) : ℕ) := Nat.one_le_two_pow
    have hc : ((2 ^ (z - 1) - 1 : ℕ) : ℤ) = r - 1 := by
      rw [Nat.cast_sub hrN]
      simp [r]
    have he : ((m + n : ℕ) : ℤ) = ((2 ^ (z - 1) - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_add, hc]
      exact hcompI
    exact_mod_cast he
  have hFmass : Av ≤ (m : ℤ) * u ∧ (m : ℤ) * u ≤ C := by
    simpa only [hmCast] using And.intro hmAv hmC
  let h := (m : ℤ) * u - Av
  have hhE : h = v - ((n : ℤ) + 1) * u := by
    dsimp only [h]
    rw [hmCast, hnI]
    exact hheight
  have hh : 0 ≤ h ∧ h ≤ C := by dsimp only [h]; clear * - hFmass hAv0; omega
  have hP2 : P = 2 * (P / 2) := by clear * - hPe; omega
  have hCS : C = P / 2 * w - (u + 1) / 2 := by
    have hd : 2 * ((u + 1) / 2) = u + 1 := by clear * - hue; omega
    nlinarith only [hrel.2.2, hNC, hd, congrArg (fun t : ℤ => t * w) hP2]
  obtain ⟨c, dV, dW, hc, hdV, hdW, hq0, hE0, hED⟩ :=
    second_packet x y z hx hy hz2 hxz hyz huw
      (by rw [← hCS, ← hhE]; exact hh)
  change 0 ≤ (P / 2 * w - (u + 1) / 2) -
    (v - ((n : ℤ) + 1) * u) - ((c : ℤ) * u + dV * v + dW * w) at hE0
  change (P / 2 * w - (u + 1) / 2) -
    (v - ((n : ℤ) + 1) * u) - ((c : ℤ) * u + dV * v + dW * w) ≤
      (w - 1) / 2 at hED
  rw [← hCS, ← hhE] at hE0 hED
  have hqfactor : Q = 2 * (2 : ℤ) ^ (y - 1) := by
    dsimp only [Q]
    conv_lhs => rw [show y = (y - 1) + 1 by omega, pow_succ]
    ring
  have hpfactor : P = 2 * (2 : ℤ) ^ (x - 1) := by
    dsimp only [P]
    conv_lhs => rw [show x = (x - 1) + 1 by omega, pow_succ]
    ring
  have hdVN : dV < 2 ^ (y - 1) := by
    have he : Q / 2 = (2 : ℤ) ^ (y - 1) := by clear * - hqfactor; omega
    rw [he] at hdV
    exact_mod_cast hdV
  have hdWN : dW < 2 ^ (x - 1) := by
    have he : P / 2 = (2 : ℤ) ^ (x - 1) := by clear * - hpfactor; omega
    rw [he] at hdW
    exact_mod_cast hdW
  have hAwD : Aw = C - (w - 1) / 2 := by dsimp only [Aw]; clear * - hNC hwe; omega
  have hQmass : Aw ≤ (m : ℤ) * u - Av + (c : ℤ) * u + dV * v + dW * w ∧
      (m : ℤ) * u - Av + (c : ℤ) * u + dV * v + dW * w ≤ C := by
    dsimp only [h] at hE0 hED
    constructor <;> linarith only [hE0, hED, hAwD]
  have hUp (e : ℕ) (he : e < z - 1) : f e = (2 : ℤ) ^ e * u := by
    have hlt : e + 1 < z := by clear * - he; omega
    simpa only [ite_eq_left hlt] using hU e (by clear * - he; omega)
  have hVp (e : ℕ) (he : e < y - 1) : f (z + e) = (2 : ℤ) ^ e * v := by
    have hlt : e + 1 < y := by clear * - he; omega
    simpa only [ite_eq_left hlt] using hV e (by clear * - he; omega)
  have hWp (e : ℕ) (he : e < x - 1) : f (z + y + e) = (2 : ℤ) ^ e * w := by
    have hlt : e + 1 < x := by clear * - he; omega
    simpa only [ite_eq_left hlt] using hW e (by clear * - he; omega)
  have hAv : f (z - 1) = -Av := by
    have ht := hU (z - 1) (by clear * - hz; omega)
    rw [ite_eq_right (show ¬z - 1 + 1 < z by clear * - hz; omega)] at ht
    have he : -(N - v) / 2 = -Av := by dsimp only [Av]; clear * - hNe hve; omega
    exact ht.trans he
  have hAw : f (z + y - 1) = -Aw := by
    have ht := hV (y - 1) (by clear * - hy; omega)
    rw [ite_eq_right (show ¬y - 1 + 1 < y by clear * - hy; omega),
      show z + (y - 1) = z + y - 1 by clear * - hy; omega] at ht
    have he : -(N - w) / 2 = -Aw := by dsimp only [Aw]; clear * - hNe hwe; omega
    exact ht.trans he
  have hAu : f (x + y + z - 1) = -Au := by
    have ht := hW (x - 1) (by clear * - hx; omega)
    rw [ite_eq_right (show ¬x - 1 + 1 < x by clear * - hx; omega),
      show z + y + (x - 1) = x + y + z - 1 by clear * - hx; omega] at ht
    have he : -(N - u) / 2 = -Au := by dsimp only [Au]; clear * - hNe hue; omega
    exact ht.trans he
  have hpos (i : ℕ) (hi : i < x + y + z)
      (hav : i ≠ z - 1) (haw : i ≠ z + y - 1) (hau : i ≠ x + y + z - 1) :
      0 ≤ f i := by
    by_cases hiU : i < z - 1
    · rw [hUp i hiU]; positivity
    · by_cases hiV : i < z + y - 1
      · let e := i - z
        have he : i = z + e := by dsimp only [e]; clear * - hiU hav; omega
        rw [he, hVp e (by dsimp only [e]; clear * - hiV hiU hav; omega)]
        positivity
      · let e := i - (z + y)
        have he : i = z + y + e := by dsimp only [e]; clear * - hiV haw; omega
        rw [he, hWp e (by dsimp only [e]; clear * - hi hiV haw hau; omega)]
        positivity
  have htotal : ((List.range (x + y + z)).map f).sum = 0 := by
    have ht := source_zero (x + y + z) (1 + 2 ^ x + 2 ^ (x + y)) (by omega)
    simpa only [f, N, u, P, Q, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_mul, pow_add] using ht
  obtain ⟨word, hperm, hstrip⟩ := masked_schedule x y z m n c dV dW hx hy hz2
    f u v w Av Aw Au C hUp hVp hWp hAv hAw hAu hpos hAv0 hAw0 hAuC
    hcomp hc hdVN hdWN hFmass hQmass htotal
  exact ⟨word, hperm, hstrip, by rw [(hperm.map f).sum_eq]; exact htotal⟩


/-- A cyclic permutation transports the complete physical schedule. -/
private theorem transport_order (k t s : ℕ) (f : ℕ → ℤ) (hk : 3 ≤ k)
    (hf : ∀ i, centered (modulus k) ((2 : ℤ) ^ (i + s) * t) = f i)
    (l : List ℕ) (hl : l.Perm (List.range k))
    (hs : InStrip f ((2 : ℤ) ^ (k - 1) - 1) 0 l)
    (ht : (l.map f).sum = 0) :
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      (∀ n : ℕ, ((word.take n).map (actualSource k t)).sum ∈
        Set.Icc (0 : ℤ) ((2 : ℤ) ^ (k - 1) - 1)) ∧
      (word.map (actualSource k t)).sum = 0 := by
  haveI : NeZero k := ⟨by omega⟩
  let σ : Equiv.Perm (Fin k) := Equiv.addRight (⟨s % k, Nat.mod_lt s (by omega)⟩ : Fin k)
  let g : ℕ → Fin k := fun i => σ ⟨i % k, Nat.mod_lt i (by omega)⟩
  have hg (i : ℕ) : actualSource k t (g i) = f i := by
    change centered (modulus k) ((2 : ℤ) ^ (g i).val * t) = f i
    have hv : (g i).val = (i + s) % k := by
      simp [g, σ, Fin.val_add, Nat.add_mod]
    rw [hv, centered_index_mod k t (i + s) hk, hf]
  have hbase : (List.range k).map (fun i => (⟨i % k, Nat.mod_lt i (by omega)⟩ : Fin k)) =
      List.finRange k := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by simpa using hi)
  have hperm : (l.map g).Perm (List.finRange k) := by
    apply (hl.map g).trans
    change ((List.range k).map (σ ∘ (fun i => (⟨i % k, Nat.mod_lt i (by omega)⟩ : Fin k)))).Perm _
    rw [← List.map_map, hbase]
    exact Equiv.Perm.map_finRange_perm σ
  refine ⟨l.map g, hperm, ?_, ?_⟩
  · intro n
    have hp := inStrip_prefix hs n
    simpa only [← List.map_take, List.map_map, Function.comp_def, hg, zero_add,
      Set.mem_Icc] using hp
  · simpa only [List.map_map, Function.comp_def, hg] using ht

/-- Minimum selection among all three actual rotations, including ties. -/
private theorem cyclic_order (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hk : 4 ≤ x + y + z) :
    ∃ word : List (Fin (x + y + z)), word.Perm (List.finRange (x + y + z)) ∧
      (∀ n : ℕ, ((word.take n).map
        (actualSource (x + y + z) (1 + 2 ^ x + 2 ^ (x + y)))).sum ∈
          Set.Icc (0 : ℤ) ((2 : ℤ) ^ (x + y + z - 1) - 1)) ∧
      (word.map (actualSource (x + y + z) (1 + 2 ^ x + 2 ^ (x + y)))).sum = 0 := by
  let u : ℤ := 1 + 2 ^ x + 2 ^ x * 2 ^ y
  let v : ℤ := 1 + 2 ^ z + 2 ^ z * 2 ^ x
  let w : ℤ := 1 + 2 ^ y + 2 ^ y * 2 ^ z
  have go (X Y Z s : ℕ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
      (hK : X + Y + Z = x + y + z)
      (hminV : (1 : ℤ) + 2 ^ X + 2 ^ X * 2 ^ Y ≤ 1 + 2 ^ Z + 2 ^ Z * 2 ^ X)
      (hminW : (1 : ℤ) + 2 ^ X + 2 ^ X * 2 ^ Y ≤ 1 + 2 ^ Y + 2 ^ Y * 2 ^ Z)
      (hrot : ∀ i, centered (modulus (x + y + z))
          ((2 : ℤ) ^ (i + s) * (1 + 2 ^ x + 2 ^ (x + y))) =
        centered (modulus (x + y + z))
          ((2 : ℤ) ^ i * (1 + 2 ^ X + 2 ^ X * 2 ^ Y))) :
      ∃ word : List (Fin (x + y + z)), word.Perm (List.finRange (x + y + z)) ∧
        (∀ n : ℕ, ((word.take n).map
          (actualSource (x + y + z) (1 + 2 ^ x + 2 ^ (x + y)))).sum ∈
            Set.Icc (0 : ℤ) ((2 : ℤ) ^ (x + y + z - 1) - 1)) ∧
        (word.map (actualSource (x + y + z) (1 + 2 ^ x + 2 ^ (x + y)))).sum = 0 := by
    have hn := normalized_order X Y Z hX hY hZ (by omega) hminV hminW
    rw [hK] at hn
    obtain ⟨l, hl, hs, ht⟩ := hn
    apply transport_order (x + y + z) (1 + 2 ^ x + 2 ^ (x + y)) s _ (by omega)
      (fun i => ?_) l hl hs ht
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using hrot i
  have hrotV (i : ℕ) := source_rotation x y z i hx hy hz
  have hrotW (i : ℕ) :
      centered (modulus (x + y + z))
        ((2 : ℤ) ^ (i + (z + y)) * (1 + 2 ^ x + 2 ^ (x + y))) =
      centered (modulus (x + y + z))
        ((2 : ℤ) ^ i * (1 + 2 ^ y + 2 ^ (y + z))) := by
    rw [show i + (z + y) = (i + y) + z by omega, hrotV (i + y)]
    simpa only [show z + x + y = x + y + z by omega] using
      source_rotation z x y i hz hx hy
  by_cases huv : u ≤ v
  · by_cases huw : u ≤ w
    · exact go x y z 0 hx hy hz rfl huv huw (fun i => by simp [pow_add])
    · exact go y z x (z + y) hy hz hx (by omega) (by dsimp [u, w] at *; omega)
        (by dsimp [v, w] at *; omega)
        (fun i => by simpa only [pow_add] using hrotW i)
  · by_cases hvw : v ≤ w
    · exact go z x y z hz hx hy (by omega) hvw (by dsimp [u, v] at *; omega)
        (fun i => by simpa only [pow_add] using hrotV i)
    · exact go y z x (z + y) hy hz hx (by omega) (by dsimp [u, w] at *; omega)
        (by dsimp [v, w] at *; omega)
        (fun i => by simpa only [pow_add] using hrotW i)

/-- Every three-bit source admits an exact physical-label order in the half-modulus strip. -/
public theorem three_bit_source_order (k a b : ℕ)
    (ha : 0 < a) (hab : a < b) (hbk : b < k) :
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      (∀ n : ℕ, ((word.take n).map
        (SourceWidth.actualSource k (1 + 2 ^ a + 2 ^ b))).sum ∈
          Set.Icc (0 : ℤ) ((2 : ℤ) ^ (k - 1) - 1)) ∧
      (word.map (SourceWidth.actualSource k (1 + 2 ^ a + 2 ^ b))).sum = 0 := by
  have hk : 3 ≤ k := by omega
  by_cases hk3 : k = 3
  · subst k
    have ha1 : a = 1 := by omega
    have hb2 : b = 2 := by omega
    subst a
    subst b
    have hz (i : Fin 3) : actualSource 3 (1 + 2 ^ 1 + 2 ^ 2) i = 0 := by
      fin_cases i <;> norm_num [actualSource, centered, modulus]
    have hf : actualSource 3 7 = (fun _ => 0) := funext hz
    have hsum (l : List (Fin 3)) : (l.map (actualSource 3 7)).sum = 0 := by
      simp [hf]
    refine ⟨List.finRange 3, List.Perm.refl _, ?_, ?_⟩
    · intro n
      change (((List.finRange 3).take n).map (actualSource 3 7)).sum ∈
        Set.Icc (0 : ℤ) 3
      rw [hsum]
      norm_num
    · exact hsum _
  · have hs : a + (b - a) + (k - b) = k := by omega
    have habs : a + (b - a) = b := by omega
    have ho := cyclic_order a (b - a) (k - b) ha (by omega) (by omega) (by omega)
    rw [hs] at ho
    simpa only [habs] using ho

#print axioms three_bit_source_order

end D5.S3.Combinatorics.Circle.ThreeBitSource
