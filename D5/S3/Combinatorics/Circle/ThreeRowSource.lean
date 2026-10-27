/- GID: D5/S3/Combinatorics/Circle/ThreeRowSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeRowSource
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: An attained unused row mask retires the last two large occurrences. -/
module
public import D5.S3.Combinatorics.Circle.ThreeRowParameters
import all D5.S3.Combinatorics.Circle.ThreeRowScheduler
public import D5.S3.Combinatorics.Circle.SourceWidth
import D5.S3.Combinatorics.Circle.ThreeParentFamily
import D5.S3.Combinatorics.Circle.TwoRunSource
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
namespace D5.S3.Combinatorics.Circle.ThreeRowSource
open SourceWidth
open scoped BigOperators
/- Explicit source correspondence for the three-row family. This is an explicit
function, not a theorem, axiom, source-order assumption, or acceptance marker.
Offsets are exhaustive on Fin(baseLength J m).
-/
def rowValue (J m : ℕ) (i : Fin (baseLength J m)) : ℤ :=
  let L := rowLength J m
  let r := r J
  let q := q J m
  if i.val = 0 then M r q
  else if i.val ≤ L then -(2 ^ (i.val - 1) * a r q)
  else if i.val = L + 1 then -D r q
  else if i.val ≤ L + J + 1 then 2 ^ (i.val - (L + 2)) * b r q
  else if i.val = L + J + 2 then V1 r q
  else if i.val < 2 * L + J + 2 then -(2 ^ (i.val - (L + J + 3)) * z1 r q)
  else if i.val = 2 * L + J + 2 then -W1 r q
  else if i.val = 2 * L + J + 3 then V2 r q
  else if i.val < 3 * L + J + 3 then -(2 ^ (i.val - (2 * L + J + 4)) * z2 r q)
  else -W2 r q

/- Exact scalar range facts for the row realization. Doubling the W-bounds
avoids division in the polynomial certificates. -/
private theorem row_scalar_bounds (r q : ℤ) (hr : 4 ≤ r) (hq : 2 * r ^ 2 ≤ q)
    (hq2 : 2 * (q / 2) = q) :
    0 < a r q ∧ 0 < b r q ∧ 0 < z1 r q ∧ 0 < z2 r q ∧
    Q r q < M r q ∧ M r q < C r q ∧
    Q r q < D r q ∧ D r q < C r q ∧
    Q r q < V1 r q ∧ V1 r q < C r q ∧
    Q r q < V2 r q ∧ V2 r q < C r q ∧
    Q r q < W1 r q ∧ W1 r q < C r q ∧
    Q r q < W2 r q ∧ W2 r q < C r q := by
  obtain ⟨x, hx, hrx⟩ : ∃ x : ℤ, 0 ≤ x ∧ r = x + 4 :=
    ⟨r - 4, by omega, by ring⟩
  obtain ⟨y, hy, hqy⟩ : ∃ y : ℤ, 0 ≤ y ∧ q = y + 2 * (x + 4) ^ 2 := by
    refine ⟨q - 2 * r ^ 2, by omega, ?_⟩
    rw [← hrx]; ring
  have hp :
      0 < a r q ∧ 0 < b r q ∧ 0 < z1 r q ∧ 0 < z2 r q ∧
      0 < M r q - Q r q ∧ 0 < C r q - M r q ∧
      0 < D r q - Q r q ∧ 0 < C r q - D r q ∧
      0 < V1 r q - Q r q ∧ 0 < C r q - V1 r q ∧
      0 < V2 r q - Q r q ∧ 0 < C r q - V2 r q ∧
      0 < q * z1 r q - 2 * Q r q ∧ 0 < 2 * C r q - q * z1 r q ∧
      0 < q * z2 r q - 2 * Q r q ∧ 0 < 2 * C r q - q * z2 r q := by
    repeat' constructor
    all_goals rw [hrx, hqy]
    all_goals dsimp [a, b, z1, z2, M, D, V1, V2, Q, C, H, delta, e2]
    all_goals ring_nf
    all_goals positivity
  have hw1 : 2 * W1 r q = q * z1 r q := by
    dsimp [W1]
    calc 2 * (q / 2 * z1 r q) = (2 * (q / 2)) * z1 r q := by ring
         _ = _ := by rw [hq2]
  have hw2 : 2 * W2 r q = q * z2 r q := by
    dsimp [W2]
    calc 2 * (q / 2 * z2 r q) = (2 * (q / 2)) * z2 r q := by ring
         _ = _ := by rw [hq2]
  rcases hp with ⟨ha, hb, hz1, hz2, hM0, hM1, hD0, hD1,
    hV10, hV11, hV20, hV21, hW10, hW11, hW20, hW21⟩
  exact ⟨ha, hb, hz1, hz2, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/- A whole dyadic run is identified by centered uniqueness, without pretending
that a numerical value is a physical occurrence. Its start index remains fixed.
-/
private theorem centered_ladder (k t start len : ℕ) (hk : 0 < k) (seed : ℤ)
    (hseed : centered (modulus k) ((2 : ℤ) ^ start * t) = seed)
    (hcap : (2 : ℤ) ^ len * |seed| ≤ modulus k / 2) :
    ∀ i : ℕ, i ≤ len →
      centered (modulus k) ((2 : ℤ) ^ (start + i) * t) = 2 ^ i * seed := by
  obtain ⟨hN, hodd⟩ := TwoRunSource.modulus_positive_odd k hk
  intro i hi
  have hpow : (2 : ℤ) ^ i ≤ 2 ^ len :=
    pow_le_pow_right₀ (by norm_num) hi
  have habs : |(2 : ℤ) ^ i * seed| ≤ modulus k / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℤ) ^ i)]
    exact le_trans (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)) hcap
  apply centered_unique hN hodd (centered_bounds hN hodd _)
    (abs_le.mp habs)
  rw [centered_mod]
  have hs : seed % modulus k = ((2 : ℤ) ^ start * t) % modulus k := by
    rw [← hseed, centered_mod]
  rw [pow_add]
  calc
    ((2 : ℤ) ^ start * 2 ^ i * t) % modulus k =
        (2 ^ i * ((2 : ℤ) ^ start * t)) % modulus k := by ring_nf
    _ = (2 ^ i * (((2 : ℤ) ^ start * t) % modulus k)) % modulus k := by
      rw [Int.mul_emod, Int.mul_emod]
      simp only [Int.emod_emod]
      simpa only [Int.emod_emod] using
        (Int.mul_emod (2 ^ i) ((2 ^ start * t) % modulus k) (modulus k)).symm
    _ = (2 ^ i * (seed % modulus k)) % modulus k := by rw [hs]
    _ = (2 ^ i * seed) % modulus k := by
      rw [Int.mul_emod, Int.mul_emod]
      simp only [Int.emod_emod]
      exact (Int.mul_emod (2 ^ i) seed (modulus k)).symm

/- Exact original-source realization. The scalar certificates, ladder bounds,
index arithmetic and all nine row boundaries are checked below.
-/
private theorem proposed_source_values (J m : ℕ) (hJ : 2 ≤ J) (hm : 1 ≤ m) :
    ∀ i : Fin (baseLength J m),
      actualSource (baseLength J m) (M (r J) (q J m)).toNat i = rowValue J m i := by
  let L := rowLength J m
  let k := baseLength J m
  let r := r J
  let q := q J m
  let t := (M r q).toNat
  let v : ℕ → ℤ := fun i => centered (modulus k) ((2 : ℤ) ^ i * t)
  obtain ⟨hr, hq, hr2, hq2, hL, _, _⟩ := parameter_bounds J m hJ hm
  change 1 ≤ L at hL
  have hk : 0 < k := by dsimp [k, baseLength]; omega
  obtain ⟨hN, hodd⟩ := TwoRunSource.modulus_positive_odd k hk
  have hmod : modulus k = N r q := modulus_identity J m
  have hhalf : modulus k / 2 = C r q := by
    rw [hmod]
    unfold N C
    have hr0 : 0 ≤ r := by omega
    have hq0 : 0 ≤ q := by nlinarith [hq, sq_nonneg r]
    have hnonneg : 0 ≤ 16 * r * q ^ 3 := by positivity
    have hde := Int.emod_add_mul_ediv (16 * r * q ^ 3 - 1) 2
    have heq : 16 * r * q ^ 3 - 1 = 2 * (8 * r * q ^ 3) - 1 := by ring
    rw [heq] at hde ⊢
    have hrem : (2 * (8 * r * q ^ 3) - 1) % 2 = 1 := by omega
    omega
  obtain ⟨ha, hb, hz1, hz2, hM0, hM1, hD0, hD1,
    hV10, hV11, hV20, hV21, hW10, hW11, hW20, hW21⟩ :=
      row_scalar_bounds r q hr hq hq2
  have hQ : 0 < Q r q := by
    unfold Q
    have hrp : 0 < r := by omega
    have hqp : 0 < q := by omega
    positivity
  have ht : (t : ℤ) = M r q := Int.toNat_of_nonneg (by omega)
  have hpowJ : (2 : ℤ) ^ J = r := rfl
  have hpowL : (2 : ℤ) ^ L = q := rfl
  have hpowL1 : (2 : ℤ) ^ (L - 1) = q / 2 := by
    have he : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hL]
    rw [hpowL] at he
    have hde := Int.emod_add_mul_ediv q 2
    have hrem : q % 2 = 0 := by omega
    omega
  have hident :
      N r q = 2 * M r q + a r q ∧ N r q = 2 * D r q + b r q ∧
      N r q = 2 * V1 r q + z1 r q ∧ N r q = 2 * W1 r q + V2 r q ∧
      N r q = 2 * V2 r q + z2 r q ∧ N r q = 2 * W2 r q + M r q := by
    have hw1 : 2 * W1 r q = q * z1 r q := by
      dsimp [W1]; linear_combination (z1 r q) * hq2
    have hw2 : 2 * W2 r q = q * z2 r q := by
      dsimp [W2]; linear_combination (z2 r q) * hq2
    repeat' constructor
    all_goals first
      | (rw [hw1]; simp [N, V2, M, z1, a, delta, e2, H]; ring)
      | (rw [hw2]; simp [N, M, z2, a, e2, H]; ring)
      | (simp [N, M, D, V1, V2, a, b, z1, z2, W1, W2, delta, e2, H]; ring)
  have hstep (i : ℕ) : v (i + 1) = doubleStep (modulus k) (v i) := by
    dsimp [v]
    have he : (2 : ℤ) ^ (i + 1) * t = 2 * (2 ^ i * (t : ℤ)) := by
      rw [pow_succ]; ring
    rw [he, centered_double hN hodd]
  have positive_cut (x : ℤ) (hx : Q r q < x) :
      doubleStep (modulus k) x = 2 * x - N r q := by
    have hc : modulus k < 4 * x := by
      rw [hmod]
      unfold N Q at *
      nlinarith [hx]
    have hn : ¬ 4 * x < -modulus k := by omega
    rw [doubleStep, if_pos hc]
    rw [hmod]
  have negative_cut (x : ℤ) (hx : Q r q < x) :
      doubleStep (modulus k) (-x) = -2 * x + N r q := by
    have hpos : ¬ modulus k < 4 * (-x) := by omega
    have hc : 4 * (-x) < -modulus k := by
      rw [hmod]
      unfold N Q at *
      nlinarith [hx]
    rw [doubleStep, if_neg hpos, if_pos hc]
    rw [hmod]
    ring_nf
  have h0 : v 0 = M r q := by
    apply centered_unique hN hodd (centered_bounds hN hodd _)
    · rw [hhalf]; constructor <;> omega
    · simp [v, centered_mod, ht]
  have h1 : v 1 = -a r q := by
    rw [show 1 = 0 + 1 by omega, hstep, h0, positive_cut _ hM0]
    linear_combination -hident.1
  have oldRun (i : ℕ) (hi : i ≤ L) : v (1 + i) = -(2 ^ i * a r q) := by
    have he := centered_ladder k t 1 L hk (-a r q) h1
      (by rw [hpowL, abs_neg, abs_of_pos ha, hhalf]; change D r q ≤ C r q; omega) i hi
    simpa [v] using he
  have hD : v (L + 1) = -D r q := by
    simpa [hpowL, D, Nat.add_comm, v] using oldRun L (le_refl _)
  have hB : v (L + 2) = b r q := by
    rw [show L + 2 = (L + 1) + 1 by omega, hstep, hD, negative_cut _ hD0]
    linear_combination hident.2.1
  have posRun (i : ℕ) (hi : i ≤ J) : v (L + 2 + i) = 2 ^ i * b r q := by
    exact centered_ladder k t (L + 2) J hk (b r q) hB
      (by rw [hpowJ, abs_of_pos hb, hhalf]; change V1 r q ≤ C r q; omega) i hi
  have hV1 : v (L + J + 2) = V1 r q := by
    simpa [hpowJ, V1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using posRun J (le_refl _)
  have hZ1 : v (L + J + 3) = -z1 r q := by
    rw [show L + J + 3 = (L + J + 2) + 1 by omega, hstep, hV1, positive_cut _ hV10]
    linear_combination -hident.2.2.1
  have nextRun (i : ℕ) (hi : i ≤ L - 1) :
      v (L + J + 3 + i) = -(2 ^ i * z1 r q) := by
    have he := centered_ladder k t (L + J + 3) (L - 1) hk (-z1 r q) hZ1
      (by rw [hpowL1, abs_neg, abs_of_pos hz1, hhalf]; change W1 r q ≤ C r q; omega) i hi
    simpa [v] using he
  have hW1 : v (2 * L + J + 2) = -W1 r q := by
    have hi : L + J + 3 + (L - 1) = 2 * L + J + 2 := by omega
    simpa [hi, hpowL1, W1] using nextRun (L - 1) (le_refl _)
  have hV2 : v (2 * L + J + 3) = V2 r q := by
    rw [show 2 * L + J + 3 = (2 * L + J + 2) + 1 by omega,
      hstep, hW1, negative_cut _ hW10]
    linear_combination hident.2.2.2.1
  have hZ2 : v (2 * L + J + 4) = -z2 r q := by
    rw [show 2 * L + J + 4 = (2 * L + J + 3) + 1 by omega,
      hstep, hV2, positive_cut _ hV20]
    linear_combination -hident.2.2.2.2.1
  have thirdRun (i : ℕ) (hi : i ≤ L - 1) :
      v (2 * L + J + 4 + i) = -(2 ^ i * z2 r q) := by
    have he := centered_ladder k t (2 * L + J + 4) (L - 1) hk (-z2 r q) hZ2
      (by rw [hpowL1, abs_neg, abs_of_pos hz2, hhalf]; change W2 r q ≤ C r q; omega) i hi
    simpa [v] using he
  have hW2 : v (3 * L + J + 3) = -W2 r q := by
    have hi : 2 * L + J + 4 + (L - 1) = 3 * L + J + 3 := by omega
    simpa [hi, hpowL1, W2] using thirdRun (L - 1) (le_refl _)
  -- The seam is also explicit: the successor of -W2 is M.
  have hseam : v k = M r q := by
    change v (3 * L + J + 4) = _
    rw [show 3 * L + J + 4 = (3 * L + J + 3) + 1 by omega,
      hstep, hW2, negative_cut _ hW20]
    linear_combination hident.2.2.2.2.2
  intro i
  change v i.val = rowValue J m i
  unfold rowValue
  change v i.val = if i.val = 0 then M r q else _
  split_ifs with h0i hAi hDi hBi hV1i hZ1i hW1i hV2i hZ2i
  · simpa [h0i] using h0
  · have hi : i.val = 1 + (i.val - 1) := by omega
    simpa [← hi] using oldRun (i.val - 1) (by omega)
  · simpa [hDi] using hD
  · have hi : i.val = L + 2 + (i.val - (L + 2)) := by omega
    simpa [← hi] using posRun (i.val - (L + 2)) (by omega)
  · simpa [hV1i] using hV1
  · have hi : i.val = L + J + 3 + (i.val - (L + J + 3)) := by omega
    simpa [← hi] using nextRun (i.val - (L + J + 3)) (by omega)
  · simpa [hW1i] using hW1
  · simpa [hV2i] using hV2
  · have hi : i.val = 2 * L + J + 4 + (i.val - (2 * L + J + 4)) := by omega
    simpa [← hi] using thirdRun (i.val - (2 * L + J + 4)) (by omega)
  · have hi : i.val = 3 * L + J + 3 := by
      have := i.isLt
      change i.val < 3 * L + J + 4 at this
      omega
    simpa [hi] using hW2

private theorem orbit_mod (k t n : ℕ) (hk : 0 < k) :
    centered (modulus k) ((2 : ℤ) ^ n * t) =
      centered (modulus k) ((2 : ℤ) ^ (n % k) * t) := by
  apply SourceWidth.centered_congr
  have hpow : (2 : ℤ) ^ k % modulus k = 1 % modulus k := by
    rw [show (2 : ℤ) ^ k = modulus k + 1 by unfold modulus; ring,
      add_comm (modulus k) 1, Int.add_emod_right]
  have he : n = n % k + k * (n / k) := (Nat.mod_add_div n k).symm
  conv_lhs => rw [he, pow_add, pow_mul]
  have hN := TwoRunSource.modulus_positive_odd k hk
  have hkmod : (2 : ℤ) ^ k ≡ 1 [ZMOD modulus k] := by
    change (2 : ℤ) ^ k % modulus k = 1 % modulus k
    exact hpow
  have hp := hkmod.pow (n / k)
  change ((2 : ℤ) ^ k) ^ (n / k) % modulus k = (1 : ℤ) ^ (n / k) % modulus k at hp
  have hp1 : ((2 : ℤ) ^ k) ^ (n / k) % modulus k = 1 % modulus k := by
    simpa only [one_pow] using hp
  have hmul_mod (a b c : ℤ) (h : b % modulus k = c % modulus k) :
      (a * b) % modulus k = (a * c) % modulus k := by
    calc
      (a * b) % modulus k = (a % modulus k * (b % modulus k)) % modulus k := Int.mul_emod _ _ _
      _ = (a % modulus k * (c % modulus k)) % modulus k := by rw [h]
      _ = (a * c) % modulus k := (Int.mul_emod _ _ _).symm
  have hstep := hmul_mod ((2 : ℤ) ^ (n % k))
    (((2 : ℤ) ^ k) ^ (n / k)) 1 hp1
  have hstep' := hmul_mod (t : ℤ)
    ((2 : ℤ) ^ (n % k) * ((2 : ℤ) ^ k) ^ (n / k))
    ((2 : ℤ) ^ (n % k) * 1) hstep
  simpa only [mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hstep'

/- The exact natural geometric multiplier is the requested quotient. -/
def multiplier (b d : ℕ) : ℕ := ∑ j ∈ Finset.range d, 2 ^ (j * b)

private theorem multiplier_identity (b d : ℕ) :
    (multiplier b d : ℤ) * modulus b = modulus (d * b) := by
  induction d with
  | zero => simp [multiplier, modulus]
  | succ d ih =>
    have hs : (multiplier b (d + 1) : ℤ) = multiplier b d + (2 : ℤ) ^ (d * b) := by
      simp [multiplier, Finset.sum_range_succ, Nat.cast_sum, Nat.cast_pow]
    rw [hs, show (d + 1) * b = d * b + b by simp [Nat.succ_mul]]
    unfold modulus at ih ⊢
    rw [pow_add]
    nlinarith [ih]

private theorem multiplier_quotient (b d : ℕ) (hb : 0 < b) :
    multiplier b d = (2 ^ (d * b) - 1) / (2 ^ b - 1) := by
  have hbase : 0 < 2 ^ b - 1 := by
    have := Nat.one_lt_two_pow (ne_of_gt hb)
    omega
  have hnat : multiplier b d * (2 ^ b - 1) = 2 ^ (d * b) - 1 := by
    have hi := multiplier_identity b d
    have h1 : 1 ≤ (2 : ℕ) ^ b := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 : ℕ) ^ (d * b) := Nat.one_le_two_pow
    unfold modulus at hi
    exact_mod_cast hi
  rw [← hnat, Nat.mul_div_cancel _ hbase]

private theorem multiplier_positive (b d : ℕ) (hd : 1 ≤ d) :
    1 ≤ multiplier b d := by
  have h0 : 0 ∈ Finset.range d := by simp; omega
  have hs := Finset.single_le_sum (fun j _ => Nat.zero_le (2 ^ (j * b))) h0
  simpa [multiplier] using hs

private theorem centered_scale (N0 N lam x : ℤ)
    (h0 : 0 < N0) (hodd0 : N0 % 2 = 1)
    (hN : 0 < N) (hodd : N % 2 = 1) (hlam : 1 ≤ lam) (he : N = lam * N0) :
    centered N (lam * x) = lam * centered N0 x := by
  have hhalf0 := Int.emod_add_mul_ediv N0 2
  have hhalf := Int.emod_add_mul_ediv N 2
  have hcap : lam * (N0 / 2) ≤ N / 2 := by nlinarith
  have hc := centered_bounds h0 hodd0 x
  have hlo := mul_le_mul_of_nonneg_left hc.1 (by omega : 0 ≤ lam)
  have hhi := mul_le_mul_of_nonneg_left hc.2 (by omega : 0 ≤ lam)
  apply centered_unique hN hodd (centered_bounds hN hodd _)
    (by constructor <;> nlinarith)
  rw [centered_mod]
  have hd := (Int.modEq_iff_dvd).mp (centered_mod N0 x).symm
  obtain ⟨z, hz⟩ := hd
  apply (Int.modEq_iff_dvd).mpr
  refine ⟨z, ?_⟩
  rw [he]
  linear_combination lam * hz

private theorem repeated_source (b d t : ℕ) (hb : 0 < b) (hd : 1 ≤ d)
    (i : Fin (d * b)) :
    actualSource (d * b) ((multiplier b d * t) % (2 ^ (d * b) - 1)) i =
      (multiplier b d : ℤ) * actualSource b t ⟨i.val % b, Nat.mod_lt _ hb⟩ := by
  have hk : 0 < d * b := Nat.mul_pos (by omega) hb
  obtain ⟨hN, hodd⟩ := TwoRunSource.modulus_positive_odd (d * b) hk
  obtain ⟨h0, hodd0⟩ := TwoRunSource.modulus_positive_odd b hb
  have hlam : (1 : ℤ) ≤ multiplier b d := by exact_mod_cast multiplier_positive b d hd
  have hparam : centered (modulus (d * b))
      ((2 : ℤ) ^ i.val * (((multiplier b d * t) % (2 ^ (d * b) - 1) : ℕ) : ℤ)) =
      centered (modulus (d * b)) ((multiplier b d : ℤ) * ((2 : ℤ) ^ i.val * t)) := by
    apply SourceWidth.centered_congr
    change ((2 : ℤ) ^ i.val * (((multiplier b d * t) % (2 ^ (d * b) - 1) : ℕ) : ℤ)) %
      modulus (d * b) =
      ((multiplier b d : ℤ) * ((2 : ℤ) ^ i.val * t)) % modulus (d * b)
    have hnat :
        (((multiplier b d * t) % (2 ^ (d * b) - 1) : ℕ) : ℤ) ≡
          (multiplier b d : ℤ) * t [ZMOD modulus (d * b)] := by
      change (((multiplier b d * t) % (2 ^ (d * b) - 1) : ℕ) : ℤ) %
          modulus (d * b) = ((multiplier b d : ℤ) * t) % modulus (d * b)
      change (((multiplier b d * t) % (2 ^ (d * b) - 1) : ℕ) : ℤ) %
          ((2 : ℤ) ^ (d * b) - 1) = ((multiplier b d : ℤ) * t) %
            ((2 : ℤ) ^ (d * b) - 1)
      have hmod : ((2 ^ (d * b) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (d * b) - 1 := by
        rw [Nat.cast_sub (by
          have hp : 0 < (2 : ℕ) ^ (d * b) := pow_pos (by decide) _
          omega)]
        norm_num
      rw [Int.natCast_mod]
      rw [hmod]
      simp only [Int.emod_emod]
      simp only [Int.natCast_mul]
    have hm := (Int.ModEq.rfl : (2 : ℤ) ^ i.val ≡ (2 : ℤ) ^ i.val
      [ZMOD modulus (d * b)]).mul hnat
    simpa [mul_assoc, mul_left_comm, mul_comm] using hm.eq
  unfold actualSource
  rw [hparam, centered_scale (modulus b) (modulus (d * b)) (multiplier b d)
    ((2 : ℤ) ^ i.val * t) h0 hodd0 hN hodd hlam (multiplier_identity b d).symm,
    orbit_mod b t i.val hb]

private theorem scale_strip {α β : Type*} (f : α → ℤ) (g : β → ℤ)
    (θ : α → β) (lam B B' h : ℤ) (hlam : 0 ≤ lam) (hB : lam * B ≤ B')
    (word : List α) (hval : ∀ x ∈ word, g (θ x) = lam * f x)
    (hs : InStrip f B h word) : InStrip g B' (lam * h) (word.map θ) := by
  induction word generalizing h with
  | nil =>
    simp only [List.map_nil, InStrip] at *
    constructor <;> nlinarith
  | cons x xs ih =>
    have hx := hval x (by simp)
    simp only [List.map_cons, InStrip] at *
    refine ⟨by nlinarith [hs.1], by nlinarith [hs.2.1], ?_⟩
    have ht := ih (h + f x) (fun y hy => hval y (by simp [hy])) hs.2.2
    convert ht using 1 <;> rw [hx] <;> ring

private theorem scaled_sum {α β : Type*} (f : α → ℤ) (g : β → ℤ)
    (θ : α → β) (lam : ℤ) (word : List α)
    (hval : ∀ x ∈ word, g (θ x) = lam * f x) :
    ((word.map θ).map g).sum = lam * (word.map f).sum := by
  induction word with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hval x (by simp), ih (fun y hy => hval y (by simp [hy]))]
    ring

/- Product buckets prove exact physical consumption, including ties and
nonunits. No least numerical period or distinct-values premise is needed.
This private helper is conditional on the base word, whose construction is
the missing actual source use-site of schedule_rows.
-/
private theorem repeated_word (b d t : ℕ) (hb : 0 < b) (hd : 1 ≤ d)
    (word : List (Fin b)) (hw : word.Perm (List.finRange b))
    (hs : InStrip (actualSource b t) (((2 : ℤ) ^ b - 2) / 2) 0 word)
    (hz : (word.map (actualSource b t)).sum = 0) :
    let k := d * b
    let t' := (multiplier b d * t) % (2 ^ k - 1)
    ∃ result : List (Fin k), result.Perm (List.finRange k) ∧
      InStrip (actualSource k t') (((2 : ℤ) ^ k - 2) / 2) 0 result ∧
      (result.map (actualSource k t')).sum = 0 := by
  classical
  dsimp only
  let k := d * b
  let t' := (multiplier b d * t) % (2 ^ k - 1)
  let lam : ℤ := multiplier b d
  let B : ℤ := ((2 : ℤ) ^ b - 2) / 2
  let B' : ℤ := ((2 : ℤ) ^ k - 2) / 2
  let θ : Fin d × Fin b ≃ Fin k := finProdFinEquiv
  let labels := fun j : Fin d => (List.finRange b).map (fun i => θ (j, i))
  let words := fun j : Fin d => word.map (fun i => θ (j, i))
  have hphysical (j : Fin d) (i : Fin b) :
      actualSource k t' (θ (j, i)) = lam * actualSource b t i := by
    have ht := repeated_source b d t hb hd (θ (j, i))
    have hv : (θ (j, i)).val = i.val + b * j.val := rfl
    have hi : (⟨(θ (j, i)).val % b, Nat.mod_lt _ hb⟩ : Fin b) = i := by
      apply Fin.ext
      simp [hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
    simpa only [lam, hi] using ht
  have hlam : 1 ≤ lam := by
    dsimp [lam]
    exact_mod_cast multiplier_positive b d hd
  have hcap : lam * B ≤ B' := by
    have h0 := TwoRunSource.modulus_positive_odd b hb
    have hfull := TwoRunSource.modulus_positive_odd k (Nat.mul_pos (by omega) hb)
    have he := multiplier_identity b d
    have hhalf0 := Int.emod_add_mul_ediv (modulus b) 2
    have hhalf := Int.emod_add_mul_ediv (modulus k) 2
    have hB0 : 2 * B = modulus b - 1 := by
      dsimp [B]; unfold modulus at *; omega
    have hB1 : 2 * B' = modulus k - 1 := by
      dsimp [B']; unfold modulus at *; omega
    have hmul : lam * (2 * B) = lam * (modulus b - 1) := congrArg (fun v => lam * v) hB0
    change lam * modulus b = modulus k at he
    nlinarith
  have hB' : 0 ≤ B' := by
    have hp : (1 : ℤ) < 2 ^ k := by
      exact_mod_cast Nat.one_lt_two_pow (ne_of_gt (Nat.mul_pos (by omega) hb))
    dsimp [B']; omega
  have hp (j : Fin d) : (words j).Perm (labels j) := hw.map (fun i => θ (j, i))
  have hsum (j : Fin d) : ((words j).map (actualSource k t')).sum = 0 := by
    rw [scaled_sum _ _ (fun i => θ (j, i)) lam word (fun i _ => hphysical j i), hz]
    ring
  have hstrip (j : Fin d) : InStrip (actualSource k t') B' 0 (words j) := by
    simpa using scale_strip _ _ (fun i => θ (j, i)) lam B B' 0 (by omega) hcap word
      (fun i _ => hphysical j i) hs
  have hflatten : (List.finRange d).flatMap labels =
      ((List.finRange d).product (List.finRange b)).map θ := by
    simp only [labels, List.product, List.map_flatMap, List.map_map, Function.comp_def]
  have hcomplete : ((List.finRange d).flatMap labels).Perm (List.finRange k) := by
    rw [hflatten]
    apply (List.perm_ext_iff_of_nodup
      (((List.nodup_finRange d).product (List.nodup_finRange b)).map θ.injective)
      (List.nodup_finRange k)).mpr
    intro x
    simp only [List.mem_finRange, iff_true]
    exact List.mem_map.mpr ⟨θ.symm x,
      List.mem_product.mpr ⟨by simp, by simp⟩, θ.apply_symm_apply x⟩
  refine ⟨(List.finRange d).flatMap words,
    (List.Perm.flatMap_left _ (fun j _ => hp j)).trans hcomplete,
    TwoRunSource.concatenate_zero _ _ hB' _ words (fun j _ => hsum j) (fun j _ => hstrip j), ?_⟩
  induction (List.finRange d) with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_flatMap, List.flatMap_cons, List.map_append, List.sum_append]
    rw [hsum j]
    simpa only [List.map_flatMap, zero_add] using ih

private def physicalRotation (k : ℕ) (hk : 0 < k) (s : ℕ) : Fin k ≃ Fin k where
  toFun i := ⟨(i.val + s % k) % k, Nat.mod_lt _ hk⟩
  invFun i := ⟨(i.val + (k - s % k)) % k, Nat.mod_lt _ hk⟩
  left_inv i := by
    apply Fin.ext
    change (((i.val + s % k) % k + (k - s % k)) % k) = i.val
    have hs := Nat.mod_lt s hk
    calc
      _ = ((i.val + s % k) + (k - s % k)) % k := by
        simp only [Nat.add_mod, Nat.mod_mod]
      _ = (i.val + k) % k := by congr 1; omega
      _ = i.val := by simp [Nat.mod_eq_of_lt i.isLt]
  right_inv i := by
    apply Fin.ext
    change (((i.val + (k - s % k)) % k + s % k) % k) = i.val
    have hs := Nat.mod_lt s hk
    calc
      _ = ((i.val + (k - s % k)) + s % k) % k := by
        simp only [Nat.add_mod, Nat.mod_mod]
      _ = (i.val + k) % k := by congr 1; omega
      _ = i.val := by simp [Nat.mod_eq_of_lt i.isLt]

private theorem rotated_source (k t s : ℕ) (hk : 0 < k) (i : Fin k) :
    actualSource k ((2 ^ s * t) % (2 ^ k - 1)) i =
      actualSource k t (physicalRotation k hk s i) := by
  have hval : (physicalRotation k hk s i).val = (i.val + s) % k := by
    simp [physicalRotation, Nat.add_mod]
  unfold actualSource
  rw [hval]
  calc
    _ = centered (modulus k) ((2 : ℤ) ^ (i.val + s) * t) := by
      apply SourceWidth.centered_congr
      have hnat :
          (((2 ^ s * t) % (2 ^ k - 1) : ℕ) : ℤ) ≡
            (2 ^ s * t : ℕ) [ZMOD modulus k] := by
        change (((2 ^ s * t) % (2 ^ k - 1) : ℕ) : ℤ) % modulus k =
          ((2 ^ s * t : ℕ) : ℤ) % modulus k
        change (((2 ^ s * t) % (2 ^ k - 1) : ℕ) : ℤ) %
          ((2 : ℤ) ^ k - 1) = ((2 ^ s * t : ℕ) : ℤ) %
            ((2 : ℤ) ^ k - 1)
        have hmod : ((2 ^ k - 1 : ℕ) : ℤ) = (2 : ℤ) ^ k - 1 := by
          rw [Nat.cast_sub (by
            have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
            omega)]
          norm_num
        rw [Int.natCast_mod]
        rw [hmod]
        simp only [Int.emod_emod]
      have hm := (Int.ModEq.rfl : (2 : ℤ) ^ i.val ≡ (2 : ℤ) ^ i.val
        [ZMOD modulus k]).mul hnat
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hm.eq
    _ = _ := orbit_mod k t (i.val + s) hk

private theorem rotated_word (k t s : ℕ) (hk : 0 < k) (B : ℤ)
    (word : List (Fin k)) (hp : word.Perm (List.finRange k))
    (hs : InStrip (actualSource k t) B 0 word)
    (hz : (word.map (actualSource k t)).sum = 0) :
    ∃ result : List (Fin k), result.Perm (List.finRange k) ∧
      InStrip (actualSource k ((2 ^ s * t) % (2 ^ k - 1))) B 0 result ∧
      (result.map (actualSource k ((2 ^ s * t) % (2 ^ k - 1)))).sum = 0 := by
  let θ := physicalRotation k hk s
  let g := actualSource k ((2 ^ s * t) % (2 ^ k - 1))
  have hval (i : Fin k) : g (θ.symm i) = actualSource k t i := by
    change actualSource k ((2 ^ s * t) % (2 ^ k - 1)) (θ.symm i) =
      actualSource k t i
    rw [rotated_source k t s hk (θ.symm i)]
    exact congrArg (actualSource k t) (θ.apply_symm_apply i)
  have hcomplete : ((List.finRange k).map θ.symm).Perm (List.finRange k) := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange k).map θ.symm.injective) (List.nodup_finRange k)).mpr
    intro x
    simp only [List.mem_finRange, iff_true]
    exact List.mem_map.mpr ⟨θ x, by simp, θ.symm_apply_apply x⟩
  refine ⟨word.map θ.symm, (hp.map θ.symm).trans hcomplete, ?_, ?_⟩
  · simpa using scale_strip (actualSource k t) g θ.symm 1 B B 0
      (by norm_num) (by omega) word (fun i _ => by simp [hval]) hs
  · rw [scaled_sum (actualSource k t) g θ.symm 1 word (fun i _ => by simp [hval]), hz]
    ring

private theorem dyadic_small {α : Type*} (f : α → ℤ) (seed Q0 : ℤ)
    (xs : List α) (hs : 0 ≤ seed) (hd : Dyadic f seed xs)
    (hcap : (2 : ℤ) ^ xs.length * seed ≤ 2 * Q0 - 1) :
    ∀ x ∈ xs, |f x| ≤ Q0 - 1 := by
  induction xs generalizing seed with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hd.1, abs_of_nonneg hs]
      have hp : (1 : ℤ) ≤ 2 ^ xs.length := one_le_pow₀ (by norm_num)
      have hm := mul_le_mul_of_nonneg_right hp (by omega : 0 ≤ 2 * seed)
      simp only [List.length_cons, pow_succ] at hcap
      nlinarith
    · apply ih (2 * seed) (by omega) hd.2 ?_ y hy
      simpa only [List.length_cons, pow_succ, mul_assoc] using hcap

/- Complete base-order specialization for the original source.
-/
private theorem proposed_base_order (J m : ℕ) (hJ : 2 ≤ J) (hm : 1 ≤ m) :
    ∃ word : List (Fin (baseLength J m)), word.Perm (List.finRange (baseLength J m)) ∧
      InStrip (actualSource (baseLength J m) (M (r J) (q J m)).toNat)
        (((2 : ℤ) ^ baseLength J m - 2) / 2) 0 word ∧
      (word.map (actualSource (baseLength J m) (M (r J) (q J m)).toNat)).sum = 0 := by
  classical
  let L := rowLength J m
  let k := baseLength J m
  let r := r J
  let q := q J m
  let n : ℤ := firstCoefficient J m
  let f := actualSource k (M r q).toNat
  obtain ⟨hr, hq, hr2, hq2, hL, hnlo, hnhi⟩ := parameter_bounds J m hJ hm
  change 1 ≤ L at hL
  have hk : 0 < k := by dsimp [k, baseLength]; omega
  let p : Fin k := ⟨0, by dsimp [k, baseLength]; omega⟩
  let dlabel : Fin k := ⟨L + 1, by dsimp [k, baseLength]; omega⟩
  let top : Fin k := ⟨L + J + 1, by dsimp [k, baseLength]; omega⟩
  let parent1 : Fin k := ⟨L + J + 2, by dsimp [k, baseLength]; omega⟩
  let terminal1 : Fin k := ⟨2 * L + J + 2, by dsimp [k, baseLength]; omega⟩
  let parent2 : Fin k := ⟨2 * L + J + 3, by dsimp [k, baseLength]; omega⟩
  let terminal2 : Fin k := ⟨3 * L + J + 3, by dsimp [k, baseLength]; omega⟩
  let oldNeg := segment k 1 L (by dsimp [k, baseLength]; omega)
  let oldPosLower := segment k (L + 2) (J - 1) (by dsimp [k, baseLength]; omega)
  let nextNeg := segment k (L + J + 3) (L - 1) (by dsimp [k, baseLength]; omega)
  let thirdNeg := segment k (2 * L + J + 4) (L - 1) (by dsimp [k, baseLength]; omega)
  have hval := proposed_source_values J m hJ hm
  have hpowJ : (2 : ℤ) ^ (J - 1) = r / 2 := by
    have he : (2 : ℤ) ^ J = 2 * 2 ^ (J - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ J)]
    change r = _ at he
    omega
  have hpowL : (2 : ℤ) ^ L = q := rfl
  have hpowL1 : (2 : ℤ) ^ (L - 1) = q / 2 := by
    have he : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hL]
    rw [hpowL] at he
    have hde := Int.emod_add_mul_ediv q 2
    have hrem : q % 2 = 0 := by omega
    omega
  have hvalues : f p = M r q ∧ f dlabel = -D r q ∧ f top = (r / 2) * b r q ∧
      f parent1 = V1 r q ∧ f terminal1 = -W1 r q ∧
      f parent2 = V2 r q ∧ f terminal2 = -W2 r q := by
    have hidx : L + J - (1 + L) = J - 1 := by omega
    have hidx' : rowLength J m + J - (1 + rowLength J m) = J - 1 := by omega
    have hidxTop : L + J + 1 - (rowLength J m + 2) = J - 1 := by
      simp [L]
      omega
    repeat' constructor
    all_goals simp only [f, k, r, q]
    all_goals rw [hval]
    all_goals dsimp [p, dlabel, top, parent1, terminal1, parent2, terminal2, rowValue]
    all_goals split_ifs <;> first
      | omega
      | (simp [hidxTop, hpowJ, L, k, r, q])
  have hold : Dyadic (fun x => -f x) (a r q) oldNeg := by
    unfold oldNeg segment
    apply ThreeParentFamily.dyadic_ofFn
    intro i
    simp only [f, k, r, q]
    rw [hval]
    dsimp [rowValue]
    split_ifs <;> first | omega | (congr 1 <;> simp_all <;> omega)
  have hpos : Dyadic f (b r q) oldPosLower := by
    unfold oldPosLower segment
    apply ThreeParentFamily.dyadic_ofFn
    intro i
    simp only [f, k, r, q]
    rw [hval]
    dsimp [rowValue]
    split_ifs <;> first | omega | (congr 1 <;> simp_all <;> omega)
  have hnext : Dyadic (fun x => -f x) (z1 r q) nextNeg := by
    unfold nextNeg segment
    apply ThreeParentFamily.dyadic_ofFn
    intro i
    simp only [f, k, r, q]
    rw [hval]
    dsimp [rowValue]
    split_ifs <;> first | omega | (congr 1 <;> simp_all <;> omega)
  have hthird : Dyadic (fun x => -f x) (z2 r q) thirdNeg := by
    unfold thirdNeg segment
    apply ThreeParentFamily.dyadic_ofFn
    intro i
    simp only [f, k, r, q]
    rw [hval]
    dsimp [rowValue]
    split_ifs <;> first | omega | (congr 1 <;> simp_all <;> omega)
  obtain ⟨ha, hb, hz1, hz2, hM0, hM1, hD0, hD1,
    hV10, hV11, hV20, hV21, hW10, hW11, hW20, hW21⟩ :=
      row_scalar_bounds r q hr hq hq2
  have holdSmall : ∀ x ∈ oldNeg, |f x| ≤ Q r q - 1 := by
    simpa only [abs_neg] using dyadic_small (fun x => -f x) (a r q) (Q r q)
      oldNeg ha.le hold (by
        rw [segment_length, hpowL]
        unfold a H Q
        nlinarith [hq])
  have hnextSmall : ∀ x ∈ nextNeg, |f x| ≤ Q r q - 1 := by
    simpa only [abs_neg] using dyadic_small (fun x => -f x) (z1 r q) (Q r q)
      nextNeg hz1.le hnext (by
        rw [segment_length, hpowL1]
        have hCq : C r q = 2 * Q r q - 1 := by unfold C Q; ring
        have hw : q / 2 * z1 r q < C r q := by simpa [W1] using hW11
        rw [hCq] at hw
        omega)
  have hthirdSmall : ∀ x ∈ thirdNeg, |f x| ≤ Q r q - 1 := by
    simpa only [abs_neg] using dyadic_small (fun x => -f x) (z2 r q) (Q r q)
      thirdNeg hz2.le hthird (by
        rw [segment_length, hpowL1]
        have hCq : C r q = 2 * Q r q - 1 := by unfold C Q; ring
        have hw : q / 2 * z2 r q < C r q := by simpa [W2] using hW21
        rw [hCq] at hw
        omega)
  have htopSmall : |f top| ≤ Q r q - 1 := by
    rw [hvalues.2.2.1]
    have hrhalf : 0 ≤ r / 2 := Int.ediv_nonneg (by omega) (by norm_num)
    rw [abs_of_nonneg (mul_nonneg hrhalf hb.le)]
    have he : 2 * ((r / 2) * b r q) = V1 r q := by
      unfold V1; linear_combination (b r q) * hr2
    have hCq : C r q = 2 * Q r q - 1 := by unfold C Q; ring
    rw [hCq] at hV11
    omega
  have hposSmall : ∀ x ∈ oldPosLower, |f x| ≤ Q r q - 1 := by
    apply dyadic_small f (b r q) (Q r q) oldPosLower hb.le hpos
    rw [segment_length, hpowJ]
    have hrhalf : r / 2 ≤ r := by omega
    have hV1cap : V1 r q ≤ 2 * Q r q - 2 := by
      have hCq : C r q = 2 * Q r q - 1 := by unfold C Q; ring
      rw [hCq] at hV11
      omega
    have hrhalf_nonneg : 0 ≤ r / 2 := by omega
    have he : 2 * ((r / 2) * b r q) = V1 r q := by
      unfold V1
      linear_combination (b r q) * hr2
    nlinarith [hV1cap, he]
  have hsmall : ∀ x ∈ oldNeg ++ oldPosLower ++ [top] ++ nextNeg ++ thirdNeg,
      |f x| ≤ Q r q - 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact holdSmall x hx
          · exact hposSmall x hx
        · have hxtop : x = top := List.mem_singleton.mp hx
          simpa [hxtop] using htopSmall
      · exact hnextSmall x hx
    · exact hthirdSmall x hx
  have hcover : ([p] ++ oldNeg ++ [dlabel] ++ oldPosLower ++ [top, parent1] ++
      nextNeg ++ [terminal1, parent2] ++ thirdNeg ++ [terminal2]).Perm (List.finRange k) := by
    dsimp [k, baseLength]
    change (physicalRows J L (by omega) hL).Perm (List.finRange (3 * L + J + 4))
    rw [physical_cover]
  have hMD : 0 < M r q - D r q := (polynomial_gates r q hr hq).2.2.2.1
  have hQ0 : 0 ≤ Q r q := by
    unfold Q
    have hr0 : 0 ≤ r := by omega
    have hq0 : 0 ≤ q := by nlinarith [hq, sq_nonneg r]
    positivity
  have hlens : oldNeg.length = L ∧ oldPosLower.length = J - 1 ∧
      nextNeg.length = L - 1 ∧ thirdNeg.length = L - 1 := by
    simp [oldNeg, oldPosLower, nextNeg, thirdNeg, segment_length]
  obtain ⟨word, hp, hs, hz⟩ := schedule_rows f r q n J L hr hq hr2 hq2
    (coefficient_identity J m) hnlo hnhi hpowJ hpowL hpowL1
    p dlabel top parent1 terminal1 parent2 terminal2 oldNeg oldPosLower nextNeg thirdNeg
    hcover hvalues hold hnext hthird hpos hlens hsmall
    ⟨by omega, by omega, hMD.le, by omega, by omega⟩ (actual_total k _ hk)
  have hC : C r q = ((2 : ℤ) ^ k - 2) / 2 := by
    have he := modulus_identity J m
    change (2 : ℤ) ^ k - 1 = N r q at he
    have hpow : (2 : ℤ) ^ k = 16 * r * q ^ 3 := by
      unfold N at he
      nlinarith
    unfold C
    rw [hpow]
    have hr0 : 0 ≤ r := by omega
    have hq0 : 0 ≤ q := by nlinarith [hq, sq_nonneg r]
    have hq3 : 0 ≤ r * q ^ 3 := by positivity
    have heq : 16 * r * q ^ 3 - 2 = 2 * (8 * r * q ^ 3 - 1) := by ring
    rw [heq]
    omega
  exact ⟨word, hp, by simpa [hC] using hs, hz⟩

/- The exact infinite-family endpoint. There is no fixed-prefix or residual
certificate wrapper.
-/
public theorem exists_order (J m d s : ℕ) (hJ : 2 ≤ J) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    let k0 := baseLength J m
    let k := d * k0
    let lam := (2 ^ k - 1) / (2 ^ k0 - 1)
    let t := (lam * (M (r J) (q J m)).toNat) % (2 ^ k - 1)
    let ts := (2 ^ s * t) % (2 ^ k - 1)
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      (word.map (actualSource k ts)).sum = 0 ∧
      ∀ n : ℕ, ((word.take n).map (actualSource k ts)).sum ∈
        Set.Icc (0 : ℤ) (((2 : ℤ) ^ k - 2) / 2) := by
  dsimp only
  have hb : 0 < baseLength J m := by unfold baseLength; omega
  obtain ⟨base, hp, hs, hz⟩ := proposed_base_order J m hJ hm
  obtain ⟨repeated, hpr, hsr, hzr⟩ := repeated_word (baseLength J m) d
    (M (r J) (q J m)).toNat hb hd base hp hs hz
  rw [multiplier_quotient _ _ hb] at hsr hzr
  obtain ⟨rotated, hprot, hsrot, hzrot⟩ := rotated_word _ _ s
    (Nat.mul_pos (by omega) hb) _ repeated hpr hsr hzr
  refine ⟨rotated, hprot, hzrot, ?_⟩
  intro n
  simpa only [zero_add, Set.mem_Icc] using inStrip_prefix hsrot n

end D5.S3.Combinatorics.Circle.ThreeRowSource
