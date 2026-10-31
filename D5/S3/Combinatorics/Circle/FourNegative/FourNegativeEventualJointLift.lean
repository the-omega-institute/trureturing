/- GID: D5/S3/Combinatorics/Circle/FourNegative/FourNegativeEventualJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/FourNegativeEventualJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A common physical four-negative order and its literal fresh ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open private four_chain_table eventual_mask_certificate
  chainMask chainMask_sum maskWord
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual
open FourNegativeEventual
open private mask_labels_mem positive_block_strip
  from D5.S3.Combinatorics.Circle.ThreeBitSource
open ThreeBitSource
open private label lift_order
  marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open ThreeNegativeEqualOuterJointLift

private theorem paired_seam_bounds (N Y rho n T H K : ℤ)
    (hY : Y ≤ N) (hH : 2 * H = N - Y)
    (hK : 2 * K = 2 * N + 1 - (2 * Y - rho))
    (hn : 1 ≤ n) (hrho : 1 ≤ rho)
    (hres : n * rho < n * Y - T) (hup : 2 * (n * Y - T) < Y - 1) :
    (0 ≤ n * Y - T ∧ H + (n * Y - T) ≤ N / 2) ∧
    (0 ≤ n * (2 * Y - rho) - 2 * T ∧
      K + (n * (2 * Y - rho) - 2 * T) ≤ N) := by
  have hnrho : rho ≤ n * rho := by nlinarith only [hn, hrho]
  have ht : 0 ≤ n * Y - T := by nlinarith only [hres, hnrho, hrho]
  have hpeak : 2 * (H + (n * Y - T)) < N - 1 := by nlinarith only [hH, hup]
  refine ⟨⟨ht, by omega⟩, ?_, ?_⟩
  · nlinarith only [hres, hnrho, hrho]
  · nlinarith only [hup, hK, hnrho, hrho]

private theorem positive_then_step (f : ℕ → ℤ) (C h : ℤ) (P R : List ℕ) (v : ℕ)
    (hp : ∀ i ∈ P, 0 ≤ f i) (hh : 0 ≤ h) (hpeak : h + (P.map f).sum ≤ C)
    (hrest : InStrip f C (h + (P.map f).sum + f v) R) :
    InStrip f C h (P ++ v :: R) := by
  apply inStrip_append (positive_block_strip hp hh hpeak)
  have hs : 0 ≤ (P.map f).sum := by simpa using List.sum_le_sum hp
  exact ⟨by omega, hpeak, hrest⟩

private theorem four_strip_of_masses (f : ℕ → ℤ) (C t1 t2 t3 : ℤ)
    (P1 P2 P3 P4 : List ℕ) (alpha beta gamma delta : ℕ)
    (hC : 0 ≤ C)
    (hp1 : ∀ i ∈ P1, 0 ≤ f i) (hp2 : ∀ i ∈ P2, 0 ≤ f i)
    (hp3 : ∀ i ∈ P3, 0 ≤ f i) (hp4 : ∀ i ∈ P4, 0 ≤ f i)
    (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (ht3 : 0 ≤ t3)
    (hs1 : (P1.map f).sum + f alpha = t1)
    (hs2 : t1 + (P2.map f).sum + f beta = t2)
    (hs3 : t2 + (P3.map f).sum + f gamma = t3)
    (hs4 : t3 + (P4.map f).sum + f delta = 0)
    (hb1 : (P1.map f).sum ≤ C) (hb2 : t1 + (P2.map f).sum ≤ C)
    (hb3 : t2 + (P3.map f).sum ≤ C) (hb4 : t3 + (P4.map f).sum ≤ C) :
    InStrip f C 0 (P1 ++ alpha :: P2 ++ beta :: P3 ++ gamma :: P4 ++ [delta]) := by
  simp only [List.append_assoc, List.cons_append]
  apply positive_then_step f C 0 P1 (P2 ++ beta :: (P3 ++ gamma :: (P4 ++ [delta]))) alpha
    hp1 (by omega) (by omega)
  rw [zero_add, hs1]
  apply positive_then_step f C t1 P2 (P3 ++ gamma :: (P4 ++ [delta])) beta hp2 ht1 hb2
  rw [hs2]
  apply positive_then_step f C t2 P3 (P4 ++ [delta]) gamma hp3 ht2 hb3
  rw [hs3]
  apply positive_then_step f C t3 P4 [] delta hp4 ht3 hb4
  rw [hs4]
  exact ⟨by omega, hC⟩

private theorem negative_step (N Y Z h : ℤ) (hrel : 2 * h * Y = N + Z) :
    -(N - Z) / 2 = Z - h * Y := by
  have he : -(N - Z) = 2 * (Z - h * Y) := by nlinarith only [hrel]
  rw [he]
  omega

private theorem last_seam_bounds (N A H K : ℤ) (hA : 1 ≤ A ∧ A < N)
    (hH : 2 * H = N - A) (hK : 2 * K = 2 * N + 1 - A) :
    (0 ≤ H ∧ H ≤ N / 2) ∧ (0 ≤ K ∧ K ≤ N) := by
  constructor <;> constructor <;> omega

set_option maxHeartbeats 1000000 in
/-- The eventual construction keeps all four independent gap coordinates. -/
theorem actualSource_four_negative_eventual_joint_lift (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : a + b + c + 3 ≤ d) :
    ∃ sigma : List (Fin (a + b + c + d)), ∃ j : ℕ,
      j ≤ a + b + c + d ∧
      OriginalOrder (a + b + c + d) (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧
      OriginalOrder (a + b + c + d + 1)
        (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
        (earWord (a + b + c + d) sigma j) := by
  let k := a + b + c + d
  let u := 1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)
  let x : ℤ := 2 ^ a
  let y : ℤ := 2 ^ b
  let z : ℤ := 2 ^ c
  let t : ℤ := 2 ^ d
  let P := x * y * z
  let DB := 1 + x + x * y
  let DL := z * (1 + x)
  let DM := y * z
  let A := P + DB
  let B := t * DB + 1
  let L := t * DL + 1 + z
  let M := t * DM + 1 + y + y * z
  let N := P * t - 1
  let B' := 2 * B - 1
  let L' := 2 * L - 1 - z
  let M' := 2 * M - 1 - y - y * z
  let td : ℤ := 2 ^ (d - 1)
  let zc : ℤ := 2 ^ (c - 1)
  let yb : ℤ := 2 ^ (b - 1)
  let xa : ℤ := 2 ^ (a - 1)
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * A)
  let g := fun i : ℕ => centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * A))
  obtain ⟨hA, hB, hL, hM, huf, hvf, hwf, hxf, hug, hvg, hwg, hxg, hfresh⟩ :=
    four_chain_table a b c d ha hb hc hd
  change 1 ≤ A ∧ A < N at hA
  change 1 ≤ B ∧ B < N at hB
  change 1 ≤ L ∧ L < N at hL
  change 1 ≤ M ∧ M < N at hM
  change g (d + c + b + a) = A at hfresh
  have half_pow (e : ℕ) (he : 1 ≤ e) : (2 : ℤ) ^ e = 2 * (2 : ℤ) ^ (e - 1) := by
    calc
      (2 : ℤ) ^ e = 2 ^ ((e - 1) + 1) := by congr 1 <;> omega
      _ = 2 * (2 : ℤ) ^ (e - 1) := by rw [pow_succ]; ring
  have ht : t = 2 * td := half_pow d (by omega)
  have hz : z = 2 * zc := half_pow c (by omega)
  have hy : y = 2 * yb := half_pow b (by omega)
  have hx : x = 2 * xa := half_pow a (by omega)
  have hrelU : 2 * td * A = N + B := by
    rw [show 2 * td = t from ht.symm]; dsimp [A, B, N, P, DB]; ring
  have hrelV : 2 * zc * B = N + L := by
    rw [show 2 * zc = z from hz.symm]; dsimp [B, L, N, P, DB, DL]; ring
  have hrelW : 2 * yb * L = N + M := by
    rw [show 2 * yb = y from hy.symm]; dsimp [L, M, N, P, DL, DM]; ring
  have hrelX : 2 * xa * M = N + A := by
    rw [show 2 * xa = x from hx.symm]; dsimp [M, A, N, P, DM, DB]; ring
  have hrelU' : 2 * td * (2 * A) = (2 * N + 1) + B' := by
    dsimp [B']; nlinarith only [hrelU]
  have hrelV' : 2 * zc * B' = (2 * N + 1) + L' := by
    dsimp [B', L']; rw [hz]; nlinarith only [hrelV]
  have hrelW' : 2 * yb * L' = (2 * N + 1) + M' := by
    dsimp [L', M']; rw [hy]; nlinarith only [hrelW]
  have hrelX' : 2 * xa * M' = (2 * N + 1) + A := by
    have he : A = x * (1 + y + y * z) + 1 := by dsimp [A, P, DB]; ring
    rw [hx] at he
    dsimp [M']; nlinarith only [hrelX, he]
  obtain ⟨q, nB, nL, nM, hq, hnB, hnL, hnM, hperm, hsB, hsL, hsM⟩ :=
    eventual_mask_certificate a b c d ha hb hc hd
  change ((nB : ℤ) < nB * B - A * q ∧ 2 * (nB * B - A * q) < B - 1) at hsB
  change ((nL : ℤ) * (1 + z) < nL * L - A * q ∧ 2 * (nL * L - A * q) < L - 1) at hsL
  change ((nM : ℤ) * (1 + y + y * z) < nM * M - A * q ∧
    2 * (nM * M - A * q) < M - 1) at hsM
  have hgA : 0 ≤ 2 * A := by omega
  have hgB : 0 ≤ B' := by dsimp [B']; omega
  have hgL : 0 ≤ L' := by
    dsimp [L', L, DL, t, z, x]
    ring_nf
    positivity
  have hgM : 0 ≤ M' := by
    dsimp [M', M, DM, t, y, z]
    ring_nf
    positivity
  have hufpos (e : ℕ) (he : e < d - 1) :
      f (0 + e) = (2 : ℤ) ^ e * (A) := by
    have hv := huf e (by omega)
    simpa only [ite_eq_left (show e + 1 < d by omega), Nat.zero_add] using hv
  have hugpos (e : ℕ) (he : e < d - 1) :
      g (0 + e) = (2 : ℤ) ^ e * (2 * A) := by
    have hv := hug e (by omega)
    simpa only [ite_eq_left (show e + 1 < d by omega), Nat.zero_add] using hv
  have hunegf : f (d - 1) = B - td * A := by
    have hv := huf (d - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change f (d - 1) = -((N) - (B)) / 2 at hv
    rw [negative_step _ _ _ _ hrelU] at hv
    simpa only [Nat.zero_add, show 0 + (d - 1) = 0 + d - 1 by omega] using hv
  have hunegg : g (d - 1) = B' - td * (2 * A) := by
    have hv := hug (d - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change g (d - 1) = -((2 * N + 1) - (B')) / 2 at hv
    rw [negative_step _ _ _ _ hrelU'] at hv
    simpa only [Nat.zero_add, show 0 + (d - 1) = 0 + d - 1 by omega] using hv
  have hvfpos (e : ℕ) (he : e < c - 1) :
      f (d + e) = (2 : ℤ) ^ e * (B) := by
    have hv := hvf e (by omega)
    simpa only [ite_eq_left (show e + 1 < c by omega), Nat.zero_add] using hv
  have hvgpos (e : ℕ) (he : e < c - 1) :
      g (d + e) = (2 : ℤ) ^ e * (B') := by
    have hv := hvg e (by omega)
    simpa only [ite_eq_left (show e + 1 < c by omega), Nat.zero_add] using hv
  have hvnegf : f (d + c - 1) = L - zc * B := by
    have hv := hvf (c - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change f (d + (c - 1)) = -((N) - (L)) / 2 at hv
    rw [negative_step _ _ _ _ hrelV] at hv
    simpa only [Nat.zero_add, show d + (c - 1) = d + c - 1 by omega] using hv
  have hvnegg : g (d + c - 1) = L' - zc * B' := by
    have hv := hvg (c - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change g (d + (c - 1)) = -((2 * N + 1) - (L')) / 2 at hv
    rw [negative_step _ _ _ _ hrelV'] at hv
    simpa only [Nat.zero_add, show d + (c - 1) = d + c - 1 by omega] using hv
  have hwfpos (e : ℕ) (he : e < b - 1) :
      f (d + c + e) = (2 : ℤ) ^ e * (L) := by
    have hv := hwf e (by omega)
    simpa only [ite_eq_left (show e + 1 < b by omega), Nat.zero_add] using hv
  have hwgpos (e : ℕ) (he : e < b - 1) :
      g (d + c + e) = (2 : ℤ) ^ e * (L') := by
    have hv := hwg e (by omega)
    simpa only [ite_eq_left (show e + 1 < b by omega), Nat.zero_add] using hv
  have hwnegf : f (d + c + b - 1) = M - yb * L := by
    have hv := hwf (b - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change f (d + c + (b - 1)) = -((N) - (M)) / 2 at hv
    rw [negative_step _ _ _ _ hrelW] at hv
    simpa only [Nat.zero_add, show d + c + (b - 1) = d + c + b - 1 by omega] using hv
  have hwnegg : g (d + c + b - 1) = M' - yb * L' := by
    have hv := hwg (b - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change g (d + c + (b - 1)) = -((2 * N + 1) - (M')) / 2 at hv
    rw [negative_step _ _ _ _ hrelW'] at hv
    simpa only [Nat.zero_add, show d + c + (b - 1) = d + c + b - 1 by omega] using hv
  have hxfpos (e : ℕ) (he : e < a - 1) :
      f (d + c + b + e) = (2 : ℤ) ^ e * (M) := by
    have hv := hxf e (by omega)
    simpa only [ite_eq_left (show e + 1 < a by omega), Nat.zero_add] using hv
  have hxgpos (e : ℕ) (he : e < a - 1) :
      g (d + c + b + e) = (2 : ℤ) ^ e * (M') := by
    have hv := hxg e (by omega)
    simpa only [ite_eq_left (show e + 1 < a by omega), Nat.zero_add] using hv
  have hxnegf : f (d + c + b + a - 1) = A - xa * M := by
    have hv := hxf (a - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change f (d + c + b + (a - 1)) = -((N) - (A)) / 2 at hv
    rw [negative_step _ _ _ _ hrelX] at hv
    simpa only [Nat.zero_add, show d + c + b + (a - 1) = d + c + b + a - 1 by omega] using hv
  have hxnegg : g (d + c + b + a - 1) = A - xa * M' := by
    have hv := hxg (a - 1) (by omega)
    rw [ite_eq_right (by omega)] at hv
    change g (d + c + b + (a - 1)) = -((2 * N + 1) - (A)) / 2 at hv
    rw [negative_step _ _ _ _ hrelX'] at hv
    simpa only [Nat.zero_add, show d + c + b + (a - 1) = d + c + b + a - 1 by omega] using hv
  have block (len off m : ℕ) (hm : m < 2 ^ len) (Y Z : ℤ)
      (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
      (hf : ∀ e < len, f (off + e) = (2 : ℤ) ^ e * Y)
      (hg : ∀ e < len, g (off + e) = (2 : ℤ) ^ e * Z) :
      (((chainMask len off m).map f).sum = (m : ℤ) * Y) ∧
      (((chainMask len off m).map g).sum = (m : ℤ) * Z) ∧
      (∀ i ∈ chainMask len off m, 0 ≤ f i) ∧
      (∀ i ∈ chainMask len off m, 0 ≤ g i) := by
    refine ⟨chainMask_sum len off m hm f Y hf, chainMask_sum len off m hm g Z hg, ?_, ?_⟩
    all_goals
      intro i hi
      simp only [chainMask, dite_eq_left hm, Finset.mem_toList] at hi
      obtain ⟨e, he, _, rfl⟩ := (mask_labels_mem len off m i hm).mp hi
      first | rw [hf e he]; positivity | rw [hg e he]; positivity
  let U0 := chainMask (d - 1) (0) (2 ^ (d - 1) - q)
  have hU0 := block (d - 1) (0) (2 ^ (d - 1) - q) (by omega) (A) (2 * A)
    (by omega) hgA hufpos hugpos
  let U1 := chainMask (d - 1) (0) (q - 1)
  have hU1 := block (d - 1) (0) (q - 1) (by omega) (A) (2 * A)
    (by omega) hgA hufpos hugpos
  let V0 := chainMask (c - 1) (d) (nB - 1)
  have hV0 := block (c - 1) (d) (nB - 1) (by omega) (B) (B')
    (by omega) hgB hvfpos hvgpos
  let V1 := chainMask (c - 1) (d) (2 ^ (c - 1) - nB)
  have hV1 := block (c - 1) (d) (2 ^ (c - 1) - nB) (by omega) (B) (B')
    (by omega) hgB hvfpos hvgpos
  let W0 := chainMask (b - 1) (d + c) (nL - 1)
  have hW0 := block (b - 1) (d + c) (nL - 1) (by omega) (L) (L')
    (by omega) hgL hwfpos hwgpos
  let W1 := chainMask (b - 1) (d + c) (2 ^ (b - 1) - nL)
  have hW1 := block (b - 1) (d + c) (2 ^ (b - 1) - nL) (by omega) (L) (L')
    (by omega) hgL hwfpos hwgpos
  let X0 := chainMask (a - 1) (d + c + b) (nM - 1)
  have hX0 := block (a - 1) (d + c + b) (nM - 1) (by omega) (M) (M')
    (by omega) hgM hxfpos hxgpos
  let X1 := chainMask (a - 1) (d + c + b) (2 ^ (a - 1) - nM)
  have hX1 := block (a - 1) (d + c + b) (2 ^ (a - 1) - nM) (by omega) (M) (M')
    (by omega) hgM hxfpos hxgpos
  let P1 := U0 ++ V0
  let P2 := V1 ++ W0
  let P3 := W1 ++ X0
  let P4 := U1 ++ X1
  let tau1 : ℤ := nB * B - A * q
  let tau2 : ℤ := nL * L - A * q
  let tau3 : ℤ := nM * M - A * q
  let tau1' : ℤ := nB * B' - 2 * A * q
  let tau2' : ℤ := nL * L' - 2 * A * q
  let tau3' : ℤ := nM * M' - 2 * A * q
  have hmass1f : (P1.map f).sum = td * A - B + tau1 := by
    simp only [P1, U0, V0, List.map_append, List.sum_append, hU0.1, hV0.1,
      Nat.cast_sub hq.2, Nat.cast_sub hnB.1,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hmass1g : (P1.map g).sum = td * (2 * A) - B' + tau1' := by
    simp only [P1, U0, V0, List.map_append, List.sum_append, hU0.2.1, hV0.2.1,
      Nat.cast_sub hq.2, Nat.cast_sub hnB.1,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hmass2f : (P2.map f).sum = zc * B - L + tau2 - tau1 := by
    simp only [P2, V1, W0, List.map_append, List.sum_append, hV1.1, hW0.1,
      Nat.cast_sub hnB.2, Nat.cast_sub hnL.1,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hmass2g : (P2.map g).sum = zc * B' - L' + tau2' - tau1' := by
    simp only [P2, V1, W0, List.map_append, List.sum_append, hV1.2.1, hW0.2.1,
      Nat.cast_sub hnB.2, Nat.cast_sub hnL.1,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hmass3f : (P3.map f).sum = yb * L - M + tau3 - tau2 := by
    simp only [P3, W1, X0, List.map_append, List.sum_append, hW1.1, hX0.1,
      Nat.cast_sub hnL.2, Nat.cast_sub hnM.1,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hmass3g : (P3.map g).sum = yb * L' - M' + tau3' - tau2' := by
    simp only [P3, W1, X0, List.map_append, List.sum_append, hW1.2.1, hX0.2.1,
      Nat.cast_sub hnL.2, Nat.cast_sub hnM.1,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hmass4f : (P4.map f).sum = xa * M - A - tau3 := by
    simp only [P4, U1, X1, List.map_append, List.sum_append, hU1.1, hX1.1,
      Nat.cast_sub hq.1, Nat.cast_sub hnM.2,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hmass4g : (P4.map g).sum = xa * M' - 2 * A - tau3' := by
    simp only [P4, U1, X1, List.map_append, List.sum_append, hU1.2.1, hX1.2.1,
      Nat.cast_sub hq.1, Nat.cast_sub hnM.2,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    dsimp [tau1, tau2, tau3, tau1', tau2', tau3', td, zc, yb, xa]
    ring
  have hboundB := paired_seam_bounds N B 1 nB (A * q) (td * A - B)
    (td * (2 * A) - B') hB.2.le (by nlinarith only [hrelU])
    (by dsimp [B']; nlinarith only [hrelU']) (by exact_mod_cast hnB.1)
    (by norm_num) (by simpa using hsB.1) hsB.2
  have hboundL := paired_seam_bounds N L (1 + z) nL (A * q) (zc * B - L)
    (zc * B' - L') hL.2.le (by nlinarith only [hrelV])
    (by dsimp [L']; nlinarith only [hrelV']) (by exact_mod_cast hnL.1)
    (by have hz0 : 0 ≤ z := by dsimp [z]; positivity
        omega) hsL.1 hsL.2
  have hboundM := paired_seam_bounds N M (1 + y + y * z) nM (A * q) (yb * L - M)
    (yb * L' - M') hM.2.le (by nlinarith only [hrelW])
    (by dsimp [M']; nlinarith only [hrelW']) (by exact_mod_cast hnM.1)
    (by have hy0 : 0 ≤ y := by dsimp [y]; positivity
        have hyz0 : 0 ≤ y * z := by dsimp [y, z]; positivity
        nlinarith only [hy0, hyz0]) hsM.1 hsM.2
  have hlast := last_seam_bounds N A (xa * M - A) (xa * M' - A) hA
    (by nlinarith only [hrelX]) (by nlinarith only [hrelX'])
  have hlastf := hlast.1
  have hlastg := hlast.2
  have append_pos (h : ℕ → ℤ) (A B : List ℕ)
      (hA : ∀ i ∈ A, 0 ≤ h i) (hB : ∀ i ∈ B, 0 ≤ h i) :
      ∀ i ∈ A ++ B, 0 ≤ h i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hA i hi
    · exact hB i hi
  have hold : InStrip f (N / 2) 0
      (P1 ++ (d - 1) :: P2 ++ (d + c - 1) :: P3 ++ (d + c + b - 1) ::
        P4 ++ [d + c + b + a - 1]) := by
    apply four_strip_of_masses f (N / 2) tau1 tau2 tau3 P1 P2 P3 P4
      (d - 1) (d + c - 1) (d + c + b - 1) (d + c + b + a - 1)
      (by omega) (append_pos f U0 V0 hU0.2.2.1 hV0.2.2.1)
      (append_pos f V1 W0 hV1.2.2.1 hW0.2.2.1)
      (append_pos f W1 X0 hW1.2.2.1 hX0.2.2.1)
      (append_pos f U1 X1 hU1.2.2.1 hX1.2.2.1)
      hboundB.1.1 hboundL.1.1 hboundM.1.1
    · rw [hmass1f, hunegf]; ring
    · rw [hmass2f, hvnegf]; ring
    · rw [hmass3f, hwnegf]; ring
    · rw [hmass4f, hxnegf]; ring
    · nlinarith only [hmass1f, hboundB.1.2]
    · nlinarith only [hmass2f, hboundL.1.2]
    · nlinarith only [hmass3f, hboundM.1.2]
    · nlinarith only [hmass4f, hlastf.2]
  have hgk : g k = A := by
    simpa only [show d + c + b + a = k by dsimp [k]; omega] using hfresh
  have hearpos : ∀ i ∈ [k] ++ P4, 0 ≤ g i := by
    apply append_pos g [k] P4
    · intro i hi; simp only [List.mem_singleton] at hi; subst i; rw [hgk]; omega
    · exact append_pos g U1 X1 hU1.2.2.2 hX1.2.2.2
  have hearmass : (([k] ++ P4).map g).sum = xa * M' - A - tau3' := by
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hgk, hmass4g]
    ring
  have hnew : InStrip g N 0
      (P1 ++ (d - 1) :: P2 ++ (d + c - 1) :: P3 ++ (d + c + b - 1) ::
        ([k] ++ P4) ++ [d + c + b + a - 1]) := by
    apply four_strip_of_masses g N tau1' tau2' tau3' P1 P2 P3 ([k] ++ P4)
      (d - 1) (d + c - 1) (d + c + b - 1) (d + c + b + a - 1)
      (by omega) (append_pos g U0 V0 hU0.2.2.2 hV0.2.2.2)
      (append_pos g V1 W0 hV1.2.2.2 hW0.2.2.2)
      (append_pos g W1 X0 hW1.2.2.2 hX0.2.2.2) hearpos
      (by dsimp [tau1', B']; nlinarith only [hboundB.2.1])
      (by dsimp [tau2', L']; nlinarith only [hboundL.2.1])
      (by dsimp [tau3', M']; nlinarith only [hboundM.2.1])
    · rw [hmass1g, hunegg]; ring
    · rw [hmass2g, hvnegg]; ring
    · rw [hmass3g, hwnegg]; ring
    · rw [hearmass, hxnegg]; ring
    · dsimp [tau1', B'] at hmass1g ⊢
      nlinarith only [hmass1g, hboundB.2.2]
    · dsimp [tau1', tau2', L'] at hmass2g ⊢
      nlinarith only [hmass2g, hboundL.2.2]
    · dsimp [tau2', tau3', M'] at hmass3g ⊢
      nlinarith only [hmass3g, hboundM.2.2]
    · nlinarith only [hearmass, hlastg.2]
  let Pre := P1 ++ [d - 1] ++ P2 ++ [d + c - 1] ++ P3 ++ [d + c + b - 1]
  let Post := P4 ++ [d + c + b + a - 1]
  let l := Pre ++ Post
  have hpold : l.Perm (List.range k) := by
    simpa only [maskWord, l, Pre, Post, P1, P2, P3, P4, U0, U1, V0, V1, W0, W1, X0, X1,
      List.append_assoc] using hperm
  have hcut : Pre.length ≤ k := by
    have hh := hpold.length_eq
    simp only [l, List.length_append, List.length_range] at hh
    omega
  have hpnew : (Pre ++ k :: Post).Perm (List.range (k + 1)) := by
    have hreorder : (Pre ++ k :: Post).Perm (l ++ [k]) := by
      simpa only [l, List.append_assoc] using
        (List.perm_append_singleton k Post).symm.append_left Pre
    have hrange : List.range k ++ [k] = List.range (k + 1) := by
      simpa only [Nat.succ_eq_add_one] using (List.range_succ (n := k)).symm
    exact hreorder.trans ((hpold.append (List.Perm.refl [k])).trans (List.Perm.of_eq hrange))
  have hmod : modulus k = N := by dsimp [modulus, k, N, P, x, y, z, t]; ring
  have hmod' : modulus (k + 1) = 2 * N + 1 := by
    dsimp [modulus, k, N, P, x, y, z, t]; ring
  have hseed : (u : ℤ) = A := by
    simp only [u, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [A, P, DB, x, y, z]; ring
  have hseed' : ((2 * u : ℕ) : ℤ) = 2 * A := by push_cast; rw [hseed]
  have hk : 0 < k := by dsimp [k]; omega
  have hold' : OriginalOrder k u (l.map (label k hk)) := by
    apply lift_order k u hk l hpold
    · simpa only [f, hmod, hseed, l, Pre, Post, List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append] using hold
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k u (by dsimp [k]; omega)
  have hnew' : OriginalOrder (k + 1) (2 * u)
      ((Pre ++ k :: Post).map (label (k + 1) (by omega))) := by
    apply lift_order (k + 1) (2 * u) (by omega) (Pre ++ k :: Post) hpnew
    · have hhalf : (2 * N + 1) / 2 = N := by omega
      simpa only [g, hmod', hseed', hhalf, Pre, Post, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append] using hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * u) (by dsimp [k]; omega)
  refine ⟨l.map (label k hk), Pre.length, hcut, hold', ?_⟩
  change OriginalOrder (k + 1) (2 * u) (earWord k ((Pre ++ Post).map (label k hk)) Pre.length)
  rw [marked_word k Pre.length hk Pre Post rfl hpold]
  exact hnew'

end D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
