/- GID: D5/S1/Digit/AlternatingFloorSqrtZeroBlocks
   generality: G
   mirror-B: D5/B/S1/Digit/AlternatingFloorSqrtZeroBlocks
   mirror-E: none(waiver:symbolic-proof)
   anchors: []
   utility: none
   digest: Explicit disjoint zero blocks for alternating floor square-root differences. -/

import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.AlternatingFloorSqrtZeroBlocks

/-- Natural square-root encoding of the floor difference; subtraction is truncated. -/
def d (n l : Nat) : Nat := Nat.sqrt (2 * l * n) - Nat.sqrt ((2 * l - 1) * n)

/-- The explicit block start, using natural division and truncated subtraction. -/
def blockStart (n lam : Nat) : Nat :=
  (n - 1) / 2 + 1 + lam - Nat.sqrt (2 * lam * n)

/-- Definition fidelity on the source domain, with real arithmetic inside the roots. -/
theorem d_eq_floor_real_sqrt (n l : Nat) (hl : 1 <= l) :
    (d n l : Int) =
      ⌊Real.sqrt (2 * (l : Real) * (n : Real))⌋ -
        ⌊Real.sqrt ((2 * (l : Real) - 1) * (n : Real))⌋ := by
  have hsub : 1 <= 2 * l := by omega
  have hcast : (((2 * l - 1) * n : Nat) : Real) =
      (2 * (l : Real) - 1) * (n : Real) := by
    simp only [Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_ofNat, Nat.cast_one]
  have hcast' : ((2 * l * n : Nat) : Real) = 2 * (l : Real) * (n : Real) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [← hcast, ← hcast']
  rw [Real.floor_real_sqrt_eq_nat_sqrt, Real.floor_real_sqrt_eq_nat_sqrt]
  exact Int.ofNat_sub (Nat.sqrt_le_sqrt (Nat.mul_le_mul_right n (Nat.sub_le _ _)))

private theorem label_bounds {n h lam : Nat} (hn : n = 2 * h + 1)
    (hlam : 1 <= lam) (hlamh : lam <= h) :
    lam <= Nat.sqrt ((2 * lam - 1) * n) /\
      Nat.sqrt (2 * lam * n) <= h + lam := by
  constructor
  · apply Nat.le_sqrt'.2
    have ht : 2 * lam - 1 + 1 = 2 * lam := by omega
    have hprod : (2 * lam - 1) * n + n = 2 * lam * n := by
      nlinarith [congrArg (fun x : Nat => x * n) ht]
    have hnl : 2 * lam + 1 <= n := by omega
    nlinarith [Nat.mul_le_mul_left (2 * lam - 1) hnl]
  · have hgap : 2 * lam * n < (h + lam + 1) ^ 2 := by
      have hd : h - lam + lam = h := Nat.sub_add_cancel hlamh
      nlinarith [sq_nonneg (h - lam : Int),
        congrArg (fun x : Nat => x ^ 2) hd]
    exact Nat.le_of_lt_succ (Nat.sqrt_lt'.2 hgap)

/-- Complementary indices place both radicands between the same consecutive squares. -/
theorem witness_bounds {n h lam k : Nat} (hn : n = 2 * h + 1)
    (hlam : 1 <= lam) (hlamh : lam <= h)
    (hka : Nat.sqrt ((2 * lam - 1) * n) + 2 <= k)
    (hkb : k <= Nat.sqrt (2 * lam * n)) :
    let l := h + 1 + lam - k
    1 <= l /\ l <= h /\ k <= n /\
      (n - k) ^ 2 <= (2 * l - 1) * n /\
      (2 * l - 1) * n <= 2 * l * n /\
      2 * l * n < (n - k + 1) ^ 2 := by
  have hr := label_bounds hn hlam hlamh
  have hkn : k <= n := by omega
  have hkl : k <= h + 1 + lam := by omega
  let l := h + 1 + lam - k
  have hladd : l + k = h + 1 + lam := Nat.sub_add_cancel hkl
  have hlpos : 1 <= l := by omega
  have hlh : l <= h := by omega
  have hk2 : k ^ 2 <= 2 * lam * n := Nat.le_sqrt'.1 hkb
  have hkm2 : (2 * lam - 1) * n < (k - 1) ^ 2 :=
    Nat.sqrt_lt'.1 (by omega)
  have hnk : n - k + k = n := Nat.sub_add_cancel hkn
  have hkm : k - 1 + 1 = k := by omega
  have htwol : 2 * l - 1 + 1 = 2 * l := by omega
  have htwolam : 2 * lam - 1 + 1 = 2 * lam := by omega
  have hlabel : 2 * l + 2 * k = n + 1 + 2 * lam := by omega
  have hlabelmul := congrArg (fun x : Nat => x * n) hlabel
  have hnksq := congrArg (fun x : Nat => x ^ 2) hnk
  have hnkmul := congrArg (fun x : Nat => x * k) hnk
  have hkmsq := congrArg (fun x : Nat => x ^ 2) hkm
  have htwolmul := congrArg (fun x : Nat => x * n) htwol
  have htwolammul := congrArg (fun x : Nat => x * n) htwolam
  refine And.intro hlpos (And.intro hlh (And.intro hkn ?_))
  constructor
  · nlinarith
  constructor
  · exact Nat.mul_le_mul_right n (Nat.sub_le _ _)
  · nlinarith

/-- Each offset in an eligible block has a complementary index making both roots equal. -/
theorem block_point {n h lam : Nat} (hn : n = 2 * h + 1)
    (hlam : 1 <= lam) (hlamh : lam <= h) (hd : 2 <= d n lam)
    {j : Nat} (hj : j <= d n lam - 2) :
    1 <= blockStart n lam + j /\ blockStart n lam + j <= h /\
      exists k, k <= n /\ blockStart n lam + j + k = h + 1 + lam /\
        Nat.sqrt ((2 * (blockStart n lam + j) - 1) * n) = n - k /\
        Nat.sqrt (2 * (blockStart n lam + j) * n) = n - k := by
  have hh : (n - 1) / 2 = h := by omega
  have hr := label_bounds hn hlam hlamh
  have hd' : Nat.sqrt ((2 * lam - 1) * n) + 2 <= Nat.sqrt (2 * lam * n) := by
    unfold d at hd
    omega
  have hj' : j <= Nat.sqrt (2 * lam * n) - Nat.sqrt ((2 * lam - 1) * n) - 2 := hj
  let k := Nat.sqrt (2 * lam * n) - j
  have hka : Nat.sqrt ((2 * lam - 1) * n) + 2 <= k := by omega
  have hkb : k <= Nat.sqrt (2 * lam * n) := Nat.sub_le _ _
  have hidx : h + 1 + lam - k = blockStart n lam + j := by
    simp only [blockStart, hh]
    omega
  have hb := witness_bounds hn hlam hlamh hka hkb
  change 1 <= h + 1 + lam - k /\ _ at hb
  rw [hidx] at hb
  refine And.intro hb.1 (And.intro hb.2.1 ?_)
  refine Exists.intro k (And.intro hb.2.2.1 (And.intro ?_ (And.intro ?_ ?_)))
  · simp only [blockStart, hh]
    omega
  · exact (Nat.eq_sqrt'.2 (And.intro hb.2.2.2.1
      (lt_of_le_of_lt hb.2.2.2.2.1 hb.2.2.2.2.2))).symm
  · exact (Nat.eq_sqrt'.2 (And.intro
      (le_trans hb.2.2.2.1 hb.2.2.2.2.1) hb.2.2.2.2.2)).symm

/-- Every eligible label has the asserted consecutive zero block inside the source range. -/
theorem zero_block {n h lam : Nat} (hn : n = 2 * h + 1)
    (hlam : 1 <= lam) (hlamh : lam <= h) (hd : 2 <= d n lam) :
    1 <= blockStart n lam /\ blockStart n lam + (d n lam - 2) <= h /\
      forall j, j <= d n lam - 2 -> d n (blockStart n lam + j) = 0 := by
  have hfirst := block_point hn hlam hlamh hd (Nat.zero_le (d n lam - 2))
  have hlast := block_point hn hlam hlamh hd (Nat.le_refl (d n lam - 2))
  refine And.intro (by simpa using hfirst.1) (And.intro hlast.2.1 ?_)
  intro j hj
  obtain ⟨_, _, k, _, _, ha, hb⟩ := block_point hn hlam hlamh hd hj
  unfold d
  rw [ha, hb, Nat.sub_self]

/-- Equal complementary root values at a common index recover both the index and label. -/
theorem common_index_label_recovery {n h lam mu l k j : Nat}
    (hkn : k <= n) (hjn : j <= n)
    (hlk : l + k = h + 1 + lam) (hlj : l + j = h + 1 + mu)
    (hroot : n - k = n - j) :
    k = j /\ lam = mu := by
  omega

/-- A common index would recover the same complementary root and the same label. -/
theorem blocks_disjoint {n h lam mu : Nat} (hn : n = 2 * h + 1)
    (hlam : 1 <= lam) (hlamh : lam <= h) (hdlam : 2 <= d n lam)
    (hmu : 1 <= mu) (hmuh : mu <= h) (hdmu : 2 <= d n mu)
    (hne : lam ≠ mu) :
    forall l, blockStart n lam <= l -> l <= blockStart n lam + (d n lam - 2) ->
      blockStart n mu <= l -> l <= blockStart n mu + (d n mu - 2) -> False := by
  intro l hll hlu hml hmu'
  have hlj : l - blockStart n lam <= d n lam - 2 := by omega
  have hmj : l - blockStart n mu <= d n mu - 2 := by omega
  have hli : blockStart n lam + (l - blockStart n lam) = l := by omega
  have hmi : blockStart n mu + (l - blockStart n mu) = l := by omega
  have hb1 := block_point hn hlam hlamh hdlam hlj
  have hb2 := block_point hn hmu hmuh hdmu hmj
  rw [hli] at hb1
  rw [hmi] at hb2
  obtain ⟨_, _, k, hkn, hlk, _, hfk⟩ := hb1
  obtain ⟨_, _, j, hjn, hlj', _, hfj⟩ := hb2
  have hroot : n - k = n - j := hfk.symm.trans hfj
  exact hne (common_index_label_recovery hkn hjn hlk hlj' hroot).2

/-- The full simultaneous existence and disjointness statement of Conjecture 2.1. -/
theorem conjecture21 {n : Nat} (hn : 1 <= n) (hodd : Odd n) :
    exists s : Nat -> Nat,
      (forall lam, 1 <= lam -> lam <= (n - 1) / 2 -> 2 <= d n lam ->
        1 <= s lam /\ s lam + (d n lam - 2) <= (n - 1) / 2 /\
        forall j, j <= d n lam - 2 -> d n (s lam + j) = 0) /\
      (forall lam mu, 1 <= lam -> lam <= (n - 1) / 2 -> 2 <= d n lam ->
        1 <= mu -> mu <= (n - 1) / 2 -> 2 <= d n mu -> lam ≠ mu ->
        forall l, s lam <= l -> l <= s lam + (d n lam - 2) ->
          s mu <= l -> l <= s mu + (d n mu - 2) -> False) := by
  obtain ⟨h, hh⟩ := hodd
  have hnh : n = 2 * h + 1 := by omega
  have hh' : (n - 1) / 2 = h := by omega
  refine Exists.intro (blockStart n) (And.intro ?_ ?_)
  · intro lam hlam hlamh hd
    rw [hh'] at hlamh ⊢
    exact zero_block hnh hlam hlamh hd
  · intro lam mu hlam hlamh hdlam hmu hmuh hdmu hne
    rw [hh'] at hlamh hmuh
    exact blocks_disjoint hnh hlam hlamh hdlam hmu hmuh hdmu hne

example : (List.range 7).map (fun j => d 15 (j + 1)) = [2, 1, 1, 0, 1, 1, 1] := by
  decide +kernel
example : (List.range 10).map (fun j => d 21 (j + 1)) = [2, 2, 1, 0, 1, 0, 1, 1, 1, 1] := by
  decide +kernel
example : (List.range 16).map (fun j => d 33 (j + 1)) =
    [3, 2, 2, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1] := by decide +kernel
example : 1 <= (21 : Nat) /\ Odd (21 : Nat) /\ 2 <= d 21 1 := by decide +kernel
example : Nonempty Nat := ⟨21⟩

#print axioms d_eq_floor_real_sqrt
#print axioms witness_bounds
#print axioms block_point
#print axioms zero_block
#print axioms common_index_label_recovery
#print axioms blocks_disjoint
#print axioms conjecture21

end D5.S1.Digit.AlternatingFloorSqrtZeroBlocks
