/- GID: D5/S3/Combinatorics/Parking/CutRunCorrespondence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Parking/CutRunCorrespondence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cut and uncut coordinates with circular-to-linear run correspondence. -/

import D5.S3.Combinatorics.Parking.OperationalDynamics

/-!
# Cut-run correspondence

Cutting the circle at an unoccupied vacancy identifies the bounded circular
scanner with the frozen supplier's linear first-free scanner. The forward
feedback-state induction retains anchor priority and the offset-zero rule.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularTwoChoiceParkingBijection

open D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata

def cutSpot {n : Nat} (j x : Spot n) : Nat :=
  (x - j).val

def uncutSpot {n : Nat} (j : Spot n) (p : Nat) : Spot n :=
  j + (p : Spot n)

private theorem firstFree_cut_zero {n : Nat} (occupied : List (Spot n))
    (start : Spot n) (hnodup : occupied.Nodup) (hcard : occupied.length <= n)
    (hzero : (0 : Spot n) ∉ occupied) (hyzero : firstFree n occupied start ≠ 0) :
    cutSpot 0 (firstFree n occupied start) =
      parkStep (occupied.map (cutSpot 0)) (cutSpot 0 start) := by
  have orbit_apply (s : Spot n) (r : Fin (n + 1)) :
      orbitEquiv n s r = (r.val : Spot n) + s := by
    simp only [orbitEquiv, Equiv.trans_apply]
    have hfin : (ZMod.finEquiv (n + 1)).toEquiv r = (r.val : Spot n) := by
      apply ZMod.val_injective (n + 1)
      change r.val = ((r.val : Nat) : Spot n).val
      rw [ZMod.val_natCast_of_lt r.isLt]
    rw [hfin, Equiv.coe_addRight]
  let off := firstFreeOffset n occupied.toFinset start
  let y := firstFree n occupied start
  have hstart : start ≠ 0 := by
    intro hs
    subst start
    exact hyzero (firstFree_of_not_mem occupied 0 hzero)
  letI : NeZero start := ⟨hstart⟩
  let zeroOff : Fin (n + 1) := ⟨(-start).val, ZMod.val_lt _⟩
  have hzeroOrbit : orbitEquiv n start zeroOff = 0 := by
    rw [orbit_apply]
    dsimp [zeroOff]
    rw [ZMod.natCast_zmod_val]
    abel
  have hzeroMem : zeroOff ∈ freeOffsets n occupied.toFinset start := by
    simp [freeOffsets, hzeroOrbit, hzero]
  have hne : (freeOffsets n occupied.toFinset start).Nonempty := ⟨zeroOff, hzeroMem⟩
  have hoffle : off <= zeroOff := by
    change firstFreeOffset n occupied.toFinset start <= zeroOff
    rw [firstFreeOffset, dif_pos hne]
    exact Finset.min'_le _ _ hzeroMem
  have hofflt : off < zeroOff := by
    exact hoffle.lt_of_ne fun heq => hyzero (by
      change firstFree n occupied start = 0
      rw [firstFree, show firstFreeOffset n occupied.toFinset start = zeroOff from heq]
      exact hzeroOrbit)
  have hzeroVal : zeroOff.val = n + 1 - start.val := by
    exact ZMod.val_neg_of_ne_zero start
  have hsum : start.val + off.val < n + 1 := by
    change off.val < zeroOff.val at hofflt
    rw [hzeroVal] at hofflt
    omega
  have hyval : y.val = start.val + off.val := by
    have hsum' : start.val + (firstFreeOffset n occupied.toFinset start).val < n + 1 := by
      simpa [off] using hsum
    change (firstFree n occupied start).val =
      start.val + (firstFreeOffset n occupied.toFinset start).val
    rw [firstFree, orbit_apply]
    have hoffVal :
        (((firstFreeOffset n occupied.toFinset start).val : Nat) : Spot n).val =
          (firstFreeOffset n occupied.toFinset start).val :=
      ZMod.val_natCast_of_lt (firstFreeOffset n occupied.toFinset start).isLt
    rw [ZMod.val_add_of_lt (by simpa [hoffVal, add_comm] using hsum'), hoffVal]
    omega
  have hyfresh : y ∉ occupied := by
    exact firstFree_fresh n occupied start hnodup hcard
  have hyMap : y.val ∉ occupied.map (cutSpot 0) := by
    intro hm
    rcases List.mem_map.mp hm with ⟨z, hz, heq⟩
    apply hyfresh
    have : z = y := ZMod.val_injective (n + 1) (by simpa [cutSpot] using heq)
    simpa [this] using hz
  have hskipped : ∀ q, start.val <= q -> q < y.val ->
      q ∈ occupied.map (cutSpot 0) := by
    intro q hp hq
    have hqn : q < n + 1 := lt_trans hq (ZMod.val_lt y)
    let r : Fin (n + 1) := ⟨q - start.val, by omega⟩
    have hr : r < off := by
      rw [hyval] at hq
      change r.val < off.val
      dsimp [r]
      omega
    have hrmem := firstFree_skipped n occupied start hnodup hcard r hr
    have horbit : orbitEquiv n start r = (q : Spot n) := by
      rw [orbit_apply]
      dsimp [r]
      calc
        ((q - start.val : Nat) : Spot n) + start =
            ((q - start.val : Nat) : Spot n) + (start.val : Spot n) := by
              rw [ZMod.natCast_zmod_val]
        _ = (((q - start.val) + start.val : Nat) : Spot n) := by
              rw [Nat.cast_add]
        _ = (q : Spot n) := by congr 1; omega
    rw [horbit] at hrmem
    apply List.mem_map.mpr
    refine ⟨(q : Spot n), hrmem, ?_⟩
    simp [cutSpot, ZMod.val_natCast_of_lt hqn]
  have hlinear := parkStep_spec (occupied.map (cutSpot 0)) start.val
  have hforward : y.val <= parkStep (occupied.map (cutSpot 0)) start.val := by
    by_contra hlt
    exact hlinear.1 (hskipped _ (le_parkStep _ _) (by omega))
  have hbackward : parkStep (occupied.map (cutSpot 0)) start.val <= y.val := by
    by_contra hlt
    exact hyMap (hlinear.2 y.val (by rw [hyval]; omega) (by omega))
  simpa [cutSpot, y] using le_antisymm hforward hbackward

theorem firstFree_cut {n : Nat} (occupied : List (Spot n)) (start j : Spot n)
    (hnodup : occupied.Nodup) (hcard : occupied.length <= n)
    (hj : j ∉ occupied) (hyj : firstFree n occupied start ≠ j) :
    cutSpot j (firstFree n occupied start) =
      parkStep (occupied.map (cutSpot j)) (cutSpot j start) := by
  have hrotNodup : (rotateList (-j) occupied).Nodup := by
    exact hnodup.map fun _ _ h => add_right_cancel h
  have hrotCard : (rotateList (-j) occupied).length <= n := by
    simpa [rotateList] using hcard
  have hrotZero : (0 : Spot n) ∉ rotateList (-j) occupied := by
    intro h
    apply hj
    apply (mem_rotateList_iff (-j) j occupied).1
    simpa using h
  have hrotLanding : firstFree n (rotateList (-j) occupied) (start - j) ≠ 0 := by
    rw [show start - j = start + -j by abel, firstFree_rotate]
    intro h
    apply hyj
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)
  have h := firstFree_cut_zero (rotateList (-j) occupied) (start - j)
    hrotNodup hrotCard hrotZero hrotLanding
  rw [show start - j = start + -j by abel, firstFree_rotate] at h
  have hmap : (rotateList (-j) occupied).map (cutSpot 0) =
      occupied.map (cutSpot j) := by
    simp [cutSpot, rotateList, List.map_map, Function.comp_def, sub_eq_add_neg]
  rw [hmap] at h
  simpa [cutSpot, sub_eq_add_neg, add_comm] using h

theorem firstFree_ne_vacancy {n : Nat} (occupied : List (Spot n))
    (j : Spot n) (p q : Nat) (hp : 1 <= p) (hpq : p <= q) (hq : q <= n)
    (hfree : uncutSpot j q ∉ occupied) :
    firstFree n occupied (uncutSpot j p) ≠ j := by
  have orbit_apply (s : Spot n) (r : Fin (n + 1)) :
      orbitEquiv n s r = (r.val : Spot n) + s := by
    simp only [orbitEquiv, Equiv.trans_apply]
    have hfin : (ZMod.finEquiv (n + 1)).toEquiv r = (r.val : Spot n) := by
      apply ZMod.val_injective (n + 1)
      change r.val = ((r.val : Nat) : Spot n).val
      rw [ZMod.val_natCast_of_lt r.isLt]
    rw [hfin, Equiv.coe_addRight]
  let qoff : Fin (n + 1) := ⟨q - p, by omega⟩
  let joff : Fin (n + 1) := ⟨n + 1 - p, by omega⟩
  have hqorbit : orbitEquiv n (uncutSpot j p) qoff = uncutSpot j q := by
    rw [orbit_apply]
    simp only [qoff, uncutSpot]
    have hc : ((q - p : Nat) : Spot n) + (p : Spot n) = (q : Spot n) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    rw [show ((q - p : Nat) : Spot n) + (j + (p : Spot n)) =
      j + (((q - p : Nat) : Spot n) + (p : Spot n)) by abel, hc]
  have hjorbit : orbitEquiv n (uncutSpot j p) joff = j := by
    rw [orbit_apply]
    simp only [joff, uncutSpot]
    have hm : ((n + 1 : Nat) : Spot n) = 0 := ZMod.natCast_self (n + 1)
    have hc : ((n + 1 - p : Nat) : Spot n) + (p : Spot n) = 0 := by
      rw [← Nat.cast_add, show n + 1 - p + p = n + 1 by omega, hm]
    rw [show ((n + 1 - p : Nat) : Spot n) + (j + (p : Spot n)) =
      j + (((n + 1 - p : Nat) : Spot n) + (p : Spot n)) by abel, hc, add_zero]
  have hqmem : qoff ∈ freeOffsets n occupied.toFinset (uncutSpot j p) := by
    simp [freeOffsets, hqorbit, hfree]
  have hne : (freeOffsets n occupied.toFinset (uncutSpot j p)).Nonempty := ⟨qoff, hqmem⟩
  have hoffq : firstFreeOffset n occupied.toFinset (uncutSpot j p) <= qoff := by
    rw [firstFreeOffset, dif_pos hne]
    exact Finset.min'_le _ _ hqmem
  have hqj : qoff < joff := by
    change q - p < n + 1 - p
    omega
  intro hy
  have heq : firstFreeOffset n occupied.toFinset (uncutSpot j p) = joff := by
    apply (orbitEquiv n (uncutSpot j p)).injective
    calc
      orbitEquiv n (uncutSpot j p)
          (firstFreeOffset n occupied.toFinset (uncutSpot j p)) =
          firstFree n occupied (uncutSpot j p) := rfl
      _ = j := hy
      _ = orbitEquiv n (uncutSpot j p) joff := hjorbit.symm
  rw [heq] at hoffq
  exact (not_le_of_gt hqj) hoffq

theorem cut_run {n : Nat} (j : Spot n) (occupied : List (Spot n))
    (anchors : List (Spot n)) (hnodup : occupied.Nodup)
    (hcap : occupied.length + anchors.length <= n) (hjocc : j ∉ occupied)
    (hjrun : j ∉ parkFrom (oneStep n) occupied anchors) :
    D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
        (occupied.map (cutSpot j)) (anchors.map (cutSpot j)) =
        (parkFrom (oneStep n) occupied anchors).map (cutSpot j) /\
      ∀ x ∈ anchors, x ≠ j := by
  induction anchors generalizing occupied with
  | nil =>
      constructor
      · rfl
      · simp
  | cons x xs ih =>
      let y := oneStep n occupied x
      have hyfresh := firstFree_fresh n occupied x hnodup (by omega)
      have hyj : y ≠ j := by
        intro heq
        apply hjrun
        simp [parkFrom, y, heq]
      have hxj : x ≠ j := by
        intro heq
        subst x
        exact hyj (by simp [y, oneStep, firstFree_of_not_mem occupied j hjocc])
      have hstep : cutSpot j y = parkStep (occupied.map (cutSpot j)) (cutSpot j x) :=
        firstFree_cut occupied x j hnodup (by omega) hjocc (by simpa [oneStep, y] using hyj)
      have htail : j ∉ parkFrom (oneStep n) (y :: occupied) xs := by
        intro hm
        exact hjrun (by simp [parkFrom, y, hm])
      have hi := ih (y :: occupied) (List.nodup_cons.mpr ⟨hyfresh, hnodup⟩)
        (by simp only [List.length_cons] at hcap ⊢; omega)
        (by simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hyj, hjocc⟩) htail
      constructor
      · simp only [List.map_cons,
          D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom, parkFrom]
        rw [← hstep]
        change cutSpot j y ::
            D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
              (cutSpot j y :: occupied.map (cutSpot j))
              (xs.map (cutSpot j)) =
          cutSpot j y :: (parkFrom (oneStep n) (y :: occupied) xs).map (cutSpot j)
        apply congrArg (List.cons (cutSpot j y))
        simpa only [List.map_cons] using hi.1
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxj
        · exact hi.2 z hz


end D5.S3.Combinatorics.CircularTwoChoiceParkingBijection
