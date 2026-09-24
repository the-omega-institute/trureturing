/- GID: D5/S3/Combinatorics/CircularTwoChoiceParkingBijection
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CircularTwoChoiceParkingBijection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical two-choice circular parking bijections. -/

import D5.S3.Combinatorics.CircularTwoChoiceParkingOperational

/-!
# Circular two-choice parking: classical bridge

This module cuts the operational circular process at its observed vacancy,
proves the feedback-state correspondence with classical parking, and assembles
the fixed-fiber and observable global equivalences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularTwoChoiceParkingBijection

open D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata

/-- Classical length-`n` parking functions, with the supplier's literal predicate. -/
def ClassicalPF (n : Nat) :=
  {p : List Nat // p.length = n /\ IsParkingFunction p}

private def cutAnchors {n : Nat} (j : Spot n) (anchors : Anchors n) : List Nat :=
  (List.ofFn anchors).map (cutSpot j)

private theorem cutAnchors_isParking {n : Nat} (j : Spot n)
    (anchors : OneChoiceFiber n j) : IsParkingFunction (cutAnchors j anchors.1) := by
  have cut_pos (x : Spot n) (h : x ≠ j) : 1 <= cutSpot j x := by
    rw [Nat.one_le_iff_ne_zero, cutSpot, ZMod.val_ne_zero]
    exact sub_ne_zero.mpr h
  have hjrun : j ∉ oneSpots n anchors.1 :=
    (one_unique_vacancy n anchors.1 j).2 anchors.2.symm
  have hr := cut_run j [] (List.ofFn anchors.1) (by simp) (by simp) (by simp) hjrun
  constructor
  · intro p hp
    rcases List.mem_map.mp hp with ⟨x, hx, rfl⟩
    constructor
    · exact cut_pos x (hr.2 x hx)
    · rw [show (cutAnchors j anchors.1).length = n by simp [cutAnchors]]
      change (x - j).val <= n
      exact Nat.le_of_lt_succ (ZMod.val_lt (x - j))
  · intro q hq
    rw [show spots (cutAnchors j anchors.1) =
        (oneSpots n anchors.1).map (cutSpot j) by
          simpa [spots, oneSpots, cutAnchors] using hr.1] at hq
    rcases List.mem_map.mp hq with ⟨x, hx, rfl⟩
    have hxj : x ≠ j := fun heq => hjrun (heq ▸ hx)
    constructor
    · exact cut_pos x hxj
    · rw [show (cutAnchors j anchors.1).length = n by simp [cutAnchors]]
      change (x - j).val <= n
      exact Nat.le_of_lt_succ (ZMod.val_lt (x - j))

private theorem uncut_run {n : Nat} (j : Spot n) (occupied prefs : List Nat)
    (hocc : ∀ q ∈ occupied, 1 <= q /\ q <= n) (hnodup : occupied.Nodup)
    (hpref : ∀ p ∈ prefs, 1 <= p /\ p <= n)
    (hspots : ∀ q ∈
      D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom occupied prefs,
      1 <= q /\ q <= n)
    (hcap : occupied.length + prefs.length <= n) :
    parkFrom (oneStep n) (occupied.map (uncutSpot j)) (prefs.map (uncutSpot j)) =
      (D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
        occupied prefs).map (uncutSpot j) := by
  have uncut_cut_local (x : Spot n) : uncutSpot j (cutSpot j x) = x := by
    rw [uncutSpot, cutSpot, ZMod.natCast_zmod_val]
    abel
  have cut_uncut_local (p : Nat) (hp : p <= n) : cutSpot j (uncutSpot j p) = p := by
    simp only [cutSpot, uncutSpot, add_sub_cancel_left]
    exact ZMod.val_natCast_of_lt ((Nat.lt_succ_iff).2 hp)
  have uncut_injective (a b : Nat) (ha : a <= n) (hb : b <= n)
      (h : uncutSpot j a = uncutSpot j b) : a = b := by
    have hc := congrArg (cutSpot j) h
    simpa [cut_uncut_local a ha, cut_uncut_local b hb] using hc
  induction prefs generalizing occupied with
  | nil => rfl
  | cons p ps ih =>
      let q := parkStep occupied p
      have hp := hpref p (by simp)
      have hqmem : q ∈
          D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
            occupied (p :: ps) := by
        simp only [D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom,
          List.mem_cons]
        exact Or.inl rfl
      have hq : 1 <= q /\ q <= n := hspots q hqmem
      have hqfree : uncutSpot j q ∉ occupied.map (uncutSpot j) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨r, hr, heq⟩
        have hrq := uncut_injective r q (hocc r hr).2 hq.2 heq
        apply (parkStep_spec occupied p).1
        change q ∈ occupied
        exact hrq ▸ hr
      have hcircNodup : (occupied.map (uncutSpot j)).Nodup := by
        exact hnodup.map_on fun a ha b hb heq =>
          uncut_injective a b (hocc a ha).2 (hocc b hb).2 heq
      have hyj := firstFree_ne_vacancy (occupied.map (uncutSpot j)) j p q
        hp.1 (le_parkStep occupied p) hq.2 hqfree
      have hjocc : j ∉ occupied.map (uncutSpot j) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨r, hr, heq⟩
        have hz := congrArg (cutSpot j) heq
        rw [cut_uncut_local r (hocc r hr).2, cutSpot, sub_self, ZMod.val_zero] at hz
        exact (Nat.ne_of_gt (hocc r hr).1) hz
      have hcut := firstFree_cut (occupied.map (uncutSpot j)) (uncutSpot j p) j
        hcircNodup (by simpa using (show occupied.length <= n by omega))
        hjocc hyj
      have hmap : (occupied.map (uncutSpot j)).map (cutSpot j) = occupied := by
        rw [List.map_map]
        exact (List.map_congr_left fun r hr =>
          cut_uncut_local r (hocc r hr).2).trans (List.map_id occupied)
      have hstep : oneStep n (occupied.map (uncutSpot j)) (uncutSpot j p) =
          uncutSpot j q := by
        apply (uncut_cut_local _).symm.trans
        rw [oneStep, hcut, hmap, cut_uncut_local p hp.2]
      have htailSpots : ∀ r ∈
          D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
            (q :: occupied) ps, 1 <= r /\ r <= n := by
        intro r hr
        apply hspots r
        simp only [D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom,
          List.mem_cons]
        exact Or.inr hr
      have hnewOcc : ∀ r ∈ q :: occupied, 1 <= r /\ r <= n := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hq
        · exact hocc r hr
      have hi := ih (q :: occupied) hnewOcc
        (List.nodup_cons.mpr ⟨(parkStep_spec occupied p).1, hnodup⟩)
        (by intro r hr; exact hpref r (by simp [hr])) htailSpots
        (by simp only [List.length_cons] at hcap ⊢; omega)
      simp only [List.map_cons, parkFrom,
        D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom]
      rw [hstep]
      simpa [q] using hi

private def uncutAnchors {n : Nat} (j : Spot n) (p : ClassicalPF n) : Anchors n :=
  fun i => uncutSpot j (p.1.get (Fin.cast p.2.1.symm i))

private theorem uncutAnchors_empty {n : Nat} (j : Spot n) (p : ClassicalPF n) :
    oneEmpty n (uncutAnchors j p) = j := by
  have hofFn : List.ofFn (uncutAnchors j p) = p.1.map (uncutSpot j) := by
    apply List.ext_get
    · simp [p.2.1]
    · intro i hi hpi
      simp [uncutAnchors, List.get_ofFn]
  have cut_uncut_local (q : Nat) (hq : q <= n) : cutSpot j (uncutSpot j q) = q := by
    simp only [cutSpot, uncutSpot, add_sub_cancel_left]
    exact ZMod.val_natCast_of_lt ((Nat.lt_succ_iff).2 hq)
  have hpref : ∀ q ∈ p.1, 1 <= q /\ q <= n := by
    intro q hq
    simpa [p.2.1] using p.2.2.1 q hq
  have hspots : ∀ q ∈
      D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom [] p.1,
      1 <= q /\ q <= n := by
    intro q hq
    simpa [spots, p.2.1] using p.2.2.2 q hq
  have hrun := uncut_run j [] p.1 (by simp) (by simp) hpref hspots (by simp [p.2.1])
  have hj : j ∉ oneSpots n (uncutAnchors j p) := by
    rw [oneSpots, hofFn]
    have hrun' : parkFrom (oneStep n) [] (p.1.map (uncutSpot j)) =
        (D5.S0.Certificates.Combinatorics.UnitIntervalParkingFoata.parkFrom
          [] p.1).map (uncutSpot j) := by simpa using hrun
    rw [hrun']
    intro hm
    rcases List.mem_map.mp hm with ⟨q, hq, heq⟩
    have hqbound := hspots q hq
    have := congrArg (cutSpot j) heq
    rw [cut_uncut_local q hqbound.2, cutSpot, sub_self, ZMod.val_zero] at this
    exact (Nat.ne_of_gt hqbound.1) this
  exact ((one_unique_vacancy n (uncutAnchors j p) j).1 hj).symm

/-- Cutting at the vacancy and uncutting give the explicit classical bridge. -/
def oneChoiceClassicalEquiv (n : Nat) (j : Spot n) :
    OneChoiceFiber n j ≃ ClassicalPF n where
  toFun anchors := ⟨cutAnchors j anchors.1, by simp [cutAnchors],
    cutAnchors_isParking j anchors⟩
  invFun p := ⟨uncutAnchors j p, uncutAnchors_empty j p⟩
  left_inv anchors := by
    apply Subtype.ext
    have uncut_cut_local (x : Spot n) : uncutSpot j (cutSpot j x) = x := by
      rw [uncutSpot, cutSpot, ZMod.natCast_zmod_val]
      abel
    funext i
    simp [uncutAnchors, cutAnchors, uncut_cut_local]
    congr 1
  right_inv p := by
    apply Subtype.ext
    have hofFn : List.ofFn (uncutAnchors j p) = p.1.map (uncutSpot j) := by
      apply List.ext_get
      · simp [p.2.1]
      · intro i hi hpi
        simp [uncutAnchors, List.get_ofFn]
    have cut_uncut_local (q : Nat) (hq : q <= n) : cutSpot j (uncutSpot j q) = q := by
      simp only [cutSpot, uncutSpot, add_sub_cancel_left]
      exact ZMod.val_natCast_of_lt ((Nat.lt_succ_iff).2 hq)
    change cutAnchors j (uncutAnchors j p) = p.1
    rw [cutAnchors, hofFn, List.map_map]
    exact (List.map_congr_left fun q hq =>
      cut_uncut_local q (by simpa [p.2.1] using (p.2.2.1 q hq).2)).trans
        (List.map_id p.1)

/-- The source-level fixed-increment, fixed-empty-spot bijection. -/
def fixedFiberEquiv (n : Nat) (increments : IncrementMatrix n) (j : Spot n) :
    FixedActualFiber n increments j ≃ ClassicalPF n :=
  (fixedFiberOneChoiceEquiv increments j).trans (oneChoiceClassicalEquiv n j)

/-- The source-level fixed-increment, fixed-vacancy bijectivity statement. -/
theorem result (n : Nat) (hn : 1 <= n) (increments : IncrementMatrix n) (j : Spot n) :
    Function.Bijective (fixedFiberEquiv n increments j) :=
  (fixedFiberEquiv n increments j).bijective

/-- The observable global product: the classical parking function, every
original increment, and the actual process's unique empty spot. -/
def globalParkingEquiv (n : Nat) (_hn : 1 <= n) :
    ActualPreferences n ≃ ClassicalPF n × IncrementMatrix n × Spot n :=
  let observe : ActualPreferences n -> IncrementMatrix n × Spot n :=
    fun choices => (actualIncrements choices, actualEmpty n choices)
  let identifyFibers :
      (Σ data : IncrementMatrix n × Spot n,
        {choices : ActualPreferences n // observe choices = data}) ≃
        (Σ data : IncrementMatrix n × Spot n, FixedActualFiber n data.1 data.2) :=
    Equiv.sigmaCongrRight fun (data : IncrementMatrix n × Spot n) =>
      { toFun := fun choices =>
          ⟨choices.1, congrArg Prod.fst choices.2, congrArg Prod.snd choices.2⟩
        invFun := fun choices => ⟨choices.1, Prod.ext choices.2.1 choices.2.2⟩
        left_inv := fun choices => Subtype.ext rfl
        right_inv := fun choices => Subtype.ext rfl }
  (Equiv.sigmaFiberEquiv observe).symm |>.trans identifyFibers |>.trans
    (Equiv.sigmaCongrRight fun (data : IncrementMatrix n × Spot n) =>
      fixedFiberEquiv n data.1 data.2) |>.trans
    (Equiv.sigmaEquivProd (IncrementMatrix n × Spot n) (ClassicalPF n)) |>.trans
    (Equiv.prodComm (IncrementMatrix n × Spot n) (ClassicalPF n))

section GenericConsumer

variable {n : Nat} (hn : 1 <= n) (increments : IncrementMatrix n) (j : Spot n)

example (choices : FixedActualFiber n increments j) :
    (fixedFiberEquiv n increments j).symm (fixedFiberEquiv n increments j choices) = choices :=
  (fixedFiberEquiv n increments j).symm_apply_apply choices

example (classical : ClassicalPF n) :
    fixedFiberEquiv n increments j ((fixedFiberEquiv n increments j).symm classical) = classical :=
  (fixedFiberEquiv n increments j).apply_symm_apply classical

example (choices : ActualPreferences n) :
    (globalParkingEquiv n hn).symm (globalParkingEquiv n hn choices) = choices :=
  (globalParkingEquiv n hn).symm_apply_apply choices

example (data : ClassicalPF n × IncrementMatrix n × Spot n) :
    globalParkingEquiv n hn ((globalParkingEquiv n hn).symm data) = data :=
  (globalParkingEquiv n hn).apply_symm_apply data

example (choices : ActualPreferences n) :
    (globalParkingEquiv n hn choices).2.1 = actualIncrements choices := by
  rfl

example (choices : ActualPreferences n) :
    (globalParkingEquiv n hn choices).2.2 = actualEmpty n choices := by
  rfl

example (data : ClassicalPF n × IncrementMatrix n × Spot n) :
    actualIncrements ((globalParkingEquiv n hn).symm data) = data.2.1 := by
  exact ((fixedFiberEquiv n data.2.1 data.2.2).symm data.1).2.1

example (choices : ActualPreferences n) (i : Fin n) :
    (((globalParkingEquiv n hn).symm (globalParkingEquiv n hn choices)) i).anchor =
      (choices i).anchor := by
  rw [(globalParkingEquiv n hn).symm_apply_apply]

example (choices : ActualPreferences n) (i : Fin n) :
    (((globalParkingEquiv n hn).symm (globalParkingEquiv n hn choices)) i).second =
      (choices i).second := by
  rw [(globalParkingEquiv n hn).symm_apply_apply]

end GenericConsumer

#print axioms actual_prefix_fresh
#print axioms actual_unique_vacancy
#print axioms actualSpots_rotate
#print axioms actualEmpty_rotate
#print axioms fixedFiberOneChoiceEquiv
#print axioms oneChoiceClassicalEquiv
#print axioms fixedFiberEquiv
#print axioms result
#print axioms globalParkingEquiv

end D5.S3.Combinatorics.CircularTwoChoiceParkingBijection
