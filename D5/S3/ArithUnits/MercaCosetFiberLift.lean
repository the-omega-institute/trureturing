/- GID: D5/S3/ArithUnits/MercaCosetFiberLift
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MercaCosetFiberLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime unit-coset lifts have an exact least-residue first moment. -/

import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.ArithUnits.MercaCosetFiberLift
open scoped BigOperators Pointwise
noncomputable section

/-- The actual left coset, represented as a finite set of units. -/
def cosetFinset {n : ℕ} [NeZero n]
    (K : Subgroup (ZMod n)ˣ) (c : (ZMod n)ˣ) : Finset (ZMod n)ˣ := by
  classical
  exact Finset.univ.filter (fun u => c⁻¹ * u ∈ K)

/-- Reduction on units along the divisibility of the two moduli. -/
def reduceUnits (N ell : ℕ) : (ZMod (N * ell))ˣ →* (ZMod N)ˣ :=
  ZMod.unitsMap (show N ∣ N * ell from ⟨ell, rfl⟩)

/-- The preimage of an actual finite set of units under reduction. -/
def liftedFinset (N ell : ℕ) [NeZero (N * ell)]
    (C : Finset (ZMod N)ˣ) : Finset (ZMod (N * ell))ˣ := by
  classical
  exact Finset.univ.filter (fun u => reduceUnits N ell u ∈ C)

/-- The uncentered sum of least nonnegative representatives, in the rationals. -/
def moment (n : ℕ) (C : Finset (ZMod n)ˣ) : ℚ :=
  ∑ u ∈ C, (((u : ZMod n).val : ℕ) : ℚ)

/-- The rational deviation from the subgroup-sized center. -/
def deviation (n : ℕ) (K : Subgroup (ZMod n)ˣ)
    (C : Finset (ZMod n)ˣ) : ℚ :=
  moment n C - (n : ℚ) * (Nat.card K : ℚ) / 2

private abbrev Fiber {N : ℕ} (ell : ℕ) (C : Finset (ZMod N)ˣ) := C × Fin ell

private def block {N ell : ℕ} {C : Finset (ZMod N)ˣ} (p : Fiber ell C) : ℕ :=
  ((p.1.1 : ZMod N).val) + N * p.2.val

private lemma block_lt {N ell : ℕ} [NeZero N] {C : Finset (ZMod N)ˣ}
    (p : Fiber ell C) : block p < N * ell := by
  have hr := ZMod.val_lt (p.1.1 : ZMod N)
  have ht := p.2.isLt
  have hN := NeZero.pos N
  dsimp [block]
  nlinarith

private lemma block_cast {N ell : ℕ} [NeZero N] {C : Finset (ZMod N)ˣ}
    (p : Fiber ell C) : (block p : ZMod N) = p.1.1 := by
  simp [block, Nat.cast_add, Nat.cast_mul]

private lemma block_coprime {N ell : ℕ} [NeZero N] {C : Finset (ZMod N)ˣ}
    (p : Fiber ell C) : Nat.Coprime (block p) N := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  rw [block_cast]
  exact p.1.1.isUnit

private lemma block_injective {N ell : ℕ} [NeZero N] {C : Finset (ZMod N)ˣ} :
    Function.Injective (@block N ell C) := by
  intro p q h
  have he : ((p.1.1 : ZMod N), p.2.val) = ((q.1.1 : ZMod N), q.2.val) :=
    (Nat.residueClassesEquiv N).symm.injective h
  apply Prod.ext
  · apply Subtype.ext
    exact Units.ext (congrArg Prod.fst he)
  · exact Fin.ext (congrArg Prod.snd he)

private lemma reduce_coe {N ell : ℕ} [NeZero (N * ell)]
    (v : (ZMod (N * ell))ˣ) :
    (reduceUnits N ell v : ZMod N) = ((v : ZMod (N * ell)).val : ZMod N) := by
  rw [reduceUnits, ZMod.unitsMap_val, ZMod.cast_eq_val]

private lemma reduce_val {N ell : ℕ} [NeZero (N * ell)]
    (v : (ZMod (N * ell))ˣ) :
    (reduceUnits N ell v : ZMod N).val = (v : ZMod (N * ell)).val % N := by
  rw [reduce_coe, ZMod.val_natCast]

private abbrev Good {N : ℕ} (ell : ℕ) (C : Finset (ZMod N)ˣ) :=
  {p : Fiber ell C // ¬ell ∣ block p}
private abbrev Bad {N : ℕ} (ell : ℕ) (C : Finset (ZMod N)ˣ) :=
  {p : Fiber ell C // ell ∣ block p}

private def goodMap {N ell : ℕ} [NeZero N] [NeZero (N * ell)]
    (hell : Nat.Prime ell) {C : Finset (ZMod N)ˣ} (p : Good ell C) :
    liftedFinset N ell C := by
  classical
  have hq : Nat.Coprime (block p.1) (N * ell) :=
    (block_coprime p.1).mul_right ((hell.coprime_iff_not_dvd.mpr p.2).symm)
  let v := ZMod.unitOfCoprime (block p.1) hq
  have hv : reduceUnits N ell v = p.1.1.1 := by
    apply Units.ext
    rw [reduce_coe, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt (block_lt p.1)]
    exact block_cast p.1
  exact ⟨v, by simpa [liftedFinset, hv] using p.1.1.2⟩

private lemma goodMap_val {N ell : ℕ} [NeZero N] [NeZero (N * ell)]
    (hell : Nat.Prime ell) {C : Finset (ZMod N)ˣ} (p : Good ell C) :
    ((goodMap hell p).1 : ZMod (N * ell)).val = block p.1 := by
  exact ZMod.val_natCast_of_lt (block_lt p.1)

private def goodInv {N ell : ℕ} [NeZero N] [NeZero (N * ell)]
    (hell : Nat.Prime ell) {C : Finset (ZMod N)ˣ} (v : liftedFinset N ell C) :
    Good ell C := by
  classical
  let r := (v.1 : ZMod (N * ell)).val
  have ht : r / N < ell := (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr
    (by simpa [r, mul_comm] using ZMod.val_lt (v.1 : ZMod (N * ell)))
  let p : Fiber ell C :=
    (⟨reduceUnits N ell v.1, by simpa [liftedFinset] using v.2⟩, ⟨r / N, ht⟩)
  have hp : block p = r := by
    dsimp [block, p]
    rw [reduce_val]
    exact Nat.mod_add_div r N
  have hc : Nat.Coprime ell r :=
    ((ZMod.val_coe_unit_coprime v.1).of_dvd_right (dvd_mul_left ell N)).symm
  exact ⟨p, by rw [hp]; exact hell.coprime_iff_not_dvd.mp hc⟩

private lemma goodInv_block {N ell : ℕ} [NeZero N] [NeZero (N * ell)]
    (hell : Nat.Prime ell) {C : Finset (ZMod N)ˣ} (v : liftedFinset N ell C) :
    block (goodInv hell v).1 = (v.1 : ZMod (N * ell)).val := by
  dsimp [goodInv, block]
  rw [reduce_val]
  exact Nat.mod_add_div _ _

/-- Each block not divisible by the new prime is exactly one lifted unit. -/
private def goodLiftEquiv {N ell : ℕ} [NeZero N] [NeZero (N * ell)]
    (hell : Nat.Prime ell) (C : Finset (ZMod N)ˣ) :
    Good ell C ≃ liftedFinset N ell C where
  toFun := goodMap hell
  invFun := goodInv hell
  left_inv p := by
    apply Subtype.ext
    apply block_injective
    rw [goodInv_block, goodMap_val]
  right_inv v := by
    apply Subtype.ext
    apply Units.ext
    apply ZMod.val_injective
    rw [goodMap_val, goodInv_block]

private def removedMap {N ell : ℕ} [NeZero N] (hell : Nat.Prime ell)
    (hcop : Nat.Coprime ell N) (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ)
    (y : cosetFinset K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c)) :
    Bad ell (cosetFinset K c) := by
  classical
  let e := ZMod.unitOfCoprime ell hcop
  let z := ell * (y.1 : ZMod N).val
  have hz : z < N * ell := by
    dsimp [z]
    nlinarith [ZMod.val_lt (y.1 : ZMod N), hell.pos]
  have hu : e * y.1 ∈ cosetFinset K c := by
    simpa [cosetFinset, e, mul_assoc, mul_comm, mul_left_comm] using y.2
  have hr : (e * y.1 : ZMod N).val = z % N := by
    have he : (e * y.1 : ZMod N) = (z : ZMod N) := by
      simp [e, z, Nat.cast_mul]
    rw [he, ZMod.val_natCast]
  let p : Fiber ell (cosetFinset K c) :=
    (⟨e * y.1, hu⟩, ⟨z / N, (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr
      (by simpa [mul_comm] using hz)⟩)
  have hp : block p = z := by
    dsimp [block, p]
    rw [hr]
    exact Nat.mod_add_div z N
  exact ⟨p, by rw [hp]; exact dvd_mul_right ell (y.1 : ZMod N).val⟩

private lemma removedMap_block {N ell : ℕ} [NeZero N] (hell : Nat.Prime ell)
    (hcop : Nat.Coprime ell N) (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ)
    (y : cosetFinset K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c)) :
    block (removedMap hell hcop K c y).1 = ell * (y.1 : ZMod N).val := by
  dsimp [removedMap, block]
  have he : (ell : ZMod N) * (y.1 : ZMod N) =
      ((ell * (y.1 : ZMod N).val : ℕ) : ZMod N) := by
    simp [Nat.cast_mul]
  rw [he, ZMod.val_natCast]
  exact Nat.mod_add_div _ _

private def removedInv {N ell : ℕ} [NeZero N]
    (hcop : Nat.Coprime ell N) (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ)
    (p : Bad ell (cosetFinset K c)) :
    cosetFinset K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c) := by
  classical
  let a := block p.1 / ell
  have ha : ell * a = block p.1 := Nat.mul_div_cancel' p.2
  have hc : Nat.Coprime a N :=
    (ha.symm ▸ block_coprime p.1).of_dvd_left (dvd_mul_left a ell)
  let y := ZMod.unitOfCoprime a hc
  have hy : ZMod.unitOfCoprime ell hcop * y = p.1.1.1 := by
    apply Units.ext
    simpa [y, ← Nat.cast_mul, ha] using block_cast p.1
  refine ⟨y, ?_⟩
  have hm := p.1.1.2
  rw [← hy] at hm
  simpa [cosetFinset, mul_assoc, mul_comm, mul_left_comm] using hm

private lemma removedInv_val {N ell : ℕ} [NeZero N] (hell : Nat.Prime ell)
    (hcop : Nat.Coprime ell N) (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ)
    (p : Bad ell (cosetFinset K c)) :
    ((removedInv hcop K c p).1 : ZMod N).val = block p.1 / ell := by
  have he := hell.pos
  have hb := block_lt p.1
  apply ZMod.val_natCast_of_lt
  exact (Nat.div_lt_iff_lt_mul he).mpr (by simpa [mul_comm] using hb)

/-- The removed multiples are precisely prime-scaled representatives of the inverse coset. -/
private def removedMultipleEquiv {N ell : ℕ} [NeZero N] (hell : Nat.Prime ell)
    (hcop : Nat.Coprime ell N) (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ) :
    cosetFinset K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c) ≃
      Bad ell (cosetFinset K c) where
  toFun := removedMap hell hcop K c
  invFun := removedInv hcop K c
  left_inv y := by
    apply Subtype.ext
    apply Units.ext
    apply ZMod.val_injective
    rw [removedInv_val hell, removedMap_block, Nat.mul_div_cancel_left _ hell.pos]
  right_inv p := by
    apply Subtype.ext
    apply block_injective
    rw [removedMap_block, removedInv_val hell]
    exact Nat.mul_div_cancel' p.2

private lemma coset_card {N : ℕ} [NeZero N]
    (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ) :
    (cosetFinset K c).card = Nat.card K := by
  classical
  let e : cosetFinset K c ≃ (c • (K : Set (ZMod N)ˣ) : Set (ZMod N)ˣ) :=
    Equiv.subtypeEquivRight (fun u => by simp [cosetFinset, mem_leftCoset_iff])
  have h := Nat.card_congr (e.trans (Subgroup.leftCosetEquivSubgroup c))
  simpa [Nat.card_eq_fintype_card] using h

private lemma sum_fin_rat (ell : ℕ) (hell : 0 < ell) :
    (∑ t : Fin ell, (t.val : ℚ)) = (ell : ℚ) * ((ell : ℚ) - 1) / 2 := by
  have hn := Finset.sum_range_id_mul_two ell
  have hq : (∑ t ∈ Finset.range ell, (t : ℚ)) * 2 =
      (ell : ℚ) * ((ell : ℚ) - 1) := by
    have hc := congrArg (fun n : ℕ => (n : ℚ)) hn
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat,
      Nat.cast_sub (show 1 ≤ ell from hell), Nat.cast_one] using hc
  rw [Fin.sum_univ_eq_sum_range]
  linarith

private lemma sum_representatives {N : ℕ} (C : Finset (ZMod N)ˣ) :
    (∑ u : C, ((u.1 : ZMod N).val : ℚ)) = moment N C := by
  classical
  exact Finset.sum_coe_sort C (fun u : (ZMod N)ˣ => ((u : ZMod N).val : ℚ))

private lemma total_moment {N ell : ℕ} [NeZero N]
    (hell : Nat.Prime ell) (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ) :
    (∑ p : Fiber ell (cosetFinset K c), (block p : ℚ)) =
      (ell : ℚ) * moment N (cosetFinset K c) +
      (N : ℚ) * (Nat.card K : ℚ) * ell * ((ell : ℚ) - 1) / 2 := by
  classical
  have hi (u : cosetFinset K c) :
      (∑ t : Fin ell, (block (u, t) : ℚ)) =
      (ell : ℚ) * ((u.1 : ZMod N).val : ℚ) +
        (N : ℚ) * ((ell : ℚ) * ((ell : ℚ) - 1) / 2) := by
    simp only [block, Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_fin_rat ell hell.pos]
  rw [Fintype.sum_prod_type]
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, coset_card K c,
    nsmul_eq_mul, sum_representatives]
  change (ell : ℚ) * moment N (cosetFinset K c) +
      (Nat.card K : ℚ) * ((N : ℚ) * ((ell : ℚ) * ((ell : ℚ) - 1) / 2)) = _
  ring

set_option maxHeartbeats 1000000 in

private lemma uncentered_moment {N ell : ℕ} [NeZero N] [NeZero (N * ell)]
    (hell : Nat.Prime ell) (hcop : Nat.Coprime ell N)
    (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ) :
    moment (N * ell) (liftedFinset N ell (cosetFinset K c)) =
      (ell : ℚ) * moment N (cosetFinset K c) +
        (N : ℚ) * (Nat.card K : ℚ) * ell * ((ell : ℚ) - 1) / 2 -
        (ell : ℚ) * moment N (cosetFinset K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c)) := by
  classical
  have hg : (∑ p : Good ell (cosetFinset K c), (block p.1 : ℚ)) =
      moment (N * ell) (liftedFinset N ell (cosetFinset K c)) := by
    calc
      _ = ∑ v : liftedFinset N ell (cosetFinset K c),
          ((v.1 : ZMod (N * ell)).val : ℚ) :=
        Fintype.sum_equiv (goodLiftEquiv hell _) _ _ (fun p => by
          change (block p.1 : ℚ) = (((goodMap hell p).1 : ZMod (N * ell)).val : ℚ)
          rw [goodMap_val])
      _ = _ := sum_representatives _
  have hb : (∑ p : Bad ell (cosetFinset K c), (block p.1 : ℚ)) =
      (ell : ℚ) * moment N (cosetFinset K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c)) := by
    calc
      _ = ∑ y : cosetFinset K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c),
          (ell : ℚ) * ((y.1 : ZMod N).val : ℚ) := by
        symm
        exact Fintype.sum_equiv (removedMultipleEquiv hell hcop K c) _ _
          (fun y => by
            change (ell : ℚ) * ((y.1 : ZMod N).val : ℚ) =
              (block (removedMap hell hcop K c y).1 : ℚ)
            rw [removedMap_block, Nat.cast_mul])
      _ = _ := by rw [← Finset.mul_sum, sum_representatives]
  have hp := Fintype.sum_subtype_add_sum_subtype
    (fun p : Fiber ell (cosetFinset K c) => ell ∣ block p)
    (fun p => (block p : ℚ))
  rw [hb, hg, total_moment hell K c] at hp
  linarith

private lemma lifted_card {N ell : ℕ} [NeZero N] [NeZero (N * ell)]
    (hell : Nat.Prime ell) (hcop : Nat.Coprime ell N)
    (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ) :
    (liftedFinset N ell (cosetFinset K c)).card = Nat.card K * (ell - 1) := by
  classical
  have hg := Fintype.card_congr (goodLiftEquiv hell (cosetFinset K c))
  have hb := Fintype.card_congr (removedMultipleEquiv hell hcop K c)
  have hp := Fintype.card_subtype_compl
    (fun p : Fiber ell (cosetFinset K c) => ell ∣ block p)
  change Fintype.card (Good ell (cosetFinset K c)) =
    Fintype.card (Fiber ell (cosetFinset K c)) -
    Fintype.card (Bad ell (cosetFinset K c)) at hp
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    coset_card K c, coset_card K ((ZMod.unitOfCoprime ell hcop)⁻¹ * c)] at hg hb hp
  rw [← hg, hp, ← hb, Nat.mul_sub_left_distrib, mul_one]

/-- The complete uniform prime-lift identity on actual unit cosets. -/
theorem result
    (N ell : ℕ) (hN : 1 < N) (hell : Nat.Prime ell)
    (hcop : Nat.Coprime ell N)
    (K : Subgroup (ZMod N)ˣ) (c : (ZMod N)ˣ) :
    letI : NeZero N := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)⟩
    letI : NeZero (N * ell) :=
      ⟨Nat.mul_ne_zero (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)) hell.ne_zero⟩
    let pi := reduceUnits N ell
    let H : Subgroup (ZMod (N * ell))ˣ := K.comap pi
    let e : (ZMod N)ˣ := ZMod.unitOfCoprime ell hcop
    let C := cosetFinset K c
    let C' := cosetFinset K (e⁻¹ * c)
    let L := liftedFinset N ell C
    Nat.card H = Nat.card K * (ell - 1) ∧
    L.card = Nat.card K * (ell - 1) ∧
    (∃ d : (ZMod (N * ell))ˣ,
      pi d = c ∧ L = cosetFinset H d) ∧
    moment (N * ell) L =
      (ell : ℚ) * moment N C +
        (N : ℚ) * (Nat.card K : ℚ) * (ell : ℚ) * ((ell : ℚ) - 1) / 2 -
        (ell : ℚ) * moment N C' ∧
    deviation (N * ell) H L =
      (ell : ℚ) * (deviation N K C - deviation N K C') ∧
    deviation (N * ell) H L =
      (ell : ℚ) * (moment N C - moment N C') := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)⟩
  letI : NeZero (N * ell) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)) hell.ne_zero⟩
  dsimp only
  let pi := reduceUnits N ell
  let H : Subgroup (ZMod (N * ell))ˣ := K.comap pi
  have hcard := lifted_card hell hcop K c
  have hH : Nat.card H = Nat.card K * (ell - 1) := by
    let eH : liftedFinset N ell (cosetFinset K 1) ≃ H :=
      Equiv.subtypeEquivRight (fun v => by simp [liftedFinset, cosetFinset, H, pi])
    have h := Nat.card_congr eH
    simpa [Nat.card_eq_fintype_card, lifted_card hell hcop K 1] using h.symm
  have hcoset : ∃ d : (ZMod (N * ell))ˣ,
      pi d = c ∧ liftedFinset N ell (cosetFinset K c) = cosetFinset H d := by
    obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective (show N ∣ N * ell from ⟨ell, rfl⟩) c
    refine ⟨d, hd, ?_⟩
    ext v
    have hd' : reduceUnits N ell d = c := hd
    simp [cosetFinset, liftedFinset, H, pi, ← hd', map_inv, map_mul]
  have hm := uncentered_moment hell hcop K c
  change Nat.card (K.comap (reduceUnits N ell)) = Nat.card K * (ell - 1) at hH
  refine ⟨hH, hcard, hcoset, hm, ?_, ?_⟩ <;>
    simp only [deviation, hH, hm, Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ ell from hell.one_lt.le), Nat.cast_one] <;> ring

end
end D5.S3.ArithUnits.MercaCosetFiberLift
