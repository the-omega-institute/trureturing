/- GID: D5/S3/Combinatorics/PerfectMatchings/LiteralRibbonBoundaryDelta
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/LiteralRibbonBoundaryDelta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Factors]
   utility: none
   digest: The original full-flag boundary delta classifies a marked signed ribbon. -/
import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact boundary-component delta on the full finite flag carrier, without
specifying a cut pairing as an additional input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta
noncomputable section
universe u

open Equiv FiniteEndpointPairing FiniteBandSwitch FourEndpoint OriginalCut InvolutionOrbitSplit
open scoped Classical

section
private abbrev CycleClass {X : Type*} (p : Perm X) := Quotient (Equiv.Perm.SameCycle.setoid p)

private def DirCount {X : Type*} (p : Perm X) : ℕ := Nat.card (CycleClass p)

private def Untouched {X : Type*} (p : Perm X) (S : Set X) : Set X :=
  {x | ∀ b : S, ¬ p.SameCycle b.val x}

private def untouchedSetoid {X : Type*} (p : Perm X) (S : Set X) : Setoid (Untouched p S) :=
  Setoid.comap Subtype.val (Equiv.Perm.SameCycle.setoid p)

private def inclUn {X : Type*} (p : Perm X) (S : Set X) :
    Quotient (untouchedSetoid p S) → CycleClass p :=
  Quotient.map Subtype.val (fun _ _ h => h)

private def inclRet {X : Type*} (p : Perm X) (S : Set X) (P : Perm S)
    (h : ∀ a b : S, p.SameCycle a.val b.val ↔ P.SameCycle a b) :
    CycleClass P → CycleClass p :=
  Quotient.map Subtype.val (fun a b h' => (h a b).mpr h')

private theorem splitCycles {X : Type*} (p : Perm X) (S : Set X) (P : Perm S)
    (h : ∀ a b : S, p.SameCycle a.val b.val ↔ P.SameCycle a b) :
    Nonempty (Quotient (untouchedSetoid p S) ⊕ CycleClass P ≃ CycleClass p) := by
  refine ⟨Equiv.ofBijective (Sum.elim (inclUn p S) (inclRet p S P h)) ⟨?_, ?_⟩⟩
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      have hab : p.SameCycle a.val b.val := Quotient.exact hxy
      exact congrArg Sum.inl (Quotient.sound hab)
    · obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      have hab : p.SameCycle a.val b.val := Quotient.exact hxy
      exact False.elim (a.property b hab.symm)
    · obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      have hab : p.SameCycle a.val b.val := Quotient.exact hxy
      exact False.elim (b.property a hab)
    · obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      exact congrArg Sum.inr (Quotient.sound ((h a b).mp (Quotient.exact hxy)))
  · intro z
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    by_cases hx : x ∈ Untouched p S
    · exact ⟨Sum.inl (Quotient.mk _ ⟨x,hx⟩), rfl⟩
    · change ¬ ∀ b : S, ¬ p.SameCycle b.val x at hx
      push Not at hx
      obtain ⟨b, hb⟩ := hx
      exact ⟨Sum.inr (Quotient.mk _ b), Quotient.sound hb⟩

variable {X : Type*} [Finite X]

omit [Finite X] in
private theorem powers_patch (q : Perm X) (S : Set X)
    (J : Perm S) (z : X) (hz : ∀ n : ℕ, (q ^ n) z ∉ S) (n : ℕ) :
    ((q * J.ofSubtype) ^ n) z = (q ^ n) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply,
      Perm.ofSubtype_apply_of_not_mem J (hz n), ← Perm.mul_apply, ← pow_succ']

omit [Finite X] in
private theorem powers_patch_rev (q : Perm X) (S : Set X)
    (J : Perm S) (z : X) (hz : ∀ n : ℕ, ((q * J.ofSubtype) ^ n) z ∉ S) (n : ℕ) :
    ((q * J.ofSubtype) ^ n) z = (q ^ n) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply,
      Perm.ofSubtype_apply_of_not_mem J (hz n), ih, ← Perm.mul_apply, ← pow_succ']

private theorem untouched_iff_avoids (q : Perm X) (S : Set X) (z : X) :
    z ∈ Untouched q S ↔ ∀ n : ℕ, (q ^ n) z ∉ S := by
  constructor
  · intro h n hn
    apply h ⟨(q ^ n) z, hn⟩
    exact (show q.SameCycle z ((q ^ n) z) from ⟨(n : ℤ), by simp⟩).symm
  · intro h x hx
    obtain ⟨n, hn⟩ := hx.symm.exists_nat_pow_eq
    apply h n
    simpa only [hn] using x.property

private theorem untouched_patch_iff (q : Perm X) (S : Set X)
    (J : Perm S) (z : X) :
    z ∈ Untouched (q * J.ofSubtype) S ↔ z ∈ Untouched q S := by
  simp only [untouched_iff_avoids]
  constructor
  · intro hz n
    rw [← powers_patch_rev q S J z hz n]
    exact hz n
  · intro hz n
    rw [powers_patch q S J z hz n]
    exact hz n

private def untouchedPatched (q : Perm X) (S : Set X) (J : Perm S) :
    Quotient (untouchedSetoid (q * J.ofSubtype) S) ≃ Quotient (untouchedSetoid q S) := by
  let e : Untouched (q * J.ofSubtype) S ≃ Untouched q S :=
    Equiv.subtypeEquivRight (untouched_patch_iff q S J)
  apply Quotient.congr e
  intro x y
  change (q * J.ofSubtype).SameCycle x.val y.val ↔ q.SameCycle x.val y.val
  have hp n := powers_patch q S J x.val ((untouched_iff_avoids q S x.val).mp (e x).property) n
  constructor <;> intro h
  · obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa only [zpow_natCast, hp] using hn⟩
  · obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa only [zpow_natCast, hp] using hn⟩

/-- Untouched directed-face classes are common to all attachments.  Only the
    cycles of the actual endpoint matching times the seam contribute a delta. -/
private theorem patch_count (s r : Perm X) (hs : Function.Involutive s)
    (hr : Function.Involutive r) (J : Perm {z // r z = z}) :
    DirCount (s * closeBoundary r J) =
    Nat.card (Quotient (untouchedSetoid (s * r) {z | r z = z})) +
    DirCount (endpointPairing s r hs hr * J) := by
  let S : Set X := {z | r z = z}
  let q := s * r
  let P := endpointPairing s r hs hr
  change DirCount (s * (r * J.ofSubtype)) = _ + _
  rw [← mul_assoc]
  obtain ⟨e⟩ := splitCycles (q * J.ofSubtype) S (P * J) (by
    intro a b
    simpa only [q, P, mul_assoc] using endpoint_pairing_reattach_same_cycle s r hs hr J a b)
  let ep := Equiv.sumCongr (untouchedPatched q S J).symm (Equiv.refl (CycleClass (P * J)))
  have hh := Nat.card_congr (ep.trans e)
  rw [Nat.card_sum] at hh
  exact hh.symm
end

section
private theorem dirCount_congr {A B : Type*} (e : A ≃ B) (f : Perm A) :
    DirCount (e.permCongr f) = DirCount f :=
  (Nat.card_congr (Quotient.congr e
    (fun x y => (same_cycle_perm_congr e f x y).symm))).symm

private def classLabel {p : Perm (Fin 4)} (L : Fin 4 → Fin 2)
    (h : ∀ a b, p.SameCycle a b ↔ L a = L b) : CycleClass p → Fin 2 :=
  Quotient.lift L (fun a b hr => (h a b).mp hr)

private theorem two_of_label (p : Perm (Fin 4)) (L : Fin 4 → Fin 2)
    (h : ∀ a b, p.SameCycle a b ↔ L a = L b) (hs : Function.Surjective L) :
    DirCount p = 2 := by
  let f := classLabel L h
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      exact Quotient.sound ((h a b).mpr hxy)
    · intro a
      obtain ⟨b, hb⟩ := hs a
      exact ⟨Quotient.mk _ b, hb⟩
  simpa [DirCount] using Nat.card_congr (Equiv.ofBijective f hf)

private theorem count1 : DirCount (1 : Perm (Fin 4)) = 4 := by
  let f : CycleClass (1 : Perm (Fin 4)) → Fin 4 :=
    Quotient.lift id (fun a b h => Perm.sameCycle_one.mp h)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := Quotient.exists_rep x
      obtain ⟨b, rfl⟩ := Quotient.exists_rep y
      exact Quotient.sound (Perm.sameCycle_one.mpr hxy)
    · exact fun a => ⟨Quotient.mk _ a,rfl⟩
  simpa [DirCount] using Nat.card_congr (Equiv.ofBijective f hf)

private theorem i0 : Function.Involutive J0 := by intro i; fin_cases i <;> rfl
private theorem i1 : Function.Involutive J1 := by intro i; fin_cases i <;> rfl
private theorem iK : Function.Involutive thirdPairing := by intro i; fin_cases i <;> rfl
private theorem d0 : DirCount J0 = 2 := by
  apply two_of_label J0 ![0,1,0,1]
  · intro a b
    rw [same_cycle_involutive_iff J0 i0]
    fin_cases a <;> fin_cases b <;> decide
  · intro a; fin_cases a
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
private theorem d1 : DirCount J1 = 2 := by
  apply two_of_label J1 ![0,1,1,0]
  · intro a b
    rw [same_cycle_involutive_iff J1 i1]
    fin_cases a <;> fin_cases b <;> decide
  · intro a; fin_cases a
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
private theorem dK : DirCount thirdPairing = 2 := by
  apply two_of_label thirdPairing ![0,0,1,1]
  · intro a b
    rw [same_cycle_involutive_iff thirdPairing iK]
    fin_cases a <;> fin_cases b <;> decide
  · intro a; fin_cases a
    · exact ⟨0,rfl⟩
    · exact ⟨2,rfl⟩

private theorem mul0K : J0 * thirdPairing = J1 := by ext i; fin_cases i <;> rfl
private theorem mul1K : J1 * thirdPairing = J0 := by ext i; fin_cases i <;> rfl
private theorem mulK0 : thirdPairing * J0 = J1 := by ext i; fin_cases i <;> rfl
private theorem mul10 : J1 * J0 = thirdPairing := by ext i; fin_cases i <;> rfl
private theorem mul00 : J0 * J0 = 1 := square_of_involutive _ i0
private theorem mulKK : thirdPairing * thirdPairing = 1 := square_of_involutive _ iK

private theorem finiteDelta (P : Perm (Fin 4)) (hP : Function.Involutive P)
    (hf : ∀ x, P x ≠ x) :
    (Bad P J0 ↔ DirCount (P * thirdPairing) = DirCount (P * J0) + 2) ∧
    (Good P J0 ↔ DirCount (P * thirdPairing) = DirCount (P * J0)) ∧
    (Regular P J0 ↔ DirCount (P * thirdPairing) + 2 = DirCount (P * J0)) := by
  rcases pairing_three_forms P hP hf with rfl | rfl | rfl
  all_goals
    simp only [Bad, Good, Regular, mul00, mul0K, mul1K, mulK0, mul10, mulKK,
      count1, d0, d1, dK, Perm.sameCycle_one,
      same_cycle_involutive_iff J1 i1,
      same_cycle_involutive_iff thirdPairing iK]
    decide

variable {X : Type*} [Finite X]

/-- Replacing the native across-band attachment by same-end caps changes the
directed face count by +2/0/−2 for bad/good/regular, respectively. This compares
the actual full permutations, not just the compressed four-flag orbits. -/
private theorem literal_face_delta (s r : Perm X) (hs : Function.Involutive s)
    (hr : Function.Involutive r) (hsfree : ∀ x, s x ≠ x)
    (e : Fin 4 ≃ {z // r z = z}) :
    let t := closeBoundary r (e.permCongr J0)
    let tcap := closeBoundary r (e.permCongr thirdPairing)
    let a : X := e 0
    let b : X := e 1
    (BadAt s t a b ↔ DirCount (s * tcap) = DirCount (s * t) + 2) ∧
    (GoodAt s t a b ↔ DirCount (s * tcap) = DirCount (s * t)) ∧
    (RegularAt s t a b ↔ DirCount (s * tcap) + 2 = DirCount (s * t)) := by
  let P := endpointPairing s r hs hr
  let Q := e.symm.permCongr P
  have hQ : Function.Involutive Q := by
    intro i
    simpa only [Q, Equiv.permCongr_apply, Equiv.permCongr_symm,
       Equiv.symm_symm, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
      congrArg e.symm (endpoint_pairing_involutive s r hs hr (e i))
  have hQfree : ∀ i, Q i ≠ i := by
    intro i hi
    apply endpoint_pairing_fixed_point_free s r hs hr hsfree (e i)
    simpa only [Q, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using congrArg e hi
  have hPQ : e.permCongr Q = P := e.permCongr.apply_symm_apply P
  have count (J : Perm (Fin 4)) : DirCount (s * closeBoundary r (e.permCongr J)) =
      Nat.card (Quotient (untouchedSetoid (s * r) {z | r z = z})) + DirCount (Q * J) := by
    rw [patch_count s r hs hr]
    change _ + DirCount (P * e.permCongr J) = _
    rw [← hPQ, ← e.permCongr_mul, dirCount_congr]
  have cycles (i j : Fin 4) :
      (s * closeBoundary r (e.permCongr J0)).SameCycle (e i : X) (e j : X) ↔
        (Q * J0).SameCycle i j := by
    rw [closeBoundary, endpoint_pairing_reattach_same_cycle s r hs hr]
    change (P * e.permCongr J0).SameCycle (e i) (e j) ↔ _
    rw [← hPQ, ← e.permCongr_mul]
    exact same_cycle_perm_congr e _ i j
  have hstep (i : Fin 4) :
      (s * closeBoundary r (e.permCongr J0)) (e (J0 i) : X) = s (e i : X) := by
    have hi : J0 (J0 i) = i := i0 i
    simp only [closeBoundary, Perm.mul_apply, Perm.ofSubtype_apply_coe, permCongr_apply,
      symm_apply_apply, hi, (e i).property]
  have hGood : GoodAt s (closeBoundary r (e.permCongr J0)) (e 0) (e 1) ↔ Good Q J0 :=
    cycles 0 1
  have hBad : BadAt s (closeBoundary r (e.permCongr J0)) (e 0) (e 1) ↔ Bad Q J0 := by
    unfold BadAt Bad
    rw [← hstep 0, Perm.sameCycle_apply_left, cycles]
  dsimp only
  rw [count thirdPairing, count J0]
  have h := finiteDelta Q hQ hQfree
  simp only [RegularAt, hBad, hGood, Nat.add_assoc, Nat.add_left_cancel_iff]
  exact h
end

section
variable {X : Type*} [Finite X]

/-- Physically remove the marked ribbon, stitching its two pairs of same-end
flags.  The old attachment slots stay as dummy boundary subdivisions. -/
private def capOriginal (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) : Perm X :=
  closeBoundary (cutPerm t ht a b) ((cutEquiv t ht htfree a b hinj).permCongr thirdPairing)

omit [Finite X] in
private theorem label_t (t : Perm X) (ht : Function.Involutive t)
    (a b : X) (i : Fin 4) :
    t (boundaryLabel t a b i) = boundaryLabel t a b (J0 i) := by
  fin_cases i <;> simp [boundaryLabel, J0, Perm.mul_apply, swap_apply_def, ht a, ht b]

/-- The full original physical permutation minus a chosen band has the exact
boundary-orbit delta, with no supplied cut or first-return chart. -/
private theorem original_face_delta (s t : Perm X) (hs : Function.Involutive s)
    (ht : Function.Involutive t) (hsfree : ∀ x, s x ≠ x)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) :
    let tcap := capOriginal t ht htfree a b hinj
    (BadAt s t a b ↔ DirCount (s * tcap) = DirCount (s * t) + 2) ∧
    (GoodAt s t a b ↔ DirCount (s * tcap) = DirCount (s * t)) ∧
    (RegularAt s t a b ↔ DirCount (s * tcap) + 2 = DirCount (s * t)) := by
  let r := cutPerm t ht a b
  let e := cutEquiv t ht htfree a b hinj
  have hr : Function.Involutive r := by
    intro x
    exact r.left_inv x
  have hrx (x : X) : r x = x ↔ x ∈ boundary t a b := by
    change cutFun t a b x = x ↔ _
    by_cases hx : x ∈ boundary t a b <;> simp [cutFun, hx, htfree]
  have he (i : Fin 4) : (e i : X) = boundaryLabel t a b i := rfl
  have restore : closeBoundary r (e.permCongr J0) = t := by
    ext x
    by_cases hx : r x = x
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      have hix : (e i : X) = x := congrArg Subtype.val hi
      rw [← hix, closeBoundary, Perm.mul_apply, Perm.ofSubtype_apply_coe,
        permCongr_apply, symm_apply_apply, (e (J0 i)).property,
        he, he, label_t t ht a b i]
    · have hx' : x ∉ boundary t a b := fun h => hx ((hrx x).mpr h)
      rw [closeBoundary, Perm.mul_apply,
        Perm.ofSubtype_apply_of_not_mem (p := fun z => r z = z) (e.permCongr J0) hx]
      change cutFun t a b x = t x
      simp [cutFun, hx']
  have ha : (e 0 : X) = a := rfl
  have hb : (e 1 : X) = b := rfl
  simpa only [r, e, capOriginal] using
    (show let tcap := closeBoundary r (e.permCongr thirdPairing)
       (BadAt s t a b ↔ DirCount (s * tcap) = DirCount (s * t) + 2) ∧
       (GoodAt s t a b ↔ DirCount (s * tcap) = DirCount (s * t)) ∧
       (RegularAt s t a b ↔ DirCount (s * tcap) + 2 = DirCount (s * t)) from by
       simpa only [restore, ha, hb] using literal_face_delta s r hs hr hsfree e)



omit [Finite X] in
/-- The literal deleted permutation switches bands only at the four marks.
The new pairs lie at one physical end of the old band. -/
private theorem cap_original_readout (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) :
    (∀ i, capOriginal t ht htfree a b hinj (boundaryLabel t a b i) =
      boundaryLabel t a b (thirdPairing i)) ∧
    (∀ x, x ∉ boundary t a b → capOriginal t ht htfree a b hinj x = t x) := by
  let r := cutPerm t ht a b
  let e := cutEquiv t ht htfree a b hinj
  have he (i : Fin 4) : (e i : X) = boundaryLabel t a b i := rfl
  constructor
  · intro i
    rw [← he i, ← he (thirdPairing i)]
    change closeBoundary r (e.permCongr thirdPairing) (e i : X) = _
    rw [closeBoundary, Perm.mul_apply, Perm.ofSubtype_apply_coe,
      permCongr_apply, symm_apply_apply, (e (thirdPairing i)).property]
  · intro x hx
    have hrx : r x = t x := by change cutFun t a b x = t x; simp [cutFun, hx]
    have hnr : r x ≠ x := by rw [hrx]; exact htfree x
    change closeBoundary r (e.permCongr thirdPairing) x = t x
    rw [closeBoundary, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem
      (p := fun z => r z = z) (e.permCongr thirdPairing) hnr, hrx]

omit [Finite X] in
private theorem cap_original_perfect (t : Perm X) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a b : X)
    (hinj : Function.Injective (boundaryLabel t a b)) :
    Function.Involutive (capOriginal t ht htfree a b hinj) ∧
      ∀ x, capOriginal t ht htfree a b hinj x ≠ x := by
  let tc := capOriginal t ht htfree a b hinj
  have hread := cap_original_readout t ht htfree a b hinj
  have hK : Function.Involutive thirdPairing := by intro x; fin_cases x <;> rfl
  have hKf : ∀ x : Fin 4, thirdPairing x ≠ x := by decide
  have hstable : ∀ x, t x ∈ boundary t a b → x ∈ boundary t a b := by
    intro x hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨J0 i, (label_t t ht a b i).symm.trans (by rw [hi, ht x])⟩
  constructor
  · intro x
    by_cases hx : x ∈ boundary t a b
    · obtain ⟨i, rfl⟩ := hx
      change tc (tc (boundaryLabel t a b i)) = _
      rw [hread.1 i, hread.1, hK]
    · change tc (tc x) = x
      rw [hread.2 x hx, hread.2 (t x) (fun h => hx (hstable x h)), ht]
  · intro x
    by_cases hx : x ∈ boundary t a b
    · obtain ⟨i, rfl⟩ := hx
      change tc (boundaryLabel t a b i) ≠ _
      rw [hread.1]
      exact fun h => hKf i (hinj h)
    · change tc x ≠ x
      rw [hread.2 x hx]
      exact htfree x
end

section
variable {X : Type*}

/-- The connected matching-component relation on physical flags. -/
private def boundarySetoid (s t : Perm X) (hs : Function.Involutive s)
    (ht : Function.Involutive t) : Setoid X where
  r := Connected s t
  iseqv := ⟨fun _ => .refl, (by
      intro x y h
      induction h with
      | refl => exact .refl
      | @tail v w h hlast ih =>
        apply Relation.ReflTransGen.trans _ ih
        apply Relation.ReflTransGen.single
        rcases hlast with h' | h'
        · left; rw [← h', hs]
        · right; rw [← h', ht]),
    fun h g => h.trans g⟩

private abbrev BoundaryClass (s t : Perm X) (hs : Function.Involutive s)
    (ht : Function.Involutive t) := Quotient (boundarySetoid s t hs ht)

private def forget (s t : Perm X) (hs : Function.Involutive s)
    (ht : Function.Involutive t) : CycleClass (s * t) → BoundaryClass s t hs ht :=
  Quotient.map id (fun x y h => (connected_iff_rotation_orbits s t hs ht x y).mpr (.inl h))

/-- Each alternating matching component is literally two distinct orientations
of the same boundary circle. No orientation of the whole surface is needed. -/
private theorem two_directions (s t : Perm X) (hs : Function.Involutive s)
    (ht : Function.Involutive t) (hsf : ∀ x, s x ≠ x) (htf : ∀ x, t x ≠ x) :
    Nonempty (BoundaryClass s t hs ht × Bool ≃ CycleClass (s * t)) := by
  let repr (C : BoundaryClass s t hs ht) : X := (Quotient.exists_rep C).choose
  have hrepr (C : BoundaryClass s t hs ht) :
      Quotient.mk (boundarySetoid s t hs ht) (repr C) = C :=
    (Quotient.exists_rep C).choose_spec
  let g (p : BoundaryClass s t hs ht × Bool) : CycleClass (s * t) :=
    Quotient.mk _ (if p.2 then s (repr p.1) else repr p.1)
  have hg1 (C : BoundaryClass s t hs ht) (b : Bool) :
      forget s t hs ht (g (C,b)) = C := by
    cases b
    · exact hrepr C
    · trans Quotient.mk (boundarySetoid s t hs ht) (repr C)
      · apply Eq.symm
        apply Quotient.sound
        exact Relation.ReflTransGen.single (.inl rfl)
      · exact hrepr C
  have hcross (x : X) : ¬ (s*t).SameCycle x (s x) :=
    (fixedPointFree_iff_rotation_separation s t hs ht).mp ⟨hsf,htf⟩ x
  refine ⟨Equiv.ofBijective g ⟨?_,?_⟩⟩
  · intro ⟨C,b⟩ ⟨D,c⟩ hh
    have he : C = D := (hg1 C b).symm.trans ((congrArg (forget s t hs ht) hh).trans (hg1 D c))
    subst D
    cases b <;> cases c
    · rfl
    · exact False.elim (hcross _ (Quotient.exact hh))
    · have hr : (s*t).SameCycle (s (repr C)) (repr C) := Quotient.exact hh
      exact False.elim (hcross _ hr.symm)
    · rfl
  · intro z
    obtain ⟨x,rfl⟩ := Quotient.exists_rep z
    let C : BoundaryClass s t hs ht := Quotient.mk _ x
    have hc : Connected s t (repr C) x := Quotient.exact (hrepr C)
    rcases (connected_iff_rotation_orbits s t hs ht _ _).mp hc with h | h
    · exact ⟨(C,false), Quotient.sound h⟩
    · exact ⟨(C,true), Quotient.sound h⟩


private theorem dirCount_twice_boundary (s t : Perm X) (hs : Function.Involutive s)
    (ht : Function.Involutive t) (hsf : ∀ x, s x ≠ x) (htf : ∀ x, t x ≠ x) :
    DirCount (s*t) = 2 * Nat.card (BoundaryClass s t hs ht) := by
  obtain ⟨e⟩ := two_directions s t hs ht hsf htf
  have h := (Nat.card_congr e).symm
  rw [Nat.card_prod] at h
  simpa [DirCount, Nat.mul_comm] using h
end

/-- An original finite ribbon flag system with a marked band.
The flags `a,b` lie at one end of the marked band; the other end is `t a,t b`.
The four attachment flags are distinct. -/
structure MarkedRibbon where
  X : Type u
  finite : Finite X
  s : Perm X
  t : Perm X
  hs : Function.Involutive s
  ht : Function.Involutive t
  hsfree : ∀ x, s x ≠ x
  htfree : ∀ x, t x ≠ x
  a : X
  b : X
  distinctFlags : Function.Injective (boundaryLabel t a b)

/-- The number of undirected alternating components after deletion of the marked
band by same-end caps, minus the original number. Both counts use the original
flag carrier. -/
def boundaryDelta (R : MarkedRibbon.{u}) : ℤ :=
  let tcap := capOriginal R.t R.ht R.htfree R.a R.b R.distinctFlags
  let H := (cap_original_perfect R.t R.ht R.htfree R.a R.b R.distinctFlags).1
  (Nat.card (BoundaryClass R.s tcap R.hs H) : ℤ) -
    (Nat.card (BoundaryClass R.s R.t R.hs R.ht) : ℤ)

/-- On the untouched original carrier, the signed boundary delta
is +1, 0, or −1 exactly for a bad, good, or regular marked band, respectively.
The reattachment is computed from the actual original band involution. -/
theorem original_boundary_delta (R : MarkedRibbon.{u}) :
    let observed := boundaryDelta R
    (BadAt R.s R.t R.a R.b ↔ observed = 1) ∧
    (GoodAt R.s R.t R.a R.b ↔ observed = 0) ∧
    (RegularAt R.s R.t R.a R.b ↔ observed = -1) := by
  let _ : Finite R.X := R.finite
  let tcap := capOriginal R.t R.ht R.htfree R.a R.b R.distinctFlags
  obtain ⟨hi,hf⟩ := cap_original_perfect R.t R.ht R.htfree R.a R.b R.distinctFlags
  have he := original_face_delta R.s R.t R.hs R.ht R.hsfree R.htfree R.a R.b R.distinctFlags
  dsimp only at he ⊢
  rw [dirCount_twice_boundary R.s R.t R.hs R.ht R.hsfree R.htfree,
    dirCount_twice_boundary R.s tcap R.hs hi R.hsfree hf] at he
  let n : ℕ := Nat.card (BoundaryClass R.s R.t R.hs R.ht)
  let nc : ℕ := Nat.card (BoundaryClass R.s tcap R.hs hi)
  change (BadAt R.s R.t R.a R.b ↔ 2*nc=2*n+2) ∧
    (GoodAt R.s R.t R.a R.b ↔ 2*nc=2*n) ∧
    (RegularAt R.s R.t R.a R.b ↔ 2*nc+2=2*n) at he
  change (BadAt R.s R.t R.a R.b ↔ (nc : ℤ)-(n : ℤ)=1) ∧
    (GoodAt R.s R.t R.a R.b ↔ (nc : ℤ)-(n : ℤ)=0) ∧
    (RegularAt R.s R.t R.a R.b ↔ (nc : ℤ)-(n : ℤ)=-1)
  refine ⟨he.1.trans ?_, he.2.1.trans ?_, he.2.2.trans ?_⟩ <;> constructor <;> intro h <;> omega

end
end D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta
