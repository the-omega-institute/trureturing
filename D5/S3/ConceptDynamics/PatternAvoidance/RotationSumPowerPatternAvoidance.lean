/- GID: D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Powered rotation sums avoid 2143 iff at most one block stays nonidentity. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.End
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

open scoped BigOperators

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.PatternAvoidance.RotationSumPowerPatternAvoidance

private abbrev Position (d : List Nat) :=
  Sigma fun i : Fin d.length => Fin (d.get i)

private def rotVal (m r x : Nat) : Nat :=
  (x + r % m) % m

private lemma rotVal_lt {m r x : Nat} (hm : 0 < m) : rotVal m r x < m := by
  exact Nat.mod_lt _ hm

private lemma rotVal_eq_of_lt_cut {m r x : Nat} (hm : 0 < m) (_hx : x < m)
    (hcut : x < m - r % m) : rotVal m r x = x + r % m := by
  unfold rotVal
  rw [Nat.mod_eq_of_lt]
  have hk := Nat.mod_lt r hm
  omega

private lemma rotVal_eq_of_cut_le {m r x : Nat} (hm : 0 < m) (hx : x < m)
    (hcut : m - r % m <= x) : rotVal m r x = x + r % m - m := by
  unfold rotVal
  have hk := Nat.mod_lt r hm
  have hge : m <= x + r % m := by omega
  rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt]
  omega

private lemma rotVal_descent_iff {m r x y : Nat} (hm : 0 < m) (hx : x < m)
    (hy : y < m) (hxy : x < y) :
    rotVal m r y < rotVal m r x <->
      x < m - r % m ∧ m - r % m <= y := by
  constructor
  · intro hdesc
    by_cases hxcut : x < m - r % m
    · refine ⟨hxcut, ?_⟩
      by_contra hycut
      have hylt : y < m - r % m := by omega
      rw [rotVal_eq_of_lt_cut hm hx hxcut, rotVal_eq_of_lt_cut hm hy hylt] at hdesc
      omega
    · have hxge : m - r % m <= x := by omega
      have hyge : m - r % m <= y := by omega
      rw [rotVal_eq_of_cut_le hm hx hxge, rotVal_eq_of_cut_le hm hy hyge] at hdesc
      omega
  · rintro ⟨hxcut, hycut⟩
    rw [rotVal_eq_of_lt_cut hm hx hxcut, rotVal_eq_of_cut_le hm hy hycut]
    have hk := Nat.mod_lt r hm
    omega

private lemma rotVal_descent_not_dvd {m r x y : Nat} (_hm : 0 < m) (hx : x < m)
    (hy : y < m) (hxy : x < y) (hdesc : rotVal m r y < rotVal m r x) :
    ¬m ∣ r := by
  intro hdvd
  have hmod : r % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  simp only [rotVal, hmod, Nat.add_zero, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hdesc
  omega

private lemma rotVal_no_two_descents {m r a b c e : Nat} (hm : 0 < m)
    (ha : a < m) (hb : b < m) (hc : c < m) (he : e < m)
    (hab : a < b) (hbc : b < c) (hce : c < e)
    (hba : rotVal m r b < rotVal m r a)
    (hec : rotVal m r e < rotVal m r c) : False := by
  have h₁ := (rotVal_descent_iff hm ha hb hab).mp hba
  have h₂ := (rotVal_descent_iff hm hc he hce).mp hec
  omega

private lemma exists_rotVal_descent {m r : Nat} (hm : 0 < m) (hbad : ¬m ∣ r) :
    ∃ x y, x < m ∧ y < m ∧ x < y ∧ rotVal m r y < rotVal m r x := by
  have hklt : r % m < m := Nat.mod_lt r hm
  have hkpos : 0 < r % m := by
    rw [Nat.pos_iff_ne_zero]
    exact fun hzero => hbad (Nat.dvd_iff_mod_eq_zero.mpr hzero)
  refine ⟨0, m - r % m, hm, ?_, ?_, ?_⟩
  · exact Nat.sub_lt hm hkpos
  · exact Nat.sub_pos_of_lt hklt
  · rw [rotVal_eq_of_lt_cut hm hm (Nat.sub_pos_of_lt hklt)]
    rw [rotVal_eq_of_cut_le hm (Nat.sub_lt hm hkpos) le_rfl]
    simp only [Nat.zero_add]
    rw [Nat.sub_add_cancel (Nat.le_of_lt hklt), Nat.sub_self]
    exact hkpos

private def Before {d : List Nat} (p q : Position d) : Prop :=
  p.1.val < q.1.val ∨ (p.1.val = q.1.val ∧ p.2.val < q.2.val)

private def rotationSumPower (d : List Nat) (r : Nat) (p : Position d) : Position d :=
  ⟨p.1, ⟨rotVal (d.get p.1) r p.2.val,
    rotVal_lt (Nat.zero_lt_of_lt p.2.isLt)⟩⟩

private def TaggedContains2143 {d : List Nat} (f : Position d -> Position d) : Prop :=
  ∃ a b c e,
    Before a b ∧ Before b c ∧ Before c e ∧
    Before (f b) (f a) ∧ Before (f a) (f e) ∧ Before (f e) (f c)

private def badBlocks (d : List Nat) (r : Nat) : Finset (Fin d.length) :=
  Finset.univ.filter fun i => ¬d.get i ∣ r

private lemma before_block_le {d : List Nat} {p q : Position d} (h : Before p q) :
    p.1.val <= q.1.val := by
  rcases h with h | h
  · omega
  · omega

private lemma descent_same_block {d : List Nat} {r : Nat} {p q : Position d}
    (hpq : Before p q)
    (hdesc : Before (rotationSumPower d r q) (rotationSumPower d r p)) :
    p.1 = q.1 := by
  apply Fin.ext
  have h₁ := before_block_le hpq
  have h₂ := before_block_le hdesc
  change q.1.val <= p.1.val at h₂
  omega

private lemma descent_not_dvd {d : List Nat} {r : Nat} {p q : Position d}
    (hpq : Before p q)
    (hdesc : Before (rotationSumPower d r q) (rotationSumPower d r p)) :
    ¬d.get p.1 ∣ r := by
  have hblock : p.1 = q.1 := descent_same_block hpq hdesc
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  dsimp only at hblock
  subst j
  have hxy : x.val < y.val := by
    simpa [Before] using hpq
  have hrot : rotVal (d.get i) r y.val < rotVal (d.get i) r x.val := by
    simpa [Before, rotationSumPower] using hdesc
  exact rotVal_descent_not_dvd (Nat.zero_lt_of_lt x.isLt) x.isLt y.isLt hxy hrot

private lemma contains2143_of_two_bad {d : List Nat} {r : Nat}
    (hpos : ∀ i : Fin d.length, 0 < d.get i)
    {i j : Fin d.length} (hij : i < j) (hi : ¬d.get i ∣ r) (hj : ¬d.get j ∣ r) :
    TaggedContains2143 (rotationSumPower d r) := by
  obtain ⟨a, b, ha, hb, hab, hba⟩ := exists_rotVal_descent (hpos i) hi
  obtain ⟨c, e, hc, he, hce, hec⟩ := exists_rotVal_descent (hpos j) hj
  let pa : Position d := ⟨i, ⟨a, ha⟩⟩
  let pb : Position d := ⟨i, ⟨b, hb⟩⟩
  let pc : Position d := ⟨j, ⟨c, hc⟩⟩
  let pe : Position d := ⟨j, ⟨e, he⟩⟩
  refine ⟨pa, pb, pc, pe, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr ⟨rfl, hab⟩
  · exact Or.inl hij
  · exact Or.inr ⟨rfl, hce⟩
  · exact Or.inr ⟨rfl, hba⟩
  · exact Or.inl hij
  · exact Or.inr ⟨rfl, hec⟩

private lemma contains2143_gives_two_bad {d : List Nat} {r : Nat}
    (h : TaggedContains2143 (rotationSumPower d r)) :
    ∃ i j : Fin d.length, i ≠ j ∧ ¬d.get i ∣ r ∧ ¬d.get j ∣ r := by
  rcases h with ⟨a, b, c, e, hab, hbc, hce, hba, _hae, hec⟩
  have hib : a.1 = b.1 := descent_same_block hab hba
  have hje : c.1 = e.1 := descent_same_block hce hec
  have hi_bad : ¬d.get a.1 ∣ r := descent_not_dvd hab hba
  have hj_bad : ¬d.get c.1 ∣ r := descent_not_dvd hce hec
  refine ⟨a.1, c.1, ?_, hi_bad, hj_bad⟩
  intro hic
  rcases a with ⟨i, x⟩
  rcases b with ⟨ib, y⟩
  rcases c with ⟨j, z⟩
  rcases e with ⟨je, w⟩
  dsimp only at hib hje hic
  subst ib
  subst j
  subst je
  have hxy : x.val < y.val := by simpa [Before] using hab
  have hyz : y.val < z.val := by simpa [Before] using hbc
  have hzw : z.val < w.val := by simpa [Before] using hce
  have hyx : rotVal (d.get i) r y.val < rotVal (d.get i) r x.val := by
    simpa [Before, rotationSumPower] using hba
  have hwz : rotVal (d.get i) r w.val < rotVal (d.get i) r z.val := by
    simpa [Before, rotationSumPower] using hec
  exact rotVal_no_two_descents (Nat.zero_lt_of_lt x.isLt)
    x.isLt y.isLt z.isLt w.isLt hxy hyz hzw hyx hwz

private theorem tagged_avoids_2143_iff {d : List Nat} {r : Nat}
    (hpos : ∀ i : Fin d.length, 0 < d.get i) :
    (¬TaggedContains2143 (rotationSumPower d r)) ↔ (badBlocks d r).card <= 1 := by
  constructor
  · intro hav
    by_contra hcontra
    have hcard : 1 < (badBlocks d r).card := by omega
    rcases Finset.one_lt_card.mp hcard with ⟨i, hi, j, hj, hij⟩
    have hi' : ¬d.get i ∣ r := by simpa [badBlocks] using hi
    have hj' : ¬d.get j ∣ r := by simpa [badBlocks] using hj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact hav (contains2143_of_two_bad hpos hij' hi' hj')
    · exact hav (contains2143_of_two_bad hpos hji' hj' hi')
  · intro hcard hcontains
    rcases contains2143_gives_two_bad hcontains with ⟨i, j, hij, hi, hj⟩
    have hi' : i ∈ badBlocks d r := by
      simp only [badBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    have hj' : j ∈ badBlocks d r := by
      simp only [badBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    exact hij (Finset.card_le_one.mp hcard i hi' j hj')

private lemma rotVal_add (m r s x : Nat) :
    rotVal m (r + s) x = rotVal m r (rotVal m s x) := by
  unfold rotVal
  calc
    (x + (r + s) % m) % m = (x + (r + s)) % m := Nat.add_mod_mod x (r + s) m
    _ = (x + s + r) % m := by rw [Nat.add_comm r s, ← Nat.add_assoc]
    _ = ((x + s) % m + r) % m := (Nat.mod_add_mod (x + s) m r).symm
    _ = ((x + s % m) % m + r) % m := by rw [Nat.add_mod_mod]
    _ = ((x + s % m) % m + r % m) % m :=
      (Nat.add_mod_mod ((x + s % m) % m) r m).symm

private lemma rotationSumPower_add (d : List Nat) (r s : Nat) (p : Position d) :
    rotationSumPower d (r + s) p =
      rotationSumPower d r (rotationSumPower d s p) := by
  rcases p with ⟨i, x⟩
  change (⟨i, ⟨rotVal (d.get i) (r + s) x.val, _⟩⟩ : Position d) =
    ⟨i, ⟨rotVal (d.get i) r (rotVal (d.get i) s x.val), _⟩⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Fin.ext
  exact rotVal_add (d.get i) r s x.val

/-- The direct sum of the cyclic rotations `epsilon_m = (2, 3, ..., m, 1)`, flattened
to the canonical finite interval. -/
def rotationSumPerm (d : List Nat) :
    Equiv.Perm (Fin (∑ i : Fin d.length, d.get i)) :=
  let e := @finSigmaFinEquiv d.length (fun i => d.get i)
  (e.symm.trans (Equiv.Perm.sigmaCongrRight fun i => finRotate (d.get i))).trans e

/-- Standard four-position containment of the permutation pattern `2143`. -/
def Contains2143 {n : Nat} (f : Fin n -> Fin n) : Prop :=
  ∃ a b c e, a < b ∧ b < c ∧ c < e ∧
    f b < f a ∧ f a < f e ∧ f e < f c

private lemma taggedRotation_apply (d : List Nat) (p : Position d) :
    (Equiv.Perm.sigmaCongrRight fun i => finRotate (d.get i)) p =
      rotationSumPower d 1 p := by
  rcases p with ⟨i, x⟩
  change (⟨i, finRotate (d.get i) x⟩ : Position d) =
    ⟨i, ⟨rotVal (d.get i) 1 x.val, rotVal_lt (Nat.zero_lt_of_lt x.isLt)⟩⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Fin.ext
  simp [rotVal, finRotate_apply, Fin.add_def]

private lemma rotationSumPerm_apply_flatten (d : List Nat) (p : Position d) :
    rotationSumPerm d ((@finSigmaFinEquiv d.length (fun i => d.get i)) p) =
      (@finSigmaFinEquiv d.length (fun i => d.get i)) (rotationSumPower d 1 p) := by
  simp only [rotationSumPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact congrArg _ (taggedRotation_apply d p)

private lemma rotationSumPerm_pow_apply_flatten (d : List Nat) (r : Nat) (p : Position d) :
    (rotationSumPerm d ^ r) ((@finSigmaFinEquiv d.length (fun i => d.get i)) p) =
      (@finSigmaFinEquiv d.length (fun i => d.get i)) (rotationSumPower d r p) := by
  induction r with
  | zero =>
      rcases p with ⟨i, x⟩
      simp only [pow_zero, Equiv.Perm.one_apply]
      apply congrArg (@finSigmaFinEquiv d.length (fun i => d.get i))
      change (⟨i, x⟩ : Position d) =
        ⟨i, ⟨rotVal (d.get i) 0 x.val, rotVal_lt (Nat.zero_lt_of_lt x.isLt)⟩⟩
      refine Sigma.ext rfl (heq_of_eq ?_)
      apply Fin.ext
      simp only [rotVal, Nat.zero_mod, Nat.add_zero]
      exact (Nat.mod_eq_of_lt x.isLt).symm
  | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, rotationSumPerm_apply_flatten]
      apply congrArg _
      calc
        rotationSumPower d 1 (rotationSumPower d r p) =
            rotationSumPower d (1 + r) p := (rotationSumPower_add d 1 r p).symm
        _ = rotationSumPower d r.succ p := by rw [Nat.one_add]

private def blockOffset (d : List Nat) (k : Nat) : Nat :=
  ∑ x ∈ Finset.range k, d.getD x 0

private lemma finSigmaFinEquiv_val (d : List Nat) (p : Position d) :
    ((@finSigmaFinEquiv d.length (fun i => d.get i)) p : Nat) =
      blockOffset d p.1.val + p.2.val := by
  rw [finSigmaFinEquiv_apply]
  simp only [blockOffset]
  rw [← Fin.sum_univ_eq_sum_range (fun x => d.getD x 0) p.1.val]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (k.isLt.trans p.1.isLt)]
  simp only [Option.getD_some, List.get_eq_getElem]
  rfl

private lemma blockOffset_succ (d : List Nat) (k : Nat) :
    blockOffset d (k + 1) = blockOffset d k + d.getD k 0 := by
  simp [blockOffset, Finset.sum_range_succ]

private lemma blockOffset_add_block_le {d : List Nat} {i j : Fin d.length}
    (hij : i.val < j.val) :
    blockOffset d i.val + d.get i ≤ blockOffset d j.val := by
  have hi : d.getD i.val 0 = d.get i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]
    simp [List.get_eq_getElem]
  have hfirst : blockOffset d i.val + d.get i = blockOffset d (i.val + 1) := by
    rw [blockOffset_succ, hi]
  have hle : i.val + 1 ≤ j.val := by omega
  have hs := Finset.sum_range_add_sum_Ico (fun x => d.getD x 0) hle
  change blockOffset d (i.val + 1) +
    (∑ k ∈ Finset.Ico (i.val + 1) j.val, d.getD k 0) = blockOffset d j.val at hs
  rw [hfirst, ← hs]
  exact Nat.le_add_right _ _

private lemma before_iff_fin_lt {d : List Nat} (p q : Position d) :
    Before p q ↔
      (@finSigmaFinEquiv d.length (fun i => d.get i)) p <
        (@finSigmaFinEquiv d.length (fun i => d.get i)) q := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  change (i.val < j.val ∨ (i.val = j.val ∧ x.val < y.val)) ↔ _
  rw [Fin.lt_def, finSigmaFinEquiv_val, finSigmaFinEquiv_val]
  dsimp only
  constructor
  · rintro (hij | ⟨hij, hxy⟩)
    · have hbound := blockOffset_add_block_le hij
      have hxLt : x.val < d.get i := x.isLt
      omega
    · have hidx : i = j := Fin.ext hij
      subst j
      omega
  · intro hlt
    by_cases hij : i.val < j.val
    · exact Or.inl hij
    by_cases hji : j.val < i.val
    · have hbound := blockOffset_add_block_le hji
      have hyLt : y.val < d.get j := y.isLt
      omega
    · right
      have hidx : i = j := Fin.ext (by omega)
      subst j
      exact ⟨rfl, by omega⟩

private lemma contains2143_iff_tagged {d : List Nat} {r : Nat} :
    Contains2143 (⇑(rotationSumPerm d ^ r)) ↔
      TaggedContains2143 (rotationSumPower d r) := by
  let flatten := @finSigmaFinEquiv d.length (fun i => d.get i)
  constructor
  · rintro ⟨a, b, c, e, hab, hbc, hce, hba, hae, hec⟩
    let pa := flatten.symm a
    let pb := flatten.symm b
    let pc := flatten.symm c
    let pe := flatten.symm e
    refine ⟨pa, pb, pc, pe, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply (before_iff_fin_lt pa pb).mpr
      simpa [pa, pb, flatten] using hab
    · apply (before_iff_fin_lt pb pc).mpr
      simpa [pb, pc, flatten] using hbc
    · apply (before_iff_fin_lt pc pe).mpr
      simpa [pc, pe, flatten] using hce
    · apply (before_iff_fin_lt (rotationSumPower d r pb) (rotationSumPower d r pa)).mpr
      rw [← rotationSumPerm_pow_apply_flatten, ← rotationSumPerm_pow_apply_flatten]
      simpa [pa, pb, flatten] using hba
    · apply (before_iff_fin_lt (rotationSumPower d r pa) (rotationSumPower d r pe)).mpr
      rw [← rotationSumPerm_pow_apply_flatten, ← rotationSumPerm_pow_apply_flatten]
      simpa [pa, pe, flatten] using hae
    · apply (before_iff_fin_lt (rotationSumPower d r pe) (rotationSumPower d r pc)).mpr
      rw [← rotationSumPerm_pow_apply_flatten, ← rotationSumPerm_pow_apply_flatten]
      simpa [pc, pe, flatten] using hec
  · rintro ⟨a, b, c, e, hab, hbc, hce, hba, hae, hec⟩
    refine ⟨flatten a, flatten b, flatten c, flatten e, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (before_iff_fin_lt a b).mp hab
    · exact (before_iff_fin_lt b c).mp hbc
    · exact (before_iff_fin_lt c e).mp hce
    · rw [rotationSumPerm_pow_apply_flatten, rotationSumPerm_pow_apply_flatten]
      exact (before_iff_fin_lt (rotationSumPower d r b) (rotationSumPower d r a)).mp hba
    · rw [rotationSumPerm_pow_apply_flatten, rotationSumPerm_pow_apply_flatten]
      exact (before_iff_fin_lt (rotationSumPower d r a) (rotationSumPower d r e)).mp hae
    · rw [rotationSumPerm_pow_apply_flatten, rotationSumPerm_pow_apply_flatten]
      exact (before_iff_fin_lt (rotationSumPower d r e) (rotationSumPower d r c)).mp hec

/-- For positive block sizes, every power of the direct sum avoids `2143` exactly when
at most one block size fails to divide the exponent. -/
theorem rotationSumPerm_pow_avoids_2143_iff
    {d : List Nat} {r : Nat}
    (hpos : ∀ i : Fin d.length, 0 < d.get i) :
    (¬Contains2143 (⇑(rotationSumPerm d ^ r))) ↔
      (Finset.univ.filter fun i : Fin d.length => ¬d.get i ∣ r).card ≤ 1 := by
  rw [contains2143_iff_tagged]
  exact tagged_avoids_2143_iff hpos

/-- At exponent three, the exceptional blocks are exactly those whose sizes are neither
`1` nor `3`. -/
theorem rotationSumPerm_cube_avoids_2143_iff
    {d : List Nat}
    (hpos : ∀ i : Fin d.length, 0 < d.get i) :
    (¬Contains2143 (⇑(rotationSumPerm d ^ 3))) ↔
      (Finset.univ.filter fun i : Fin d.length => d.get i ≠ 1 ∧ d.get i ≠ 3).card ≤ 1 := by
  rw [rotationSumPerm_pow_avoids_2143_iff hpos]
  have hfilters :
      (Finset.univ.filter fun i : Fin d.length => ¬d.get i ∣ 3) =
        Finset.univ.filter fun i : Fin d.length => d.get i ≠ 1 ∧ d.get i ≠ 3 := by
    ext i
    simp [Nat.dvd_prime Nat.prime_three]
  rw [hfilters]

example : Nonempty
    (Fin (∑ i : Fin ([1] : List Nat).length, ([1] : List Nat).get i)) := by
  exact ⟨⟨0, by decide⟩⟩

example : ∀ i : Fin ([1] : List Nat).length, 0 < ([1] : List Nat).get i := by
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  decide

end D5.S3.ConceptDynamics.PatternAvoidance.RotationSumPowerPatternAvoidance
