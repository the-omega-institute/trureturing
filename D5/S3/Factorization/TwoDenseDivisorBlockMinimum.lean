/- GID: D5/S3/Factorization/TwoDenseDivisorBlockMinimum
   generality: G
   mirror-B: D5/B/S3/Factorization/TwoDenseDivisorBlockMinimum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Dense divisor copies are contained in whole maximal divisor blocks. -/

import D5.S3.Factorization.TwoDenseDivisorBlocksPalindrome
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.List.Pairwise

/-! Maximal divisor blocks and dense multiplicative copies. -/

namespace D5.S3.Factorization.TwoDenseDivisorBlockMinimum

/-- The actual maximal blocks of the complete increasing positive divisor list. -/
def divisorBlocks (n : ℕ) : List (List ℕ) :=
  (n.divisorsAntidiagonalList.map Prod.fst).splitBy
    (fun a b => decide (b ≤ 2 * a))

/-- The unrestricted positive-integer first-block minimum event. -/
def claim : Prop := ∀ n : ℕ, 0 < n →
  ∀ B ∈ divisorBlocks n,
    (TwoDenseDivisorBlocksPalindrome.row n).headD 0 ≤ B.length

private theorem mem_divisor_list (n d : ℕ) (hn : 0 < n) :
    d ∈ n.divisorsAntidiagonalList.map Prod.fst ↔ d ∣ n := by
  constructor
  · intro hd
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hd
    obtain ⟨hp, _⟩ := Nat.mem_divisorsAntidiagonalList.mp hp
    exact he ▸ ⟨p.2, hp.symm⟩
  · intro hd
    exact List.mem_map.mpr ⟨(d, n / d),
      Nat.mem_divisorsAntidiagonalList.mpr
        ⟨Nat.mul_div_cancel' hd, hn.ne'⟩, rfl⟩

private theorem separated_blocks_connect :
    ∀ Q : List (List ℕ), Q.flatten.Pairwise (· < ·) → [] ∉ Q →
    Q.IsChain (fun A C => ∃ ha hc, 2 * A.getLast ha < C.head hc) →
    ∀ x ∈ Q.flatten, ∀ y ∈ Q.flatten, x ≤ 2 * y → y ≤ 2 * x →
    ∀ B ∈ Q, (x ∈ B ↔ y ∈ B) := by
  intro Q
  induction Q with
  | nil => simp
  | cons A T ih =>
    intro hs he hc x hx y hy hxy hyx B hB
    rw [List.flatten_cons] at hs
    obtain ⟨hsA, hsT, cross⟩ := List.pairwise_append.mp hs
    have gap : ∀ a ∈ A, ∀ c ∈ T.flatten, 2 * a < c := by
      intro a ha c hct
      cases T with
      | nil => simp at hct
      | cons C R =>
        obtain ⟨hneA, hneC, hcut⟩ := (List.isChain_cons_cons.mp hc).1
        have halast : a ≤ A.getLast hneA :=
          (hsA.imp (fun h => Nat.le_of_lt h)).rel_getLast ha
        have htc := List.pairwise_append.mp (show (C ++ R.flatten).Pairwise (· < ·) from hsT)
        have hhead : C.head hneC ≤ c := by
          rcases List.mem_append.mp hct with hct | hct
          · exact (htc.1.imp (fun h => Nat.le_of_lt h)).rel_head hct
          · exact Nat.le_of_lt (htc.2.2 _ (List.head_mem hneC) _ hct)
        omega
    have tailne : [] ∉ T := fun h => he (List.mem_cons_of_mem A h)
    have tailchain := hc.tail
    simp only [List.flatten_cons, List.mem_append] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rcases List.mem_cons.mp hB with hBA | hB
      · subst B
        exact iff_of_true hx hy
      · have notx : x ∉ B := by
          intro hb
          have := cross x hx x (List.mem_flatten.mpr ⟨B, hB, hb⟩)
          omega
        have noty : y ∉ B := by
          intro hb
          have := cross y hy y (List.mem_flatten.mpr ⟨B, hB, hb⟩)
          omega
        exact iff_of_false notx noty
    · have := gap x hx y hy
      omega
    · have := gap y hy x hx
      omega
    · rcases List.mem_cons.mp hB with hBA | hB
      · subst B
        have notx : x ∉ A := by
          intro ha
          have := cross x ha x hx
          omega
        have noty : y ∉ A := by
          intro ha
          have := cross y ha y hy
          omega
        exact iff_of_false notx noty
      · exact ih hsT tailne tailchain x hx y hy hxy hyx B hB

private theorem chain_constant {K : List ℕ} {P : ℕ → Prop}
    (hc : K.IsChain (fun a b => P a ↔ P b)) :
    ∀ x ∈ K, ∀ y ∈ K, P x ↔ P y := by
  induction K with
  | nil => simp
  | cons a T ih =>
    intro x hx y hy
    have headrel : ∀ z ∈ a :: T, P a ↔ P z := by
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · subst z; rfl
      · exact hc.rel_cons hz
    exact (headrel x hx).symm.trans (headrel y hy)

/-- A dense coprime divisor factor supplies a full injective copy in every block.
The factor is a genuine divisor of n; its existence is not asserted here. -/
theorem block_card_ge_of_dense_factor (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hcop : u.Coprime v)
    (hdense : (u.divisorsAntidiagonalList.map Prod.fst).IsChain
      (fun a b => b ≤ 2 * a))
    (B : List ℕ) (hB : B ∈ divisorBlocks (u * v)) :
    u.divisors.card ≤ B.length := by
  classical
  let n := u * v
  let D := n.divisorsAntidiagonalList.map Prod.fst
  let U := u.divisorsAntidiagonalList.map Prod.fst
  let Q := divisorBlocks n
  have hn : 0 < n := Nat.mul_pos hu hv
  have memD (d : ℕ) : d ∈ D ↔ d ∣ n := mem_divisor_list n d hn
  have memU (a : ℕ) : a ∈ U ↔ a ∣ u := mem_divisor_list u a hu
  have hflat : Q.flatten = D := List.flatten_splitBy _ _
  have hsort : Q.flatten.Pairwise (· < ·) := by
    rw [hflat]
    exact Nat.sortedLT_map_fst_divisorsAntidiagonalList.pairwise
  have hne : [] ∉ Q := List.nil_notMem_splitBy _ _
  have hboundary : Q.IsChain (fun A C =>
      ∃ ha hc, 2 * A.getLast ha < C.head hc) := by
    apply (List.isChain_getLast_head_splitBy (fun a b => decide (b ≤ 2 * a)) D).imp
    intro A C h
    obtain ⟨ha, hc, h⟩ := h
    refine ⟨ha, hc, ?_⟩
    have hh : ¬ C.head hc ≤ 2 * A.getLast ha := of_decide_eq_false h
    omega
  have sub : B.Sublist D := hflat ▸ List.sublist_flatten_of_mem hB
  have Bne : B ≠ [] := fun hz => hne (hz ▸ hB)
  let d := B.head Bne
  have hdB : d ∈ B := List.head_mem Bne
  have hd : d ∣ u * v := (memD d).mp (sub.subset hdB)
  let a := Nat.gcd d u
  let b := Nat.gcd d v
  have hab : a * b = d := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩)
  have hbpos : 0 < b := by nlinarith
  have haU : a ∈ U := (memU a).mpr (Nat.gcd_dvd_right d u)
  have allD (x : ℕ) (hx : x ∈ U) : b * x ∈ D := by
    apply (memD _).mpr
    simpa [n, mul_comm b x] using
      Nat.mul_dvd_mul ((memU x).mp hx) (Nat.gcd_dvd_right d v)
  have hc : U.IsChain (fun x y => b * x ∈ B ↔ b * y ∈ B) := by
    have hsorted : U.IsChain (· < ·) :=
      Nat.sortedLT_map_fst_divisorsAntidiagonalList.pairwise.isChain
    have combine (L : List ℕ) (hs : L.IsChain (· < ·))
        (hd : L.IsChain (fun x y => y ≤ 2*x)) :
        L.IsChain (fun x y => x < y ∧ y ≤ 2*x) := by
      induction L using List.twoStepInduction with
      | nil => simp
      | singleton x => simp
      | cons_cons x y T ih ihNext =>
        rw [List.isChain_cons_cons] at hs hd ⊢
        exact ⟨⟨hs.1, hd.1⟩, ihNext y hs.2 hd.2⟩
    have hboth := combine U hsorted hdense
    apply hboth.imp_of_mem_imp
    intro x y hx hy hxy
    apply separated_blocks_connect Q hsort hne hboundary
      (b*x) (hflat.symm ▸ allD x hx) (b*y) (hflat.symm ▸ allD y hy)
      (by nlinarith [Nat.mul_le_mul_left b hxy.2])
      (by nlinarith [Nat.mul_le_mul_left b (Nat.le_of_lt hxy.1)]) B hB
  have allB (x : ℕ) (hx : x ∈ U) : b * x ∈ B := by
    apply (chain_constant hc x hx a haU).mpr
    simpa [mul_comm b a, hab] using hdB
  have hcard : u.divisors.card ≤ B.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun x => b * x)
    · intro x hx
      exact List.mem_toFinset.mpr (allB x ((memU x).mpr (Nat.mem_divisors.mp hx).1))
    · intro x hx y hy he
      exact Nat.eq_of_mul_eq_mul_left hbpos he
  rw [List.toFinset_card_of_nodup (sub.nodup
    Nat.sortedLT_map_fst_divisorsAntidiagonalList.nodup)] at hcard
  exact hcard


private theorem first_block_length_of_gap (n u : ℕ) (hn : 0 < n) (hu : 0 < u)
    (hudvd : u ∣ n)
    (hdense : (u.divisorsAntidiagonalList.map Prod.fst).IsChain
      (fun a b => b ≤ 2 * a))
    (hgap : ∀ d, d ∣ n → ¬ d ∣ u → 2 * u < d) :
    (TwoDenseDivisorBlocksPalindrome.row n).headD 0 = u.divisors.card := by
  classical
  let D := n.divisorsAntidiagonalList.map Prod.fst
  let U := u.divisorsAntidiagonalList.map Prod.fst
  let R := D.filter (fun d => decide (¬ d ∣ u))
  have memD (d : ℕ) : d ∈ D ↔ d ∣ n := mem_divisor_list n d hn
  have memU (d : ℕ) : d ∈ U ↔ d ∣ u := mem_divisor_list u d hu
  have hsD : D.Pairwise (· < ·) :=
    Nat.sortedLT_map_fst_divisorsAntidiagonalList.pairwise
  have hsU : U.Pairwise (· < ·) :=
    Nat.sortedLT_map_fst_divisorsAntidiagonalList.pairwise
  have hsR : R.Pairwise (· < ·) := hsD.sublist (List.filter_sublist)
  have cross : ∀ x ∈ U, ∀ y ∈ R, 2 * x < y := by
    intro x hx y hy
    have hxu := Nat.le_of_dvd hu ((memU x).mp hx)
    obtain ⟨hyD, hyu⟩ := List.mem_filter.mp hy
    have hgy := hgap y ((memD y).mp hyD) (of_decide_eq_true hyu)
    omega
  have hDU : D = U ++ R := by
    apply hsD.eq_of_mem_iff
      (List.pairwise_append.mpr ⟨hsU, hsR, fun x hx y hy => by
        have := cross x hx y hy
        omega⟩)
    intro d
    simp only [List.mem_append]
    change d ∈ D ↔ d ∈ U ∨ d ∈ D.filter (fun d => decide (¬ d ∣ u))
    simp only [List.mem_filter, decide_eq_true_eq]
    by_cases hdu : d ∣ u
    · exact ⟨fun _ => Or.inl ((memU d).mpr hdu), fun _ =>
        (memD d).mpr (hdu.trans hudvd)⟩
    · exact ⟨fun hd => Or.inr ⟨hd, hdu⟩, fun hd => by
        rcases hd with hd | hd
        · exact False.elim (hdu ((memU d).mp hd))
        · exact hd.1⟩
  have hUne : U ≠ [] := by
    intro hz
    have : 1 ∈ U := (memU 1).mpr (one_dvd u)
    simp [hz] at this
  have hsplit : divisorBlocks n = U :: R.splitBy
      (fun a b => decide (b ≤ 2 * a)) := by
    change D.splitBy _ = _
    rw [hDU, List.splitBy_append]
    · rw [List.splitBy_of_isChain hUne
        (by simpa only [decide_eq_true_eq] using hdense)]
      rfl
    · intro x hx y hy
      have := cross x (List.mem_of_mem_getLast? hx) y (List.mem_of_mem_head? hy)
      exact decide_eq_false_iff_not.mpr (by omega)
  have hset : U.toFinset = u.divisors := by
    ext d
    simp only [List.mem_toFinset, memU, Nat.mem_divisors, and_iff_left hu.ne']
  change ((divisorBlocks n).map List.length).headD 0 = _
  rw [hsplit]
  simp only [List.map_cons, List.headD_cons]
  rw [← hset, List.toFinset_card_of_nodup hsU.nodup]

/-- The complete first-block conclusion under the still-required dense-factor
construction and the separating outsider bound. -/
theorem first_block_min_of_dense_factor (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hcop : u.Coprime v)
    (hdense : (u.divisorsAntidiagonalList.map Prod.fst).IsChain
      (fun a b => b ≤ 2 * a))
    (hrough : ∀ p, p.Prime → p ∣ v → 2 * u < p) :
    ∀ B ∈ divisorBlocks (u * v),
      (TwoDenseDivisorBlocksPalindrome.row (u * v)).headD 0 ≤ B.length := by
  have hgap : ∀ d, d ∣ u * v → ¬ d ∣ u → 2 * u < d := by
    intro d hd hdu
    have he : Nat.gcd d u * Nat.gcd d v = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr hd
    have hb1 : Nat.gcd d v ≠ 1 := by
      intro hb
      rw [hb, mul_one] at he
      exact hdu (he ▸ Nat.gcd_dvd_right d u)
    have hp := Nat.minFac_prime hb1
    have hpdvd : (Nat.gcd d v).minFac ∣ d :=
      (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left d v)
    have hdpos : 0 < d := Nat.pos_of_mem_divisors
      (Nat.mem_divisors.mpr ⟨hd, (Nat.mul_pos hu hv).ne'⟩)
    exact (hrough _ hp ((Nat.minFac_dvd _).trans
      (Nat.gcd_dvd_right d v))).trans_le (Nat.le_of_dvd hdpos hpdvd)
  intro B hB
  rw [first_block_length_of_gap (u * v) u (Nat.mul_pos hu hv) hu
    (dvd_mul_right u v) hdense hgap]
  exact block_card_ge_of_dense_factor u v hu hv hcop hdense B hB


/-- Integer interval coverage of the positive divisors. -/
private def IntervalDense (u : ℕ) : Prop :=
  ∀ x : ℕ, 0 < x → x < u → ∃ d, d ∣ u ∧ x < d ∧ d ≤ 2 * x

private theorem intervalDense_mul (u p : ℕ) (hp : 0 < p)
    (hd : IntervalDense u) (hpu : p ≤ 2 * u) : IntervalDense (u * p) := by
  intro x hx hxu
  by_cases hsmall : x < u
  · obtain ⟨d, hdu, hxd, hd2⟩ := hd x hx hsmall
    exact ⟨d, hdu.trans (dvd_mul_right u p), hxd, hd2⟩
  · have hux : u ≤ x := Nat.le_of_not_gt hsmall
    by_cases hxp : x < p
    · exact ⟨p, dvd_mul_left p u, hxp, by omega⟩
    · have hqpos : 0 < x / p := Nat.div_pos (Nat.le_of_not_gt hxp) hp
      have hqlt : x / p < u := (Nat.div_lt_iff_lt_mul hp).mpr hxu
      obtain ⟨d, hdu, hqd, hd2⟩ := hd (x / p) hqpos hqlt
      refine ⟨d * p, Nat.mul_dvd_mul hdu (dvd_refl p),
        (Nat.div_lt_iff_lt_mul hp).mp hqd, ?_⟩
      have hmul := Nat.mul_le_mul_right p hd2
      have hfloor := Nat.div_mul_le_self x p
      nlinarith

private theorem chain_of_interval_cover (u : ℕ) (L : List ℕ) :
    L.Pairwise (· < ·) → (∀ x ∈ L, 0 < x) → (∀ x ∈ L, x ≤ u) →
    (∀ x ∈ L, x < u → ∃ d ∈ L, x < d ∧ d ≤ 2 * x) →
    L.IsChain (fun a b => b ≤ 2 * a) := by
  induction L with
  | nil => simp
  | cons a T ih =>
    intro hs hpos hle hcover
    cases T with
    | nil => simp
    | cons b T =>
      have hs' := List.pairwise_cons.mp hs
      have hab : a < b := hs'.1 b (by simp)
      have hbu : b ≤ u := hle b (by simp)
      obtain ⟨d, hd, had, hd2⟩ := hcover a (by simp) (by omega)
      have hbd : b ≤ d := by
        rcases List.mem_cons.mp hd with he | hd
        · omega
        · exact (hs'.2.imp (fun h => Nat.le_of_lt h)).rel_head hd
      apply List.isChain_cons_cons.mpr
      refine ⟨by omega, ih hs'.2 (fun x hx => hpos x (List.mem_cons_of_mem a hx))
        (fun x hx => hle x (List.mem_cons_of_mem a hx)) ?_⟩
      intro x hx hxu
      obtain ⟨d, hd, hxd, hd2⟩ := hcover x (List.mem_cons_of_mem a hx) hxu
      rcases List.mem_cons.mp hd with he | hd
      · have hax := hs'.1 x hx
        omega
      · exact ⟨d, hd, hxd, hd2⟩

private theorem intervalDense_chain (u : ℕ) (hu : 0 < u) (hd : IntervalDense u) :
    (u.divisorsAntidiagonalList.map Prod.fst).IsChain (fun a b => b ≤ 2 * a) := by
  apply chain_of_interval_cover u
  · exact Nat.sortedLT_map_fst_divisorsAntidiagonalList.pairwise
  · intro x hx
    exact Nat.pos_of_mem_divisors
      (Nat.mem_divisors.mpr ⟨(mem_divisor_list u x hu).mp hx, hu.ne'⟩)
  · intro x hx
    exact Nat.le_of_dvd hu ((mem_divisor_list u x hu).mp hx)
  · intro x hx hxu
    have hxpos := Nat.pos_of_mem_divisors
      (Nat.mem_divisors.mpr ⟨(mem_divisor_list u x hu).mp hx, hu.ne'⟩)
    obtain ⟨d, hdu, hxd, hd2⟩ := hd x hxpos hxu
    exact ⟨d, (mem_divisor_list u d hu).mpr hdu, hxd, hd2⟩

/-- Every positive integer satisfies the literal unrestricted first-block event. -/
theorem result : claim := by
  classical
  intro n hn
  let S := n.divisors.filter IntervalDense
  have h1 : 1 ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩, ?_⟩
    intro x hx hx1
    omega
  have hSne : S.Nonempty := ⟨1, h1⟩
  let u := S.max' hSne
  have huS : u ∈ S := S.max'_mem hSne
  obtain ⟨hun, hudense⟩ := Finset.mem_filter.mp huS
  have hu : 0 < u := Nat.pos_of_mem_divisors hun
  have hudvd : u ∣ n := (Nat.mem_divisors.mp hun).1
  let v := n / u
  have hv : 0 < v := Nat.div_pos (Nat.le_of_dvd hn hudvd) hu
  have he : u * v = n := Nat.mul_div_cancel' hudvd
  have hrough : ∀ p, p.Prime → p ∣ v → 2 * u < p := by
    intro p hp hpv
    by_contra hnot
    have hpu : p ≤ 2 * u := Nat.le_of_not_gt hnot
    have hupn : u * p ∣ n := he ▸ Nat.mul_dvd_mul (dvd_refl u) hpv
    have hupS : u * p ∈ S := Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hupn, hn.ne'⟩,
        intervalDense_mul u p hp.pos hudense hpu⟩
    have hmax : u * p ≤ u := S.le_max' (u * p) hupS
    nlinarith [hp.two_le]
  have hcop : u.Coprime v := Nat.coprime_of_dvd (fun p hp hpu hpv => by
    have hpbig := hrough p hp hpv
    have hple := Nat.le_of_dvd hu hpu
    omega)
  have hmin := first_block_min_of_dense_factor u v hu hv hcop
    (intervalDense_chain u hu hudense) hrough
  simpa only [he] using hmin

#print axioms result

#print axioms first_block_min_of_dense_factor

#print axioms block_card_ge_of_dense_factor

end D5.S3.Factorization.TwoDenseDivisorBlockMinimum
