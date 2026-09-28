/- GID: D5/S3/Combinatorics/Partitions/PartitionLInftyGeodesic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/PartitionLInftyGeodesic
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed-mass antitone partition vectors admit endpoint-confined d-infinity geodesics. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Partitions.PartitionLInftyGeodesic

def Partition (n : ℕ) :=
  {v : List ℕ // v.length = n ∧ v.Pairwise (· ≥ ·) ∧ v.sum = n}

def coord {n : ℕ} (p : Partition n) (i : Fin n) : ℕ :=
  p.1.get ⟨i.1, by simpa [p.2.1] using i.2⟩

def dInf {n : ℕ} (p q : Partition n) : ℕ :=
  Finset.sup Finset.univ (fun i => max (coord p i - coord q i) (coord q i - coord p i))

def Path {n D : ℕ} (p q : Partition n) :=
  {γ : Fin (D + 1) → Partition n //
    γ 0 = p ∧
    γ ⟨D, by omega⟩ = q ∧
    (∀ k : Fin D, dInf (γ ⟨k.1, by omega⟩) (γ ⟨k.1 + 1, by omega⟩) ≤ 1) ∧
    (∀ k : Fin (D + 1), ∀ i : Fin n,
      min (coord p i) (coord q i) ≤ coord (γ k) i ∧
      coord (γ k) i ≤ max (coord p i) (coord q i))}

private def fill (l h : List ℕ) (r : ℕ) : List ℕ :=
  match l, h with
  | a :: as, b :: bs =>
      let t := min r (b - a)
      (a + t) :: fill as bs (r - t)
  | _, _ => []

private def lowerFn {n D : ℕ} (p q : Partition n) (i : Fin n) : ℕ :=
    max 0 (max (coord p i - 1)
      (max (coord q i - (D - 1)) (min (coord p i) (coord q i))))

private def upperFn {n D : ℕ} (p q : Partition n) (i : Fin n) : ℕ :=
    min (coord p i + 1)
      (min (coord q i + (D - 1)) (max (coord p i) (coord q i)))

private def upper {n D : ℕ} (p q : Partition n) : List ℕ :=
  List.ofFn (upperFn (D := D) p q)

private def listPartition {n : ℕ} (v : List ℕ)
    (hlen : v.length = n) (hpair : v.Pairwise (· ≥ ·)) (hsum : v.sum = n) : Partition n :=
  ⟨v, hlen, hpair, hsum⟩

private def baseFn {n D : ℕ} (p q : Partition n) (i : Fin n) : ℕ :=
  ((D - 1) * coord p i + coord q i) / D

private def base {n D : ℕ} (p q : Partition n) : List ℕ :=
  List.ofFn (baseFn (D := D) p q)

/-- Every pair of fixed-mass partitions has an endpoint-confined path whose
length is its maximum coordinate difference. -/
theorem partition_lInf_geodesic {n : ℕ} (p q : Partition n) :
    Nonempty (Path (D := dInf p q) p q) ∧
      (∀ K : ℕ, ∀ γ : Fin (K + 1) → Partition n,
        γ 0 = p → γ ⟨K, by omega⟩ = q →
        (∀ k : Fin K, dInf (γ ⟨k.1, by omega⟩)
          (γ ⟨k.1 + 1, by omega⟩) ≤ 1) → dInf p q ≤ K) := by
  classical
  have fill_length {l h : List ℕ} {r : ℕ} (hlen : l.length = h.length) :
      (fill l h r).length = l.length := by
    induction l generalizing h r with
    | nil => cases h <;> simp [fill]
    | cons a as ih =>
        cases h with
        | nil => simp at hlen
        | cons b bs => simp only [List.length_cons] at hlen ⊢
                       simp [fill, ih (hlen := Nat.succ.inj hlen)]

  have list_sum_le {l h : List ℕ}
      (hlen : l.length = h.length)
      (hle : ∀ i : Fin l.length, l.get i ≤ h.get (Fin.cast hlen i)) :
      l.sum ≤ h.sum := by
    induction l generalizing h with
    | nil => cases h <;> simp
    | cons a as ih =>
        cases h with
        | nil => simp at hlen
        | cons b bs =>
            simp only [List.length_cons] at hlen
            have hab : a ≤ b := by simpa using hle ⟨0, by simp⟩
            have htail := ih (h := bs) (hlen := Nat.succ.inj hlen)
              (hle := by
                intro i
                simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
            simp only [List.sum_cons]
            omega

  have fill_zero {l h : List ℕ} (hlen : l.length = h.length) :
      fill l h 0 = l := by
    induction l generalizing h with
    | nil => cases h <;> simp [fill]
    | cons a as ih =>
        cases h with
        | nil => simp at hlen
        | cons b bs =>
            simp only [List.length_cons] at hlen
            simp [fill, ih (Nat.succ.inj hlen)]

  have fill_sum {l h : List ℕ} {r : ℕ}
      (hlen : l.length = h.length)
      (hle : ∀ i : Fin l.length, l.get i ≤ h.get (Fin.cast hlen i))
      (hr : r ≤ h.sum - l.sum) :
      (fill l h r).sum = l.sum + r := by
    induction l generalizing h r with
    | nil =>
        cases h with
        | nil =>
            have hr0 : r = 0 := Nat.eq_zero_of_le_zero (by simpa using hr)
            simp [fill, hr0]
        | cons b bs => simp at hlen
    | cons a as ih =>
        cases h with
        | nil => simp at hlen
        | cons b bs =>
            simp only [List.length_cons] at hlen
            have hsum := list_sum_le (l := as) (h := bs) (Nat.succ.inj hlen) (by
              intro i
              simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
            simp only [fill, List.sum_cons]
            let t := min r (b - a)
            have hab : a ≤ b := by
              simpa using hle ⟨0, by simp⟩
            have hrest : r - t ≤ bs.sum - as.sum := by
              dsimp [t]
              by_cases hcap : r ≤ b - a
              · simp only [min_eq_left hcap, tsub_self]
                exact Nat.zero_le _
              · simp only [min_eq_right (Nat.le_of_not_ge hcap)]
                have htotal : a + as.sum ≤ b + bs.sum := by
                  simpa [List.sum_cons] using Nat.add_le_add hab hsum
                have hadd : r + (a + as.sum) ≤ b + bs.sum :=
                  (Nat.le_sub_iff_add_le htotal).mp (by simpa [List.sum_cons] using hr)
                apply Nat.le_sub_of_add_le
                have hba : a + (b - a) = b := Nat.add_sub_of_le hab
                omega
            have htail := ih (h := bs) (r := r - t)
              (hlen := Nat.succ.inj hlen)
              (hle := by
                intro i
                simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
              hrest
            dsimp [t] at htail ⊢
            omega

  have fill_all_le {l h : List ℕ} {b : ℕ} {r : ℕ}
      (hh : (b :: h).Pairwise (· ≥ ·))
      (hlen : l.length = h.length)
      (hle : ∀ i : Fin l.length, l.get i ≤ h.get (Fin.cast hlen i))
      (hr : r ≤ h.sum - l.sum) :
      ∀ x ∈ fill l h r, x ≤ b := by
    induction l generalizing h b r with
    | nil => simp [fill]
    | cons a as ih =>
        cases h with
        | nil => simp at hlen
        | cons c cs =>
            simp only [List.length_cons] at hlen
            have hsum := list_sum_le (l := as) (h := cs) (Nat.succ.inj hlen) (by
              intro i
              simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
            have hh' := List.pairwise_cons.mp hh
            let t := min r (c - a)
            have hac : a ≤ c := by simpa using hle ⟨0, by simp⟩
            have hrest : r - t ≤ cs.sum - as.sum := by
              dsimp [t]
              by_cases hcap : r ≤ c - a
              · simp only [min_eq_left hcap, tsub_self]
                exact Nat.zero_le _
              · simp only [min_eq_right (Nat.le_of_not_ge hcap)]
                have htotal : a + as.sum ≤ c + cs.sum := by
                  simpa [List.sum_cons] using Nat.add_le_add hac hsum
                have hadd : r + (a + as.sum) ≤ c + cs.sum :=
                  (Nat.le_sub_iff_add_le htotal).mp (by simpa [List.sum_cons] using hr)
                apply Nat.le_sub_of_add_le
                have hba : a + (c - a) = c := Nat.add_sub_of_le hac
                omega
            have htail := ih (h := cs) (b := c) (r := r - t)
              (hh := hh'.2)
              (hlen := Nat.succ.inj hlen)
              (hle := by
                intro i
                simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
              hrest
            intro x hx
            dsimp [fill, t] at hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · have hbc : b ≥ c := hh'.1 c (by simp)
              by_cases hcap : r ≤ c - a
              · simp only [min_eq_left hcap]
                omega
              · simp only [min_eq_right (Nat.le_of_not_ge hcap)]
                omega
            · exact (htail x hx).trans (hh'.1 c (by simp))

  have fill_pairwise {l h : List ℕ} {r : ℕ}
      (hlen : l.length = h.length)
      (hl : l.Pairwise (· ≥ ·)) (hh : h.Pairwise (· ≥ ·))
      (hle : ∀ i : Fin l.length, l.get i ≤ h.get (Fin.cast hlen i))
      (hr : r ≤ h.sum - l.sum) :
      (fill l h r).Pairwise (· ≥ ·) := by
    induction l generalizing h r with
    | nil => simp [fill]
    | cons a as ih =>
        cases h with
        | nil => simp at hlen
        | cons b bs =>
            simp only [List.length_cons] at hlen
            have hsum := list_sum_le (l := as) (h := bs) (Nat.succ.inj hlen) (by
              intro i
              simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
            simp only [List.pairwise_cons] at hl hh ⊢
            let t := min r (b - a)
            have hab : a ≤ b := by simpa using hle ⟨0, by simp⟩
            have hrest : r - t ≤ bs.sum - as.sum := by
              dsimp [t]
              by_cases hcap : r ≤ b - a
              · simp only [min_eq_left hcap, tsub_self]
                exact Nat.zero_le _
              · simp only [min_eq_right (Nat.le_of_not_ge hcap)]
                have htotal : a + as.sum ≤ b + bs.sum := by
                  simpa [List.sum_cons] using Nat.add_le_add hab hsum
                have hadd : r + (a + as.sum) ≤ b + bs.sum :=
                  (Nat.le_sub_iff_add_le htotal).mp (by simpa [List.sum_cons] using hr)
                apply Nat.le_sub_of_add_le
                have hba : a + (b - a) = b := Nat.add_sub_of_le hab
                omega
            have htail := ih (h := bs) (r := r - t)
              (hlen := Nat.succ.inj hlen)
              (hl := by simpa using hl.2)
              (hh := by simpa using hh.2)
              (hle := by
                intro i
                simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
              hrest
            have htail_le := fill_all_le (l := as) (h := bs) (b := b) (r := r - t)
              (hh := List.pairwise_cons.mpr ⟨hh.1, hh.2⟩) (hlen := Nat.succ.inj hlen)
              (hle := by
                intro i
                simpa using hle ⟨i.1 + 1, by simp [i.2]⟩)
              hrest
            dsimp [fill, t]
            constructor
            · intro x hx
              have hxb : b ≥ x := htail_le x hx
              by_cases hcap : r ≤ b - a
              · simp only [min_eq_left hcap] at hx ⊢
                have hx' : x ∈ as := by
                  rw [Nat.sub_self r, fill_zero (Nat.succ.inj hlen)] at hx
                  exact hx
                exact (hl.1 x hx').trans (Nat.le_add_right a r)
              · simp only [min_eq_right (Nat.le_of_not_ge hcap)]
                omega
            · exact htail

  have partition_one_step {n : ℕ} (p q : Partition n) {D : ℕ}
      (hD : 0 < D) (hd : dInf p q = D) :
      ∃ r : Partition n,
        dInf p r ≤ 1 ∧ dInf r q = D - 1 ∧
        (∀ i : Fin n, min (coord p i) (coord q i) ≤ coord r i ∧
          coord r i ≤ max (coord p i) (coord q i)) := by
    classical
    have pant : ∀ ⦃i j : Fin n⦄, i < j → coord p i ≥ coord p j := by
      intro i j hij
      have hp := (List.pairwise_iff_get.mp p.2.2.1)
        ⟨i.1, by simpa [p.2.1] using i.2⟩
        ⟨j.1, by simpa [p.2.1] using j.2⟩
        (by simpa using hij)
      simpa [coord] using hp
    have qant : ∀ ⦃i j : Fin n⦄, i < j → coord q i ≥ coord q j := by
      intro i j hij
      have hq := (List.pairwise_iff_get.mp q.2.2.1)
        ⟨i.1, by simpa [q.2.1] using i.2⟩
        ⟨j.1, by simpa [q.2.1] using j.2⟩
        (by simpa using hij)
      simpa [coord] using hq
    have hcoord : ∀ i : Fin n, max (coord p i - coord q i) (coord q i - coord p i) ≤ D := by
      intro i
      have hi := Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := fun j =>
        max (coord p j - coord q j) (coord q j - coord p j)) (Finset.mem_univ i)
      have hi' : max (coord p i - coord q i) (coord q i - coord p i) ≤ dInf p q := by
        simpa [dInf] using hi
      simpa [hd] using hi'
    have hmul_one : ∀ x : ℕ, (D - 1) * x + x = D * x := by
      intro x
      rw [Nat.sub_mul]
      have hx : x ≤ D * x := by
        have h := Nat.mul_le_mul_right x hD
        simpa using h
      omega
    have hsum_coord : ∀ (v : List ℕ) (h : v.length = n),
        (List.ofFn (fun i : Fin n => v.get ⟨i.1, by simpa [h] using i.2⟩)).sum = v.sum := by
      intro v h
      subst n
      simpa using congrArg List.sum (List.ofFn_get v)
    have hpsum : (∑ i : Fin n, coord p i) = n := by
      simpa [coord, List.sum_ofFn, p.2.2.2] using hsum_coord p.1 p.2.1
    have hqsum : (∑ i : Fin n, coord q i) = n := by
      simpa [coord, List.sum_ofFn, q.2.2.2] using hsum_coord q.1 q.2.1
    have hdiv : ∀ i : Fin n,
        D * baseFn (D := D) p q i ≤ (D - 1) * coord p i + coord q i := by
      intro i
      dsimp [baseFn]
      exact Nat.mul_div_le _ _
    have hbase_sum_mul : D * (base (D := D) p q).sum ≤ (D - 1) * n + n := by
      have hs : (∑ i : Fin n, D * baseFn (D := D) p q i) ≤
          ∑ i : Fin n, ((D - 1) * coord p i + coord q i) := by
        exact Finset.sum_le_sum (fun i hi => hdiv i)
      rw [show (base (D := D) p q).sum = ∑ i : Fin n, baseFn (D := D) p q i by
        simp [base, List.sum_ofFn]]
      rw [Finset.mul_sum]
      calc
        (∑ i : Fin n, D * baseFn (D := D) p q i) ≤
            ∑ i : Fin n, ((D - 1) * coord p i + coord q i) := hs
        _ = (D - 1) * n + n := by
          rw [Finset.sum_add_distrib]
          have hp' : (∑ i : Fin n, (D - 1) * coord p i) = (D - 1) * n := by
            calc
              (∑ i : Fin n, (D - 1) * coord p i) =
                  (D - 1) * ∑ i : Fin n, coord p i := by
                exact (Finset.mul_sum (s := Finset.univ) (f := coord p)
                  (a := D - 1)).symm
              _ = (D - 1) * n := by rw [hpsum]
          rw [hp', hqsum]
    have hbase_sum_le : (base (D := D) p q).sum ≤ n := by
      have hmul : D * (base (D := D) p q).sum ≤ D * n := by
        calc
          D * (base (D := D) p q).sum ≤ (D - 1) * n + n := hbase_sum_mul
          _ = D * n := hmul_one n
      exact (Nat.le_of_mul_le_mul_left hmul) hD
    have hupper_antitone : (upper (D := D) p q).Pairwise (· ≥ ·) := by
      change (List.ofFn (upperFn (D := D) p q)).Pairwise (· ≥ ·)
      apply (List.pairwise_ofFn).2
      intro i j hij
      change upperFn (D := D) p q i ≥ upperFn (D := D) p q j
      have hp1 : coord p i + 1 ≥ coord p j + 1 := Nat.add_le_add_right (pant hij) 1
      have hq1 : coord q i + (D - 1) ≥ coord q j + (D - 1) :=
        Nat.add_le_add_right (qant hij) (D - 1)
      have hmax : max (coord p i) (coord q i) ≥ max (coord p j) (coord q j) :=
        max_le_max (pant hij) (qant hij)
      exact min_le_min hp1 (min_le_min hq1 hmax)
    have hbase_antitone : (base (D := D) p q).Pairwise (· ≥ ·) := by
      change (List.ofFn (baseFn (D := D) p q)).Pairwise (· ≥ ·)
      apply (List.pairwise_ofFn).2
      intro i j hij
      change baseFn (D := D) p q i ≥ baseFn (D := D) p q j
      apply Nat.div_le_div_right
      exact Nat.add_le_add (Nat.mul_le_mul_left (D - 1) (pant hij)) (qant hij)
    have hbase_lower : ∀ i : Fin n, lowerFn (D := D) p q i ≤ baseFn (D := D) p q i := by
      intro i
      change lowerFn (D := D) p q i ≤ baseFn (D := D) p q i
      apply (Nat.le_div_iff_mul_le hD).2
      have hdiff₁ : coord p i ≤ coord q i + D := by
        have := hcoord i
        omega
      have hdiff₂ : coord q i ≤ coord p i + D := by
        have := hcoord i
        omega
      rw [lowerFn, max_mul, max_mul, max_mul]
      apply max_le
      · omega
      · apply max_le
        · have hp : (coord p i - 1) * D ≤ (D - 1) * coord p i + coord q i := by
            rw [Nat.sub_mul, Nat.sub_mul]
            simp only [Nat.one_mul]
            rw [Nat.mul_comm (coord p i) D]
            omega
          exact hp
        · apply max_le
          · have hq : (coord q i - (D - 1)) * D ≤ (D - 1) * coord p i + coord q i := by
              rw [Nat.sub_mul]
              apply (Nat.sub_le_iff_le_add).2
              have hm := Nat.mul_le_mul_left (D - 1) hdiff₂
              calc
                coord q i * D = (D - 1) * coord q i + coord q i := by
                  rw [Nat.mul_comm]
                  exact (hmul_one (coord q i)).symm
                _ ≤ (D - 1) * (coord p i + D) + coord q i :=
                  Nat.add_le_add_right hm _
                _ = (D - 1) * coord p i + coord q i + (D - 1) * D := by
                  rw [Nat.mul_add]
                  omega
            exact hq
          · by_cases hpq : coord p i ≤ coord q i
            · rw [min_eq_left hpq]
              rw [Nat.sub_mul]
              simp only [Nat.one_mul]
              rw [Nat.mul_comm (coord p i) D]
              omega
            · have hqp : coord q i ≤ coord p i := by omega
              rw [min_eq_right hqp]
              have hm := Nat.mul_le_mul_left (D - 1) hqp
              calc
                coord q i * D = (D - 1) * coord q i + coord q i := by
                  rw [Nat.mul_comm]
                  exact (hmul_one (coord q i)).symm
                _ ≤ (D - 1) * coord p i + coord q i := Nat.add_le_add_right hm _
    have hbase_upper : ∀ i : Fin n, baseFn (D := D) p q i ≤ upperFn (D := D) p q i := by
      intro i
      change baseFn (D := D) p q i ≤ upperFn (D := D) p q i
      apply Nat.div_le_of_le_mul
      have hdiff₁ : coord q i ≤ coord p i + D := by
        have := hcoord i
        omega
      have hdiff₂ : coord p i ≤ coord q i + D := by
        have := hcoord i
        omega
      have h₁ : ((D - 1) * coord p i + coord q i) ≤ D * (coord p i + 1) := by
        calc
          (D - 1) * coord p i + coord q i ≤
              (D - 1) * coord p i + (coord p i + D) :=
            Nat.add_le_add_left hdiff₁ _
          _ = D * (coord p i + 1) := by
            rw [Nat.mul_add]
            simp only [Nat.mul_one]
            calc
              (D - 1) * coord p i + (coord p i + D) =
                  ((D - 1) * coord p i + coord p i) + D := by omega
              _ = D * coord p i + D := by rw [hmul_one]
      have h₂ : ((D - 1) * coord p i + coord q i) ≤ D * (coord q i + (D - 1)) := by
        have hm := Nat.mul_le_mul_left (D - 1) hdiff₂
        calc
          (D - 1) * coord p i + coord q i ≤ (D - 1) * (coord q i + D) + coord q i :=
            Nat.add_le_add_right hm _
          _ = D * (coord q i + (D - 1)) := by
            rw [Nat.mul_add]
            calc
              (D - 1) * coord q i + (D - 1) * D + coord q i =
                  ((D - 1) * coord q i + coord q i) + (D - 1) * D := by omega
              _ = D * coord q i + (D - 1) * D := by rw [hmul_one]
              _ = D * coord q i + D * (D - 1) := by rw [Nat.mul_comm (D - 1) D]
              _ = D * (coord q i + (D - 1)) := by rw [Nat.mul_add]
      have h₃ : ((D - 1) * coord p i + coord q i) ≤ D * max (coord p i) (coord q i) := by
        by_cases hpq : coord p i ≤ coord q i
        · rw [max_eq_right hpq]
          have hm := Nat.mul_le_mul_left (D - 1) hpq
          calc
            (D - 1) * coord p i + coord q i ≤ (D - 1) * coord q i + coord q i :=
              Nat.add_le_add_right hm _
            _ = D * coord q i := by
              exact hmul_one (coord q i)
        · have hqp : coord q i ≤ coord p i := by omega
          rw [max_eq_left hqp]
          have hm : coord q i ≤ coord p i := hqp
          calc
            (D - 1) * coord p i + coord q i ≤ (D - 1) * coord p i + coord p i :=
              Nat.add_le_add_left hm _
            _ = D * coord p i := by
              exact hmul_one (coord p i)
      have h₂' : ((D - 1) * coord p i + coord q i) ≤
          min (D * (coord q i + (D - 1)))
            (D * max (coord p i) (coord q i)) := by
        apply (le_min_iff).2
        exact ⟨h₂, h₃⟩
      change (D - 1) * coord p i + coord q i ≤
        D * min (coord p i + 1) (min (coord q i + (D - 1))
          (max (coord p i) (coord q i)))
      rw [mul_min, mul_min]
      apply (le_min_iff).2
      exact ⟨h₁, h₂'⟩
    have hupper_num : ∀ i : Fin n,
        (D - 1) * coord p i + coord q i ≤ D * upperFn (D := D) p q i := by
      intro i
      unfold upperFn
      rw [mul_min, mul_min]
      apply (le_min_iff).2
      constructor
      · calc
          (D - 1) * coord p i + coord q i ≤
              (D - 1) * coord p i + (coord p i + D) := by
            have hh := hcoord i
            omega
          _ = D * (coord p i + 1) := by
            rw [Nat.mul_add]
            simp only [Nat.mul_one]
            calc
              (D - 1) * coord p i + (coord p i + D) =
                  ((D - 1) * coord p i + coord p i) + D := by omega
              _ = D * coord p i + D := by rw [hmul_one]
      · apply (le_min_iff).2
        constructor
        · have hm := Nat.mul_le_mul_left (D - 1) (by
            have hh := hcoord i
            omega : coord p i ≤ coord q i + D)
          calc
            (D - 1) * coord p i + coord q i ≤
                (D - 1) * (coord q i + D) + coord q i :=
              Nat.add_le_add_right hm _
            _ = D * (coord q i + (D - 1)) := by
              rw [Nat.mul_add]
              calc
                (D - 1) * coord q i + (D - 1) * D + coord q i =
                    ((D - 1) * coord q i + coord q i) + (D - 1) * D := by omega
                _ = D * coord q i + (D - 1) * D := by rw [hmul_one]
                _ = D * coord q i + D * (D - 1) := by rw [Nat.mul_comm (D - 1) D]
                _ = D * (coord q i + (D - 1)) := by rw [Nat.mul_add]
        · by_cases hpq : coord p i ≤ coord q i
          · rw [max_eq_right hpq]
            have hm := Nat.mul_le_mul_left (D - 1) hpq
            calc
              (D - 1) * coord p i + coord q i ≤
                  (D - 1) * coord q i + coord q i := Nat.add_le_add_right hm _
              _ = D * coord q i := hmul_one _
          · have hqp : coord q i ≤ coord p i := by omega
            rw [max_eq_left hqp]
            calc
              (D - 1) * coord p i + coord q i ≤
                  (D - 1) * coord p i + coord p i := Nat.add_le_add_left hqp _
              _ = D * coord p i := hmul_one _
    have hupper_sum_mul : D * n ≤ D * (upper (D := D) p q).sum := by
      have hs : (∑ i : Fin n, ((D - 1) * coord p i + coord q i)) ≤
          (∑ i : Fin n, D * upperFn (D := D) p q i) :=
        Finset.sum_le_sum (fun i hi => hupper_num i)
      have hleft : (∑ i : Fin n, ((D - 1) * coord p i + coord q i)) = D * n := by
        rw [Finset.sum_add_distrib]
        have hp' : (∑ i : Fin n, (D - 1) * coord p i) = (D - 1) * n := by
          calc
            (∑ i : Fin n, (D - 1) * coord p i) =
                (D - 1) * ∑ i : Fin n, coord p i := by
              exact (Finset.mul_sum (s := Finset.univ) (f := coord p)
                (a := D - 1)).symm
            _ = (D - 1) * n := by rw [hpsum]
        rw [hp', hqsum]
        exact hmul_one n
      have hright : (∑ i : Fin n, D * upperFn (D := D) p q i) =
          D * (upper (D := D) p q).sum := by
        calc
          (∑ i : Fin n, D * upperFn (D := D) p q i) =
              D * ∑ i : Fin n, upperFn (D := D) p q i := by
            exact (Finset.mul_sum (s := Finset.univ)
              (f := upperFn (D := D) p q) (a := D)).symm
          _ = D * (upper (D := D) p q).sum := by simp [upper, List.sum_ofFn]
      rw [hleft] at hs
      rw [hright] at hs
      exact hs
    have hp_upper_sum : n ≤ (upper (D := D) p q).sum :=
      (Nat.le_of_mul_le_mul_left hupper_sum_mul) hD
    have hlen_base : (base (D := D) p q).length = n := by simp [base]
    have hlen_upper : (upper (D := D) p q).length = n := by simp [upper]
    have hbase_upper_list : ∀ i : Fin (base (D := D) p q).length,
        (base (D := D) p q).get i ≤
          (upper (D := D) p q).get (Fin.cast (hlen_base.trans hlen_upper.symm) i) := by
      intro i
      have hi_n : i.1 < n := by simpa only [hlen_base] using i.2
      let ib : Fin (List.ofFn (baseFn (D := D) p q)).length :=
        ⟨i.1, by simpa [base] using hi_n⟩
      have hib : i = ib := by apply Fin.ext; rfl
      let iu : Fin (upper (D := D) p q).length :=
        Fin.cast (hlen_base.trans hlen_upper.symm) i
      let ju : Fin (List.ofFn (upperFn (D := D) p q)).length :=
        ⟨i.1, by simpa [upper] using hi_n⟩
      have hju : iu = ju := by apply Fin.ext; rfl
      have hbget : (base (D := D) p q).get i =
          (List.ofFn (baseFn (D := D) p q)).get ib := by
        change (List.ofFn (baseFn (D := D) p q)).get i = _
        rw [hib]
      have huget : (upper (D := D) p q).get iu =
          (List.ofFn (upperFn (D := D) p q)).get ju := by
        change (List.ofFn (upperFn (D := D) p q)).get iu = _
        rw [hju]
      rw [hbget, huget]
      simpa [List.get_ofFn] using hbase_upper (⟨i.1, hi_n⟩ : Fin n)
    have hrem : n - (base (D := D) p q).sum ≤
        (upper (D := D) p q).sum - (base (D := D) p q).sum :=
      Nat.sub_le_sub_right hp_upper_sum _
    let vals : List ℕ := fill (base (D := D) p q) (upper (D := D) p q)
      (n - (base (D := D) p q).sum)
    have hvals_len : vals.length = n := by
      dsimp [vals]
      rw [fill_length (hlen_base.trans hlen_upper.symm), hlen_base]
    have hvals_pair : vals.Pairwise (· ≥ ·) := by
      dsimp [vals]
      apply fill_pairwise (hlen_base.trans hlen_upper.symm)
        hbase_antitone hupper_antitone hbase_upper_list hrem
    have hvals_sum : vals.sum = n := by
      dsimp [vals]
      rw [fill_sum (hlen_base.trans hlen_upper.symm) hbase_upper_list hrem]
      exact Nat.add_sub_of_le hbase_sum_le
    have fill_ge : ∀ {l h : List ℕ} {s : ℕ}, (hlen : l.length = h.length) →
        ∀ i : Fin l.length, l.get i ≤
          (fill l h s).get
            (Fin.cast (fill_length (l := l) (h := h) (r := s) hlen).symm i) := by
      intro l
      induction l with
      | nil =>
          intro h s hlen i
          exact Fin.elim0 i
      | cons a as ih =>
          intro h s hlen i
          cases h with
          | nil => simp at hlen
          | cons b bs =>
              simp only [List.length_cons] at hlen
              have htail := ih (h := bs) (s := s - min s (b - a))
                (Nat.succ.inj hlen)
              rcases i with ⟨i, hi⟩
              cases i with
              | zero =>
                  have hz : Fin.cast
                      (fill_length (l := a :: as) (h := b :: bs) (r := s) hlen).symm
                      ⟨0, hi⟩ = ⟨0, by simp [fill]⟩ := by
                    apply Fin.ext
                    rfl
                  rw [hz]
                  simp [fill]
              | succ i =>
                  have hi' : i < as.length := by simpa using hi
                  have hs : Fin.cast
                      (fill_length (l := a :: as) (h := b :: bs) (r := s) hlen).symm
                      ⟨i + 1, hi⟩ = Fin.succ (Fin.cast
                        (fill_length (l := as) (h := bs)
                          (r := s - min s (b - a)) (Nat.succ.inj hlen)).symm
                        ⟨i, hi'⟩) := by
                    apply Fin.ext
                    rfl
                  rw [hs]
                  simpa [fill] using htail ⟨i, hi'⟩
    have fill_le_point : ∀ {l h : List ℕ} {s : ℕ}, (hlen : l.length = h.length) →
        (∀ i : Fin l.length, l.get i ≤ h.get (Fin.cast hlen i)) →
        ∀ i : Fin l.length, (fill l h s).get
            (Fin.cast (fill_length (l := l) (h := h) (r := s) hlen).symm i) ≤
          h.get (Fin.cast hlen i) := by
      intro l
      induction l with
      | nil =>
          intro h s hlen hle i
          exact Fin.elim0 i
      | cons a as ih =>
          intro h s hlen hle i
          cases h with
          | nil => simp at hlen
          | cons b bs =>
              simp only [List.length_cons] at hlen
              have hab : a ≤ b := by simpa using hle ⟨0, by simp⟩
              have htail := ih (h := bs) (s := s - min s (b - a))
                (Nat.succ.inj hlen) (by
                  intro j
                  simpa using hle ⟨j.1 + 1, by simp [j.2]⟩)
              rcases i with ⟨i, hi⟩
              cases i with
              | zero =>
                  have hz : Fin.cast
                      (fill_length (l := a :: as) (h := b :: bs) (r := s) hlen).symm
                      ⟨0, hi⟩ = ⟨0, by simp [fill]⟩ := by
                    apply Fin.ext
                    rfl
                  rw [hz]
                  simp [fill]
                  have ht := Nat.min_le_right s (b - a)
                  omega
              | succ i =>
                  have hi' : i < as.length := by simpa using hi
                  have hs : Fin.cast
                      (fill_length (l := a :: as) (h := b :: bs) (r := s) hlen).symm
                      ⟨i + 1, hi⟩ = Fin.succ (Fin.cast
                        (fill_length (l := as) (h := bs)
                          (r := s - min s (b - a)) (Nat.succ.inj hlen)).symm
                        ⟨i, hi'⟩) := by
                    apply Fin.ext
                    rfl
                  rw [hs]
                  simpa [fill] using htail ⟨i, hi'⟩
    have hr_bounds : ∀ i : Fin n,
        baseFn (D := D) p q i ≤ coord (listPartition vals hvals_len hvals_pair hvals_sum) i ∧
          coord (listPartition vals hvals_len hvals_pair hvals_sum) i ≤
            upperFn (D := D) p q i := by
      intro i
      let ib : Fin (base (D := D) p q).length :=
        ⟨i.1, by simpa only [hlen_base] using i.2⟩
      let iv : Fin vals.length := ⟨i.1, by simpa only [hvals_len] using i.2⟩
      have hcast : Fin.cast
          (fill_length (l := base (D := D) p q) (h := upper (D := D) p q)
            (r := n - (base (D := D) p q).sum)
            (hlen_base.trans hlen_upper.symm)).symm ib = iv := by
        apply Fin.ext
        rfl
      have hge := fill_ge (l := base (D := D) p q) (h := upper (D := D) p q)
        (s := n - (base (D := D) p q).sum)
        (hlen_base.trans hlen_upper.symm) ib
      have hle := fill_le_point (l := base (D := D) p q) (h := upper (D := D) p q)
        (s := n - (base (D := D) p q).sum)
        (hlen_base.trans hlen_upper.symm) hbase_upper_list ib
      rw [hcast] at hge hle
      have hbcast : Fin.cast (by simp [base] :
          (base (D := D) p q).length =
            (List.ofFn (baseFn (D := D) p q)).length) ib =
          (⟨i.1, by simp [base]⟩ :
            Fin (List.ofFn (baseFn (D := D) p q)).length) := by
        apply Fin.ext
        rfl
      have hbget : (base (D := D) p q).get ib = baseFn (D := D) p q i := by
        change (List.ofFn (baseFn (D := D) p q)).get
          (Fin.cast (by simp [base] :
            (base (D := D) p q).length =
              (List.ofFn (baseFn (D := D) p q)).length) ib) = _
        rw [hbcast, List.get_ofFn]
        apply congrArg (baseFn (D := D) p q)
        apply Fin.ext
        rfl
      have huget : (upper (D := D) p q).get
          (Fin.cast (hlen_base.trans hlen_upper.symm) ib) =
          upperFn (D := D) p q i := by
        have hju : Fin.cast (by simp [upper] :
            (upper (D := D) p q).length =
              (List.ofFn (upperFn (D := D) p q)).length)
            (Fin.cast (hlen_base.trans hlen_upper.symm) ib) =
              (⟨i.1, by simp [upper]⟩ :
                Fin (List.ofFn (upperFn (D := D) p q)).length) := by
          apply Fin.ext
          rfl
        change (List.ofFn (upperFn (D := D) p q)).get
          (Fin.cast (by simp [upper] :
            (upper (D := D) p q).length =
              (List.ofFn (upperFn (D := D) p q)).length)
            (Fin.cast (hlen_base.trans hlen_upper.symm) ib)) = _
        rw [hju, List.get_ofFn]
        apply congrArg (upperFn (D := D) p q)
        apply Fin.ext
        rfl
      rw [hbget] at hge
      rw [huget] at hle
      have hri : coord (listPartition vals hvals_len hvals_pair hvals_sum) i =
          vals.get iv := by
        rfl
      rw [hri]
      change baseFn (D := D) p q i ≤ vals.get iv ∧
        vals.get iv ≤ upperFn (D := D) p q i
      exact ⟨hge, hle⟩
    let r : Partition n := listPartition vals hvals_len hvals_pair hvals_sum
    have hr_bounds' : ∀ i : Fin n,
        baseFn (D := D) p q i ≤ coord r i ∧
          coord r i ≤ upperFn (D := D) p q i := by
      intro i
      simpa [r] using hr_bounds i
    have hlow_p : ∀ i : Fin n, coord p i - 1 ≤ coord r i := by
      intro i
      have hli : coord p i - 1 ≤ lowerFn (D := D) p q i := by
        calc
          coord p i - 1 ≤ max (coord p i - 1)
              (max (coord q i - (D - 1)) (min (coord p i) (coord q i))) :=
            le_max_left _ _
          _ ≤ lowerFn (D := D) p q i := le_max_right _ _
      exact hli.trans ((hbase_lower i).trans (hr_bounds' i).1)
    have hlow_q : ∀ i : Fin n, coord q i - (D - 1) ≤ coord r i := by
      intro i
      have hli : coord q i - (D - 1) ≤ lowerFn (D := D) p q i := by
        calc
          coord q i - (D - 1) ≤
              max (coord q i - (D - 1)) (min (coord p i) (coord q i)) :=
            le_max_left _ _
          _ ≤ max (coord p i - 1)
              (max (coord q i - (D - 1)) (min (coord p i) (coord q i))) :=
            le_max_right _ _
          _ ≤ lowerFn (D := D) p q i := le_max_right _ _
      exact hli.trans ((hbase_lower i).trans (hr_bounds' i).1)
    have hupp_p : ∀ i : Fin n, coord r i ≤ coord p i + 1 := by
      intro i
      have hui : upperFn (D := D) p q i ≤ coord p i + 1 := by
        unfold upperFn
        exact min_le_left _ _
      exact (hr_bounds' i).2.trans hui
    have hupp_q : ∀ i : Fin n, coord r i ≤ coord q i + (D - 1) := by
      intro i
      have hui : upperFn (D := D) p q i ≤ coord q i + (D - 1) := by
        unfold upperFn
        exact (min_le_right _ _).trans (min_le_left _ _)
      exact (hr_bounds' i).2.trans hui
    have hstep : dInf p r ≤ 1 := by
      unfold dInf
      apply Finset.sup_le
      intro i hi
      have h₁ := hlow_p i
      have h₂ := hupp_p i
      apply max_le
      · omega
      · omega
    have hdist_upper : dInf r q ≤ D - 1 := by
      unfold dInf
      apply Finset.sup_le
      intro i hi
      have h₁ := hlow_q i
      have h₂ := hupp_q i
      apply max_le
      · omega
      · omega
    have hn : 0 < n := by
      by_contra hn'
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn'
      have hz : dInf p q = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply Finset.sup_le
        intro i _
        have := i.isLt
        omega
      omega
    let i0 : Fin n := ⟨0, hn⟩
    obtain ⟨i, hi, hsup⟩ :=
      Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin n)))
        (h := ⟨i0, Finset.mem_univ _⟩)
        (f := fun j : Fin n =>
          max (coord p j - coord q j) (coord q j - coord p j))
    have hmax : max (coord p i - coord q i) (coord q i - coord p i) = D := by
      calc
        max (coord p i - coord q i) (coord q i - coord p i) = dInf p q := by
          simpa [dInf] using hsup.symm
        _ = D := hd
    have hdist_lower : D - 1 ≤ dInf r q := by
      by_cases hab : coord p i - coord q i ≤ coord q i - coord p i
      · have hqdiff : coord q i - coord p i = D := by
          rw [max_eq_right hab] at hmax
          exact hmax
        have hrlo := hlow_q i
        have hrup := hupp_p i
        have hqeq : coord q i = coord p i + D := by omega
        have hdiff : coord q i - coord r i = D - 1 := by omega
        have hi_sup := Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n =>
            max (coord r j - coord q j) (coord q j - coord r j))
          (Finset.mem_univ i)
        have hi_sup' : max (coord r i - coord q i) (coord q i - coord r i) ≤
            dInf r q := by
          simpa [dInf] using hi_sup
        calc
          D - 1 = coord q i - coord r i := hdiff.symm
          _ ≤ max (coord r i - coord q i) (coord q i - coord r i) := le_max_right _ _
          _ ≤ dInf r q := hi_sup'
      · have hpq : coord q i - coord p i ≤ coord p i - coord q i := by omega
        have hpdiff : coord p i - coord q i = D := by
          rw [max_eq_left hpq] at hmax
          exact hmax
        have hrlo := hlow_p i
        have hrup := hupp_q i
        have hpeq : coord p i = coord q i + D := by omega
        have hdiff : coord r i - coord q i = D - 1 := by omega
        have hi_sup := Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n =>
            max (coord r j - coord q j) (coord q j - coord r j))
          (Finset.mem_univ i)
        have hi_sup' : max (coord r i - coord q i) (coord q i - coord r i) ≤
            dInf r q := by
          simpa [dInf] using hi_sup
        calc
          D - 1 = coord r i - coord q i := hdiff.symm
          _ ≤ max (coord r i - coord q i) (coord q i - coord r i) := le_max_left _ _
          _ ≤ dInf r q := hi_sup'
    have heq : dInf r q = D - 1 := le_antisymm hdist_upper hdist_lower
    refine ⟨r, hstep, heq, ?_⟩
    intro i
    have hmin : min (coord p i) (coord q i) ≤ lowerFn (D := D) p q i := by
      calc
        min (coord p i) (coord q i) ≤
            max (coord q i - (D - 1)) (min (coord p i) (coord q i)) :=
          le_max_right _ _
        _ ≤ max (coord p i - 1)
            (max (coord q i - (D - 1)) (min (coord p i) (coord q i))) :=
          le_max_right _ _
        _ ≤ lowerFn (D := D) p q i := le_max_right _ _
    have hmaxu : upperFn (D := D) p q i ≤ max (coord p i) (coord q i) := by
      unfold upperFn
      exact (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨hmin.trans ((hbase_lower i).trans (hr_bounds' i).1),
      (hr_bounds' i).2.trans hmaxu⟩
  constructor
  · suffices aux : ∀ D : ℕ, ∀ p q : Partition n,
        dInf p q = D → Nonempty (Path (D := D) p q) by
      exact aux _ p q rfl
    intro D
    induction D with
    | zero =>
        intro p q hd
        have hpq : p = q := by
          apply Subtype.ext
          apply List.ext_get (p.2.1.trans q.2.1.symm)
          intro i hip hiq
          let j : Fin n := ⟨i, by simpa [p.2.1] using hip⟩
          have hh : max (coord p j - coord q j) (coord q j - coord p j) ≤ 0 := by
            have hj : max (coord p j - coord q j) (coord q j - coord p j) ≤
                dInf p q := by
              change max (coord p j - coord q j) (coord q j - coord p j) ≤
                Finset.sup Finset.univ (fun k : Fin n =>
                  max (coord p k - coord q k) (coord q k - coord p k))
              exact Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
                (f := fun k : Fin n =>
                  max (coord p k - coord q k) (coord q k - coord p k))
                (Finset.mem_univ j)
            simpa [hd] using hj
          have he : coord p j = coord q j := by omega
          exact he
        subst q
        refine ⟨⟨fun _ => p, rfl, rfl, ?_, ?_⟩⟩
        · intro k
          exact Fin.elim0 k
        · intro k i
          simp
    | succ D ih =>
        intro p q hd
        obtain ⟨r, hpr, hrq, hr⟩ := partition_one_step p q (Nat.succ_pos D) hd
        have hrq' : dInf r q = D := by simpa using hrq
        obtain ⟨⟨γ, hγ0, hγlast, hγstep, hγbounds⟩⟩ := ih r q hrq'
        refine ⟨⟨Fin.cases p γ, ?_, ?_, ?_, ?_⟩⟩
        · rfl
        · change γ ⟨D, by omega⟩ = q
          exact hγlast
        · intro k
          refine Fin.cases ?_ (fun j => ?_) k
          · change dInf p (γ 0) ≤ 1
            rw [hγ0]
            exact hpr
          · change dInf (γ ⟨j.1, by omega⟩) (γ ⟨j.1 + 1, by omega⟩) ≤ 1
            exact hγstep j
        · intro k
          refine Fin.cases ?_ (fun j => ?_) k
          · intro i
            exact ⟨min_le_left _ _, le_max_left _ _⟩
          · intro i
            change min (coord p i) (coord q i) ≤ coord (γ j) i ∧
              coord (γ j) i ≤ max (coord p i) (coord q i)
            have h₁ := hr i
            have h₂ := hγbounds j i
            omega
  · intro K γ hstart hend hstep
    have coord_bound : ∀ k : Fin (K + 1), ∀ i : Fin n,
        coord (γ 0) i ≤ coord (γ k) i + k.1 ∧
        coord (γ k) i ≤ coord (γ 0) i + k.1 := by
      intro k
      obtain ⟨k, hk⟩ := k
      induction k with
      | zero => intro i; simp
      | succ k ih =>
          intro i
          have prev := ih (by omega) i
          have next : max (coord (γ ⟨k, by omega⟩) i -
                coord (γ ⟨k + 1, hk⟩) i)
              (coord (γ ⟨k + 1, hk⟩) i - coord (γ ⟨k, by omega⟩) i) ≤ 1 :=
            (Finset.le_sup (s := Finset.univ)
              (f := fun j => max (coord (γ ⟨k, by omega⟩) j - coord (γ ⟨k + 1, hk⟩) j)
                (coord (γ ⟨k + 1, hk⟩) j - coord (γ ⟨k, by omega⟩) j))
              (Finset.mem_univ i)).trans (hstep ⟨k, by omega⟩)
          dsimp only at prev ⊢
          omega
    apply Finset.sup_le
    intro i _
    have h := coord_bound ⟨K, by omega⟩ i
    rw [hstart, hend] at h
    dsimp only at h
    omega

end D5.S3.Combinatorics.Partitions.PartitionLInftyGeodesic
