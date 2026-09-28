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

/-! The source construction fills the lower endpoint greedily from left to
right, spending as much of the remaining mass as the current capacity allows.
The definitions below expose that construction at the coordinate level. -/
def fill (l h : List ℕ) (r : ℕ) : List ℕ :=
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

def algorithmStepValues {n D : ℕ} (f g : Fin n → ℕ) : List ℕ :=
  let l := List.ofFn (fun i =>
    max 0 (max (f i - 1)
      (max (g i - (D - 1)) (min (f i) (g i)))))
  let h := List.ofFn (fun i =>
    min (f i + 1)
      (min (g i + (D - 1)) (max (f i) (g i))))
  fill l h (n - l.sum)

def algorithmStepFn {n D : ℕ} (f g : Fin n → ℕ) : Fin n → ℕ :=
  let v := algorithmStepValues (D := D) f g
  fun i => v.getD i.1 0

/-- One source-algorithm step: form the displayed `l` and `h` bounds and
greedily fill from the smallest index until the fixed mass is reached. -/
def algorithmStep {n D : ℕ} (p q : Partition n) : List ℕ :=
  algorithmStepValues (D := D) (fun i => coord p i) (fun i => coord q i)

/-- The source algorithm iterated for exactly `D` steps.  The first coordinate
function is the initial endpoint; each subsequent one is the greedy step with
the remaining distance as its parameter. -/
def algorithmPathValuesAt {n : ℕ} : (D : ℕ) →
    (Fin n → ℕ) → (Fin n → ℕ) → Fin (D + 1) → List ℕ
  | 0, f, _, _ => List.ofFn f
  | D + 1, f, g, k => Fin.cases (List.ofFn f)
      (fun j => algorithmPathValuesAt D
        (algorithmStepFn (D := D + 1) f g) g j) k

def AlgorithmPath {n D : ℕ} (p q : Partition n) :=
  {G : Path (D := D) p q //
    ∀ k : Fin (D + 1), (G.1 k).1 =
      algorithmPathValuesAt D (fun i => coord p i) (fun i => coord q i) k}

/-- Every pair of fixed-mass partitions has an endpoint-confined path whose
length is its maximum coordinate difference. -/
theorem partition_lInf_geodesic {n : ℕ} (p q : Partition n) :
    Nonempty (Path (D := dInf p q) p q) ∧
      Nonempty (AlgorithmPath (D := dInf p q) p q) ∧
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
          coord r i ≤ max (coord p i) (coord q i)) ∧
        r.1 = algorithmStep (D := D) p q := by
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
    have hbase_upper : ∀ i : Fin n, baseFn (D := D) p q i ≤ upperFn (D := D) p q i := by
      intro i
      exact Nat.div_le_of_le_mul (hupper_num i)
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
    have hlower_antitone : (List.ofFn (lowerFn (D := D) p q)).Pairwise (· ≥ ·) := by
      apply (List.pairwise_ofFn).2
      intro i j hij
      unfold lowerFn
      apply max_le_max
      · exact le_rfl
      · apply max_le_max
        · exact Nat.sub_le_sub_right (pant hij) _
        · apply max_le_max
          · exact Nat.sub_le_sub_right (qant hij) _
          · exact min_le_min (pant hij) (qant hij)
    have hlen_lower : (List.ofFn (lowerFn (D := D) p q)).length = n := by simp
    have hlower_base_list : ∀ i : Fin (List.ofFn (lowerFn (D := D) p q)).length,
        (List.ofFn (lowerFn (D := D) p q)).get i ≤
          (base (D := D) p q).get (Fin.cast (hlen_lower.trans hlen_base.symm) i) := by
      intro i
      have hi : i.1 < n := by simpa [hlen_lower] using i.2
      let ii : Fin n := ⟨i.1, hi⟩
      have hcast : i = (⟨i.1, by simpa [hlen_lower] using i.2⟩ : Fin (List.ofFn (lowerFn (D := D) p q)).length) := by
        apply Fin.ext
        rfl
      rw [hcast]
      have hbasecast : Fin.cast (hlen_lower.trans hlen_base.symm)
          (⟨i.1, by simpa [hlen_lower] using i.2⟩ :
            Fin (List.ofFn (lowerFn (D := D) p q)).length) =
          (⟨i.1, by simpa [base] using hi⟩ : Fin (List.ofFn (baseFn (D := D) p q)).length) := by
        apply Fin.ext
        rfl
      rw [hbasecast]
      simpa [base] using hbase_lower ii
    have hlower_sum : (List.ofFn (lowerFn (D := D) p q)).sum ≤ n := by
      have hle := list_sum_le (l := List.ofFn (lowerFn (D := D) p q))
        (h := base (D := D) p q) (hlen := hlen_lower.trans hlen_base.symm)
        (hle := hlower_base_list)
      exact hle.trans hbase_sum_le
    have hlower_upper_list : ∀ i : Fin (List.ofFn (lowerFn (D := D) p q)).length,
        (List.ofFn (lowerFn (D := D) p q)).get i ≤
          (upper (D := D) p q).get
            (Fin.cast (hlen_lower.trans hlen_upper.symm) i) := by
      intro i
      exact (hlower_base_list i).trans
        (hbase_upper_list (Fin.cast (hlen_lower.trans hlen_base.symm) i))
    have hlower_rem : n - (List.ofFn (lowerFn (D := D) p q)).sum ≤
        (upper (D := D) p q).sum - (List.ofFn (lowerFn (D := D) p q)).sum := by
      exact Nat.sub_le_sub_right hp_upper_sum _
    let algVals : List ℕ := fill (List.ofFn (lowerFn (D := D) p q))
      (upper (D := D) p q) (n - (List.ofFn (lowerFn (D := D) p q)).sum)
    have halg_len : algVals.length = n := by
      dsimp [algVals]
      rw [fill_length (hlen_lower.trans hlen_upper.symm), hlen_lower]
    have halg_pair : algVals.Pairwise (· ≥ ·) := by
      dsimp [algVals]
      exact fill_pairwise (hlen_lower.trans hlen_upper.symm) hlower_antitone
        hupper_antitone hlower_upper_list hlower_rem
    have halg_sum : algVals.sum = n := by
      dsimp [algVals]
      rw [fill_sum (hlen_lower.trans hlen_upper.symm) hlower_upper_list hlower_rem]
      exact Nat.add_sub_of_le hlower_sum
    let alg : Partition n := listPartition algVals halg_len halg_pair halg_sum
    have halg_bounds : ∀ i : Fin n,
        lowerFn (D := D) p q i ≤ coord alg i ∧
          coord alg i ≤ upperFn (D := D) p q i := by
      intro i
      let il : Fin (List.ofFn (lowerFn (D := D) p q)).length :=
        ⟨i.1, by rw [hlen_lower]; exact i.2⟩
      let ia : Fin algVals.length := ⟨i.1, by rw [halg_len]; exact i.2⟩
      have hcast : Fin.cast
          (fill_length (l := List.ofFn (lowerFn (D := D) p q))
            (h := upper (D := D) p q)
            (r := n - (List.ofFn (lowerFn (D := D) p q)).sum)
            (hlen_lower.trans hlen_upper.symm)).symm il = ia := by
        apply Fin.ext
        rfl
      have hge := fill_ge (l := List.ofFn (lowerFn (D := D) p q))
        (h := upper (D := D) p q)
        (s := n - (List.ofFn (lowerFn (D := D) p q)).sum)
        (hlen_lower.trans hlen_upper.symm) il
      have hle := fill_le_point (l := List.ofFn (lowerFn (D := D) p q))
        (h := upper (D := D) p q)
        (s := n - (List.ofFn (lowerFn (D := D) p q)).sum)
        (hlen_lower.trans hlen_upper.symm) hlower_upper_list il
      rw [hcast] at hge hle
      have hlow_get : (List.ofFn (lowerFn (D := D) p q)).get il = lowerFn (D := D) p q i := by
        change (List.ofFn (lowerFn (D := D) p q)).get il = _
        simp [il, List.get_ofFn]
      have hupp_get : (upper (D := D) p q).get
          (Fin.cast (hlen_lower.trans hlen_upper.symm) il) = upperFn (D := D) p q i := by
        have hcast_u : Fin.cast (hlen_lower.trans hlen_upper.symm) il =
            (⟨i.1, by rw [hlen_upper]; exact i.2⟩ : Fin (upper (D := D) p q).length) := by
          apply Fin.ext
          rfl
        rw [hcast_u]
        change (List.ofFn (upperFn (D := D) p q)).get _ = _
        simp [upper, List.get_ofFn]
      change lowerFn (D := D) p q i ≤ algVals.get ia ∧
        algVals.get ia ≤ upperFn (D := D) p q i
      constructor
      · simpa [algVals, hlow_get] using hge
      · have hle' : algVals.get ia ≤
            (upper (D := D) p q).get (Fin.cast (hlen_lower.trans hlen_upper.symm) il) := by
          simpa [algVals] using hle
        rw [hupp_get] at hle'
        exact hle'
    have alg_low_p : ∀ i : Fin n, coord p i - 1 ≤ coord alg i := by
      intro i
      have hA : coord p i - 1 ≤ lowerFn (D := D) p q i := by
        unfold lowerFn
        calc
          coord p i - 1 ≤ max (coord p i - 1)
              (max (coord q i - (D - 1)) (min (coord p i) (coord q i))) := le_max_left _ _
          _ ≤ max 0 (max (coord p i - 1)
              (max (coord q i - (D - 1)) (min (coord p i) (coord q i)))) := le_max_right _ _
      exact hA.trans (halg_bounds i).1
    have alg_low_q : ∀ i : Fin n, coord q i - (D - 1) ≤ coord alg i := by
      intro i
      have hB : coord q i - (D - 1) ≤ lowerFn (D := D) p q i := by
        unfold lowerFn
        calc
          coord q i - (D - 1) ≤ max (coord q i - (D - 1))
              (min (coord p i) (coord q i)) := le_max_left _ _
          _ ≤ max (coord p i - 1)
              (max (coord q i - (D - 1)) (min (coord p i) (coord q i))) := le_max_right _ _
          _ ≤ max 0 (max (coord p i - 1)
              (max (coord q i - (D - 1)) (min (coord p i) (coord q i)))) := le_max_right _ _
      exact hB.trans (halg_bounds i).1
    have alg_upp_p : ∀ i : Fin n, coord alg i ≤ coord p i + 1 := by
      intro i
      exact (halg_bounds i).2.trans (min_le_left _ _)
    have alg_upp_q : ∀ i : Fin n, coord alg i ≤ coord q i + (D - 1) := by
      intro i
      exact (halg_bounds i).2.trans ((min_le_right _ _).trans (min_le_left _ _))
    have alg_step : dInf p alg ≤ 1 := by
      unfold dInf
      apply Finset.sup_le
      intro i hi
      have h₁ := alg_low_p i
      have h₂ := alg_upp_p i
      apply max_le <;> omega
    have alg_dist_upper : dInf alg q ≤ D - 1 := by
      unfold dInf
      apply Finset.sup_le
      intro i hi
      have h₁ := alg_low_q i
      have h₂ := alg_upp_q i
      apply max_le <;> omega
    have alg_dist_lower : D - 1 ≤ dInf alg q := by
      by_cases hab : coord p i - coord q i ≤ coord q i - coord p i
      · have hqdiff : coord q i - coord p i = D := by
          rw [max_eq_right hab] at hmax
          exact hmax
        have hqeq : coord q i = coord p i + D := by omega
        have h₁ := alg_low_q i
        have h₂ := alg_upp_p i
        have hdiff : coord q i - coord alg i = D - 1 := by omega
        have hi_sup := Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => max (coord alg j - coord q j) (coord q j - coord alg j))
          (Finset.mem_univ i)
        have hi_sup' : max (coord alg i - coord q i) (coord q i - coord alg i) ≤ dInf alg q := by
          simpa [dInf] using hi_sup
        exact hdiff ▸ (le_max_right _ _).trans hi_sup'
      · have hpq : coord q i - coord p i ≤ coord p i - coord q i := by omega
        have hpdiff : coord p i - coord q i = D := by
          rw [max_eq_left hpq] at hmax
          exact hmax
        have hpeq : coord p i = coord q i + D := by omega
        have h₁ := alg_low_p i
        have h₂ := alg_upp_q i
        have hdiff : coord alg i - coord q i = D - 1 := by omega
        have hi_sup := Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => max (coord alg j - coord q j) (coord q j - coord alg j))
          (Finset.mem_univ i)
        have hi_sup' : max (coord alg i - coord q i) (coord q i - coord alg i) ≤ dInf alg q := by
          simpa [dInf] using hi_sup
        exact hdiff ▸ (le_max_left _ _).trans hi_sup'
    have alg_dist : dInf alg q = D - 1 := le_antisymm alg_dist_upper alg_dist_lower
    have alg_conf : ∀ i : Fin n,
        min (coord p i) (coord q i) ≤ coord alg i ∧
          coord alg i ≤ max (coord p i) (coord q i) := by
      intro i
      have hmin : min (coord p i) (coord q i) ≤ lowerFn (D := D) p q i := by
        exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      have hmaxu : upperFn (D := D) p q i ≤ max (coord p i) (coord q i) := by
        exact (min_le_right _ _).trans (min_le_right _ _)
      exact ⟨hmin.trans (halg_bounds i).1, (halg_bounds i).2.trans hmaxu⟩
    have alg_coord : alg.1 = algorithmStep (D := D) p q := by
      rfl
    refine ⟨alg, alg_step, alg_dist, alg_conf, alg_coord⟩
  have algorithm_aux : ∀ D : ℕ, ∀ p q : Partition n,
      dInf p q = D → Nonempty (AlgorithmPath (D := D) p q) := by
    intro D
    induction D with
    | zero =>
        intro p q hd
        have hpq : p = q := by
          apply Subtype.ext
          apply List.ext_get (p.2.1.trans q.2.1.symm)
          intro i hip hiq
          let j : Fin n := ⟨i, by simpa [p.2.1] using hip⟩
          have hj : max (coord p j - coord q j) (coord q j - coord p j) ≤ dInf p q := by
            exact Finset.le_sup (s := (Finset.univ : Finset (Fin n)))
              (f := fun k : Fin n => max (coord p k - coord q k) (coord q k - coord p k))
              (Finset.mem_univ j)
          have he0 : coord p j - coord q j = 0 ∧ coord q j - coord p j = 0 := by
            simpa [hd] using hj
          have he : coord p j = coord q j := by omega
          exact he
        subst q
        refine ⟨⟨⟨fun _ => p, ?_⟩, ?_⟩⟩
        · exact ⟨rfl, rfl, by intro k; exact Fin.elim0 k, by intro k i; simp⟩
        · intro k
          simp only [algorithmPathValuesAt]
          apply List.ext_get
          · simp [p.2.1]
          · intro i hi₁ hi₂
            have hi_n : i < n := by simpa [p.2.1] using hi₁
            simp [coord, hi_n]
    | succ D ih =>
        intro p q hd
        obtain ⟨r, hpr, hrq, hrest⟩ := partition_one_step p q (Nat.succ_pos D) hd
        obtain ⟨hr, hr_alg⟩ := hrest
        have hrq' : dInf r q = D := by simpa using hrq
        obtain ⟨⟨⟨γ, hγpath⟩, hγalg⟩⟩ := ih r q hrq'
        rcases hγpath with ⟨hγ0, hγlast, hγstep, hγbounds⟩
        have hstep_fn : (fun i => coord r i) = algorithmStepFn
            (D := Nat.succ D) (fun i => coord p i) (fun i => coord q i) := by
          funext i
          have hi : i.1 < r.1.length := by simpa [r.2.1] using i.2
          calc
            coord r i = r.1.getD i.1 0 := by
              simpa [coord] using
                (List.getD_eq_get r.1 0 ⟨i.1, hi⟩).symm
            _ = (algorithmStep (D := Nat.succ D) p q).getD i.1 0 := by
              exact congrArg (fun v : List ℕ => v.getD i.1 0) hr_alg
            _ = algorithmStepFn (D := Nat.succ D)
                (fun i => coord p i) (fun i => coord q i) i := by
              simp [algorithmStepFn, algorithmStep]
        refine ⟨⟨⟨Fin.cases p γ, ?_⟩, ?_⟩⟩
        · refine ⟨rfl, ?_, ?_, ?_⟩
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
              have h₁ := hr i
              have h₂ := hγbounds j i
              constructor
              · by_cases hpq : coord p i ≤ coord q i
                · rw [min_eq_left hpq] at h₁ ⊢
                  exact (le_min h₁.1 hpq).trans h₂.1
                · have hqp : coord q i ≤ coord p i := by omega
                  rw [min_eq_right hqp] at h₁ ⊢
                  exact (le_min h₁.1 le_rfl).trans h₂.1
              · by_cases hpq : coord p i ≤ coord q i
                · rw [max_eq_right hpq] at h₁ ⊢
                  exact h₂.2.trans (max_le h₁.2 le_rfl)
                · have hqp : coord q i ≤ coord p i := by omega
                  rw [max_eq_left hqp] at h₁ ⊢
                  exact h₂.2.trans (max_le h₁.2 hqp)
        · intro k
          refine Fin.cases ?_ (fun j => ?_) k
          · simp only [Fin.cases_zero, algorithmPathValuesAt]
            apply List.ext_get
            · simp [p.2.1]
            · intro i hi₁ hi₂
              have hi_n : i < n := by simpa [p.2.1] using hi₁
              simp [coord, hi_n]
          · change (γ j).1 = algorithmPathValuesAt (Nat.succ D)
              (fun i => coord p i) (fun i => coord q i) ⟨j.1 + 1, by omega⟩
            have hk : (⟨j.1 + 1, by omega⟩ : Fin (Nat.succ (D + 1))) = Fin.succ j := by
              apply Fin.ext
              rfl
            rw [hk]
            simp only [algorithmPathValuesAt]
            rw [← hstep_fn]
            exact hγalg j
  obtain ⟨algPath⟩ := algorithm_aux _ p q rfl
  constructor
  · exact ⟨algPath.1⟩
  · constructor
    · exact ⟨algPath⟩
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
