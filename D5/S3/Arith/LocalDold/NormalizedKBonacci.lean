/- GID: D5/S3/Arith/LocalDold/NormalizedKBonacci
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/NormalizedKBonacci
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized k-bonacci sequences have exact parity block rank k+1. -/
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic

/-! The impulse sequence is defined by Mathlib's actual recurrence constructor.
It is not the positive-seed scalar domain of KBonacciShifts. -/
set_option autoImplicit false
namespace D5.S3.Arith.LocalDold.NormalizedKBonacci

private def recurrence (k : ℕ) : LinearRecurrence ℕ := ⟨k, fun _ => 1⟩

/-- U(0)=...=U(k-2)=0, U(k-1)=1, followed by summation of the last k terms. -/
noncomputable def term (k : ℕ) : ℕ → ℕ :=
  (recurrence k).mkSol (fun i => if i.val+1=k then 1 else 0)

private theorem initial (k i : ℕ) (hi : i < k) :
    term k i = if i+1=k then 1 else 0 :=
  (recurrence k).mkSol_eq_init _ ⟨i,hi⟩

private theorem recurs (k n : ℕ) :
    term k (n+k) = ∑ j : Fin k, term k (n+j.val) := by
  have h := (recurrence k).is_sol_mkSol
    (fun i => if i.val+1=k then 1 else 0) n
  change term k (n+k) = ∑ j : Fin k, (1 : ℕ) * term k (n+j.val) at h
  simpa only [one_mul] using h

/-- The shifted recurrence difference, over the actual natural sequence. -/
theorem difference {k : ℕ} (hk : 0 < k) (m : ℕ) :
    term k (m+k+1) + term k m = 2*term k (m+k) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [Nat.succ_eq_add_one]
  have h0 := recurs (n+1) m
  have h1 := recurs (n+1) (m+1)
  rw [Fin.sum_univ_succ] at h0
  rw [Fin.sum_univ_castSucc] at h1
  have hs : (∑ j : Fin n, term (n+1) (m+j.succ.val)) =
      ∑ j : Fin n, term (n+1) (m+1+j.castSucc.val) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp
    omega
  simp only [Fin.val_zero,add_zero] at h0
  simp only [Fin.val_last] at h1
  rw [hs] at h0
  rw [show m+1+(n+1) = m+(n+1)+1 by omega,
    show m+1+n = m+(n+1) by omega] at h1
  omega

private theorem at_order {k : ℕ} (hk : 0 < k) : term k k = 1 := by
  have h := recurs k 0
  simp only [zero_add] at h
  rw [h]
  let j : Fin k := ⟨k-1,by omega⟩
  calc
    (∑ i : Fin k, term k i.val) = term k j.val := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        rw [initial k i.val i.isLt]
        apply ite_eq_right
        intro he
        apply hij
        apply Fin.ext
        dsimp [j]
        omega
      · simp
    _ = 1 := by
      rw [initial k j.val j.isLt]
      simp [j,show k-1+1=k by omega]

/-- Exact parity of every term, not a checked finite prefix. -/
theorem term_parity {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    term k n % 2 = if n % (k+1) < k-1 then 0 else 1 := by
  have hp : Function.Periodic (fun n => term k n % 2) (k+1) := by
    intro m
    change term k (m+(k+1)) % 2 = term k m % 2
    have h := difference (by omega : 0 < k) m
    rw [show m+(k+1)=m+k+1 by omega]
    omega
  rw [← hp.map_mod_nat n]
  have hr := Nat.mod_lt n (by omega : 0 < k+1)
  by_cases hl : n % (k+1) < k
  · rw [initial k _ hl]
    split_ifs <;> omega
  · have he : n % (k+1)=k := by omega
    rw [he,at_order (by omega : 0 < k)]
    simp

/-- The actual gcd of k-1 successive terms. -/
noncomputable def blockGcd (k n : ℕ) : ℕ :=
  (Finset.range (k-1)).gcd (fun j => term k (n+j))

/-- The exact mod-two block-zero rank is k+1 in every order k>=2. -/
theorem block_even_iff {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    2 ∣ blockGcd k n ↔ k+1 ∣ n := by
  rw [blockGcd, Finset.dvd_gcd_iff]
  constructor
  · intro h
    have hr := Nat.mod_lt n (by omega : 0 < k+1)
    by_contra hd
    have hn0 : n % (k+1) ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hd
    let j := k-1-(n % (k+1))
    have hj : j < k-1 := by dsimp [j]; omega
    have hp := h j (Finset.mem_range.mpr hj)
    rw [Nat.dvd_iff_mod_eq_zero, term_parity hk] at hp
    have hmod : (n+j) % (k+1) ≥ k-1 := by
      by_cases ht : n % (k+1) < k-1
      · have he : n % (k+1)+j=k-1 := by dsimp [j]; omega
        rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : j < k+1),he,
          Nat.mod_eq_of_lt (by omega : k-1 < k+1)]
      · have hj0 : j=0 := by dsimp [j];omega
        simp [hj0]
        omega
    simp [Nat.not_lt.mpr hmod] at hp
  · intro hd j hj
    rw [Nat.dvd_iff_mod_eq_zero,term_parity hk]
    have hn0 := Nat.mod_eq_zero_of_dvd hd
    have hjlt := Finset.mem_range.mp hj
    have he : (n+j) % (k+1)=j := by
      rw [Nat.add_mod,hn0,zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega : j<k+1)]
    simp [he,hjlt]

/-- Positivity begins at the final impulse coordinate and persists forever. -/
theorem positive_tail {k : ℕ} (hk : 2 ≤ k) :
    ∀ n : ℕ, k-1 ≤ n → 0 < term k n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hl : n < k
    · rw [initial k n hl, ite_eq_left (by omega)]
      omega
    · let j : Fin k := ⟨k-1,by omega⟩
      have hj : n-k+j.val < n := by dsimp [j];omega
      have hp := ih (n-k+j.val) hj (by dsimp [j];omega)
      have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
        Nat.zero_le (term k (n-k+i.val))) (Finset.mem_univ j)
      have hr := recurs k (n-k)
      rw [Nat.sub_add_cancel (by omega : k ≤ n)] at hr
      omega

/-- Every positive-index block has strictly positive gcd, so its valuations are finite. -/
theorem block_positive {k : ℕ} (hk : 2 ≤ k) {n : ℕ} (hn : 0 < n) :
    0 < blockGcd k n := by
  let j := if k-1 ≤ n then 0 else k-1-n
  have hj : j < k-1 := by dsimp [j];split_ifs <;> omega
  have ht : k-1 ≤ n+j := by dsimp [j];split_ifs <;> omega
  have hp := positive_tail hk (n+j) ht
  have hd : blockGcd k n ∣ term k (n+j) :=
    Finset.gcd_dvd (Finset.mem_range.mpr hj)
  by_contra h
  have hz : blockGcd k n = 0 := by omega
  rw [hz,zero_dvd_iff] at hd
  omega

private theorem early_powers {k : ℕ} (hk : 2 ≤ k) (t : ℕ) :
    t ≤ k-1 → term k (k+t) = 2^t := by
  induction t with
  | zero => intro _;simpa using at_order (by omega : 0 < k)
  | succ t ih =>
    intro ht
    have hz : term k t=0 := by
      rw [initial k t (by omega),ite_eq_right (by omega)]
    have hd := difference (by omega : 0 < k) t
    rw [hz,add_zero] at hd
    calc
      term k (k+(t+1)) = 2*term k (k+t) := by
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hd
      _ = 2^(t+1) := by rw [ih (by omega),pow_succ];ring

/-- The first nontrivial even block has gcd exactly two in every order. -/
theorem first_even_block {k : ℕ} (hk : 2 ≤ k) : blockGcd k (k+1) = 2 := by
  have hs : term k (k+1)=2 := by
    simpa using early_powers hk 1 (by omega)
  apply Nat.dvd_antisymm
  · rw [← hs]
    have h := (Finset.gcd_dvd (s := Finset.range (k-1))
      (f := fun j => term k (k+1+j)) (Finset.mem_range.mpr (by omega : 0<k-1)))
    simpa [blockGcd] using h
  · exact (block_even_iff hk (k+1)).mpr dvd_rfl

#print axioms positive_tail
#print axioms block_positive
#print axioms first_even_block

#print axioms difference
#print axioms term_parity
#print axioms block_even_iff
end D5.S3.Arith.LocalDold.NormalizedKBonacci
