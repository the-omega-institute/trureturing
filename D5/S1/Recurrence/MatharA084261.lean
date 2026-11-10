/- GID: D5/S1/Recurrence/MatharA084261
   generality: I
   mirror-B: D5/B/S1/Recurrence/MatharA084261
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal even-binomial-factorial recurrence. -/
/-
proof_shape: result: bind-only
admission_basis: open-problem-resolution (issue #27208)
Direct frozen project dependencies: none; pinned Mathlib identities and normalization.
The sum and universal integer recurrence are the exact designated external event.
The source gives no onset; n >= 3 keeps all predecessor indices nonnegative.
The Reg mirror is an audit attempt, not a declared_validated or publication claim.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! The literal finite sum over the even binomial indices. -/

namespace D5.S1.Recurrence.MatharA084261
open Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range (n/2+1), n.choose (2*k) * k.factorial

def claim : Prop := ∀ n : ℕ, 3 ≤ n →
  2*(a n : ℤ)-4*(a (n-1) : ℤ)+(2-(n:ℤ))*(a (n-2):ℤ)+
    ((n:ℤ)-2)*(a (n-3):ℤ)=0

theorem result : claim := by
  let b (k : ℕ) : ℤ := if k % 2 = 0 then ((k/2).factorial : ℤ) else 0
  let tr (c : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n+1), (n.choose k : ℤ)*c k
  have pas (c : ℕ → ℤ) (n : ℕ) : tr c (n+1) = tr c n + tr (fun k => c (k+1)) n := by
    exact Finset.sum_choose_succ_mul (fun i _ => c i) n
  have brec (k : ℕ) :
      2*b (k+3)+2*b (k+2)-3*b (k+1)-2*b k = (k:ℤ)*b (k+1)+(k:ℤ)*b k := by
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have h0 : (2*m)/2 = m := by omega
      have h1 : (2*m+1)/2 = m := by omega
      have h2 : (2*m+2)/2 = m+1 := by omega
      have h3 : (2*m+3)/2 = m+1 := by omega
      simp [b, h0,h1,h2,h3, Nat.add_mod, Nat.mul_mod, Nat.factorial_succ]
      ring
    · have h0 : (2*m+1)/2 = m := by omega
      have h1 : (2*m+1+1)/2 = m+1 := by omega
      have h2 : (2*m+1+2)/2 = m+1 := by omega
      have h3 : (2*m+1+3)/2 = m+2 := by omega
      simp [b,h0,h1,h2,h3,show m+2=(m+1)+1 by omega, Nat.add_mod, Nat.mul_mod, Nat.factorial_succ]
      ring
  have weighted (n : ℕ) : (n:ℤ)*tr (fun k => b (k+1)) n =
      (∑ k ∈ range (n+1), (n.choose k:ℤ)*((k:ℤ)*b (k+1))) +
      ∑ k ∈ range (n+1), (n.choose k:ℤ)*((k:ℤ)*b k) := by
    let f (k : ℕ) : ℤ := (n.choose k:ℤ)*((k:ℤ)*b k)
    have shift : (∑ k ∈ range (n+1), f (k+1)) = ∑ k ∈ range (n+1), f k := by
      calc
        _ = ∑ k ∈ range (n+2), f k := by
          have h := sum_range_succ' f (n+1)
          simpa only [f, Nat.cast_zero, zero_mul, mul_zero, add_zero] using h.symm
        _ = _ := by rw [show n+2=(n+1)+1 by omega, sum_range_succ]; simp [f]
    have hp : ∀ k ∈ range (n+1), (n:ℤ)*((n.choose k:ℤ)*b (k+1)) =
        (n.choose k:ℤ)*((k:ℤ)*b (k+1))+f (k+1) := by
      intro k hk
      have hk' : k ≤ n := by simpa using mem_range.mp hk
      have h : (n.choose (k+1):ℤ)*(k+1:ℤ) = (n.choose k:ℤ)*((n:ℤ)-k) := by
        have hh := Nat.choose_succ_right_eq n k
        have hh' : (n.choose (k+1):ℤ)*((k+1:ℕ):ℤ) = (n.choose k:ℤ)*((n-k:ℕ):ℤ) := by exact_mod_cast hh
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hk'] using hh'
      dsimp [f]
      push_cast
      linear_combination -b (k+1)*h
    have hs := sum_congr rfl hp
    rw [sum_add_distrib, shift] at hs
    simpa only [tr, mul_sum] using hs
  have elim (n : ℕ) :
      2*tr (fun k => b (k+3)) n + 2*tr (fun k => b (k+2)) n -
        3*tr (fun k => b (k+1)) n-2*tr b n = (n:ℤ)*tr (fun k => b (k+1)) n := by
    have hs : (∑ k ∈ range (n+1),
        (2*((n.choose k:ℤ)*b (k+3))+2*((n.choose k:ℤ)*b (k+2))-
          3*((n.choose k:ℤ)*b (k+1))-2*((n.choose k:ℤ)*b k))) =
        ∑ k ∈ range (n+1), ((n.choose k:ℤ)*((k:ℤ)*b (k+1))+
          (n.choose k:ℤ)*((k:ℤ)*b k)) := by
      apply sum_congr rfl
      intro k hk
      linear_combination (n.choose k:ℤ) * brec k
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hs
    have hw := weighted n
    dsimp [tr] at hw ⊢
    linear_combination hs - hw
  have recurrence (n : ℕ) : 2*tr b (n+3)-4*tr b (n+2)-((n:ℤ)+1)*tr b (n+1)+((n:ℤ)+1)*tr b n=0 := by
    have h2 := pas b (n+2)
    have h1 := pas b (n+1)
    have h0 := pas b n
    have h11 := pas (fun k => b (k+1)) (n+1)
    have h20 := pas (fun k => b (k+2)) n
    have he := elim n
    simp only [Nat.add_assoc, Nat.reduceAdd] at h2 h1 h11 h20
    linear_combination 2*h2-2*h1-((n:ℤ)+3)*h0+2*h11+2*h20+he
  have eq_a (n : ℕ) : tr b n = (a n : ℤ) := by
    dsimp [tr, a]
    push_cast
    apply sum_bij_ne_zero (fun k _ _ => k/2)
    · intro k hk hne
      simp only [mem_range] at hk ⊢
      omega
    · intro k hk hne j hj hjne heq
      have hk0 : k%2=0 := by by_contra h; simp [b,h] at hne
      have hj0 : j%2=0 := by by_contra h; simp [b,h] at hjne
      omega
    · intro j hj hne
      refine ⟨2*j, ?_, ?_, by omega⟩
      · simp only [mem_range] at hj ⊢
        omega
      · simpa [b, Nat.mul_mod] using hne
    · intro k hk hne
      have hk0 : k%2=0 := by by_contra h; simp [b,h] at hne
      have he : 2*(k/2)=k := by omega
      simp [b,hk0,he]
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m, n=m+3 := ⟨n-3,by omega⟩
  have h := recurrence m
  simp_rw [eq_a] at h
  rw [show m+3-1=m+2 by omega, show m+3-2=m+1 by omega,show m+3-3=m by omega]
  push_cast
  linear_combination h

#print axioms result
end D5.S1.Recurrence.MatharA084261
