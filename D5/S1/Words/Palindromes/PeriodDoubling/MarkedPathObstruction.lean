/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathObstruction
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedPathObstruction
   mirror-E: none(waiver:unbounded-marked-path-charge)
   anchors: []
   utility: none
   digest: Tight even-weight factorizations bound twice the marked charge by initial charge. -/

/-
proof_shape: content (marked_charge_obstruction)
escape_witness: Induction over tight paths accumulates removed-digit charges with the phase correction.
admission_basis: escape-witness
Direct frozen dependencies: none; the period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPrefixRigidity
import D5.S1.Words.Palindromes.PeriodDoubling.EvenTightPaths
import D5.S1.Words.Palindromes.PeriodDoubling.TightFactorization
namespace D5.S1.Words.Palindromes.PeriodDoubling
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
theorem marked_charge_obstruction (n m q : ℕ) (T : ℤ) (hS : classS n) (hmark : markedPrefix n m q T)
    (hn : n%2 = 0) (hF : signedWeight (((n+1)/2 : ℕ) : ℤ)%2 = 0)
    (hopt : PL (List.ofFn (fun i : Fin n => u_pd i)) = signedWeight (((n+1)/2 : ℕ) : ℤ)) :
    2*(∑ s ∈ Finset.range m,(1+2*(((q+3*s)%2 : ℕ) : ℤ)))≤
      (signedDigitCharge n : ℤ)+(2*((q%2 : ℕ) : ℤ))*(if 2*T-((n%2 : ℕ) : ℤ) < 0 then 1 else 0) := by
  let eta : ℕ → ℤ → ℤ := fun n T => if 2*T-((n%2 : ℕ) : ℤ) < 0 then 1 else 0
  let wp : ℕ → ℤ := fun q => 1+2*((q%2 : ℕ) : ℤ)
  let W : ℕ → ℕ → ℤ := fun m q => ∑ s ∈ Finset.range m,wp (q+3*s)
  have wpos (q : ℕ) : 0 ≤ wp q-1 := by dsimp [wp];omega
  have etapos (n : ℕ) (T : ℤ) : 0 ≤ eta n T := by dsimp [eta];split_ifs <;> omega
  have Wstep (m q : ℕ) (hm : 0 < m) : W m q = wp q+W (m-1) (q+3) := by
    dsimp [W]
    conv_lhs => rw [show m = m-1+1 by omega,Finset.sum_range_succ']
    simp only [Nat.mul_zero,Nat.add_zero]
    have hh : (∑ k ∈ Finset.range (m-1),wp (q+3*(k+1)))=
        ∑ k ∈ Finset.range (m-1),wp (q+3+3*k) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      omega
    rw [hh]
    ring
  have pathbound (cuts : List ℕ) (n m q : ℕ) (T : ℤ) (hS : classS n)
      (hmark : markedPrefix n m q T) (hlast : (n::cuts).getLast?=some 0)
      (hchain : (n::cuts).IsChain (fun s t => t < s ∧
        List.Palindrome (List.ofFn (fun i : Fin (s-t) => u_pd (t+i))) ∧
        signedWeight (((s+1)/2 : ℕ) : ℤ) = signedWeight (((t+1)/2 : ℕ) : ℤ)+1))
      (hodd : (n::cuts).IsChain (fun s t => s%2≠t%2)) :
      2*W m q ≤ (signedDigitCharge n : ℤ)+(wp q-1)*eta n T := by
    induction cuts generalizing n m q T with
    | nil =>
      have hn0 : n = 0 := by simpa using hlast
      by_cases hm : m = 0
      · rw [hm]
        have hW : W 0 q = 0 := by simp [W]
        rw [hW]
        have hp:=mul_nonneg (wpos q) (etapos n T)
        have hQ : (0:ℤ) ≤ (signedDigitCharge n : ℤ) := by positivity
        linarith
      · have hpos := (marked_prefix_tail_bound n m q T (by omega) hmark).2
        omega
    | cons j cuts ih =>
      obtain ⟨⟨hj,hpal,htight⟩,hrest⟩ := List.isChain_cons_cons.mp hchain
      obtain ⟨hpar,hoddrest⟩ := List.isChain_cons_cons.mp hodd
      have hjlast : (j::cuts).getLast?=some 0 := by simpa only [List.getLast?_cons_cons] using hlast
      by_cases hm : m = 0
      · rw [hm]
        have hW : W 0 q = 0 := by simp [W]
        rw [hW]
        have hp:=mul_nonneg (wpos q) (etapos n T)
        have hQ : (0:ℤ) ≤ (signedDigitCharge n : ℤ) := by positivity
        linarith
      · have hSj:=(tight_cut_class_and_Q n j hS hj hpal htight).1
        have hrig:=marked_prefix_rigidity_and_charge n j m q T (by omega) hS hmark hj hpar hpal htight
        dsimp only at hrig
        change (∃ Tj,markedPrefix j m q Tj ∧
          (signedDigitCharge j : ℤ)-(signedDigitCharge n : ℤ)+(wp q-1)*(eta j Tj-eta n T) ≤ 0) ∨
          (markedPrefix j (m-1) (q+3) (-T) ∧ eta n T = 1 ∧ eta j (-T) = 0 ∧
          (signedDigitCharge j : ℤ)-(signedDigitCharge n : ℤ)+wp q+1 ≤ 0) at hrig
        rcases hrig with ⟨Tj,hmarkj,hcharge⟩|⟨hmarkj,hetan,hetaj,hcharge⟩
        · have h:=ih j m q Tj hSj hmarkj hjlast hrest hoddrest
          nlinarith
        · have h:=ih j (m-1) (q+3) (-T) hSj hmarkj hjlast hrest hoddrest
          rw [hetaj,mul_zero,add_zero] at h
          rw [hetan,mul_one,Wstep m q (by omega)]
          linarith
  obtain ⟨cuts,hlast,hchain⟩ := (tight_factorization_iff n).mp hopt
  have hodd:=even_tight_path_has_only_odd_cuts n cuts hS hn hF hlast hchain
  have h:=pathbound cuts n m q T hS hmark hlast hchain hodd
  change 2*W m q ≤ (signedDigitCharge n : ℤ)+(2*((q%2 : ℕ) : ℤ))*eta n T
  have hw : wp q-1 = 2*((q%2 : ℕ) : ℤ) := by dsimp [wp];ring
  rw [hw] at h
  exact h

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marked_charge_obstruction
