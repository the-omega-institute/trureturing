/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SparseExactDiagonal
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SparseExactDiagonal
   mirror-E: none(waiver:unbounded-sparse-family-exact-values)
   anchors: []
   utility: none
   digest: The sparse diagonal value is exactly three times its positive odd upper-block count. -/

/-
proof_shape: content (diagonal_exact_family)
escape_witness: A marked-path charge obstruction excludes signed-weight optimality on the sparse diagonal.
admission_basis: escape-witness
Direct frozen dependencies: none; the period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SparseInitialArithmetic
import D5.S1.Words.Palindromes.PeriodDoubling.MarkedPathObstruction
import D5.S1.Words.Palindromes.PeriodDoubling.SparseFamilyUpper
namespace D5.S1.Words.Palindromes.PeriodDoubling
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
theorem diagonal_exact_family (a : ℕ) (ha : 0<a) (hao : a%2=1) :
    let N : ℕ → ℕ → ℕ := fun a b =>
      (∑ i ∈ Finset.range a,2^(2*b+2+3*i)) + (∑ j ∈ Finset.range b,2^(2*j+1))
    PL (List.ofFn (fun i : Fin (N a (2*a-1)) => u_pd i)) = 3*a := by
  let b:=2*a-1
  let n:=(∑ i ∈ Finset.range a,2^(2*b+2+3*i)) + (∑ j ∈ Finset.range b,2^(2*j+1))
  let T:ℤ:=((∑ j ∈ Finset.range b,2^(2*j) : ℕ) : ℤ)
  let q:=2*b+1
  have hbo : b%2=1 := by dsimp [b];omega
  obtain ⟨hn,hF,hS,hQ,hm⟩ := sparse_initial_arithmetic a b
  change n%2=0 at hn
  change signedWeight (((n+1)/2 : ℕ) : ℤ)=a+b at hF
  change classS n at hS
  change signedDigitCharge n=2*a+a%2+b at hQ
  change markedPrefix n a q T at hm
  have W (a q : ℕ) :
      (∑ s ∈ Finset.range a,(1+2*(((q+3*s)%2 : ℕ) : ℤ)))=
        2*(a : ℤ)+(2*((q%2 : ℕ) : ℤ)-1)*((a%2 : ℕ) : ℤ) := by
    induction a generalizing q with
    | zero => simp
    | succ a ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.mul_zero,Nat.add_zero]
      have shift : (∑ s ∈ Finset.range a,(1+2*(((q+3*(s+1))%2 : ℕ) : ℤ)))=
          ∑ s ∈ Finset.range a,(1+2*(((q+3+3*s)%2 : ℕ) : ℤ)) := by
        apply Finset.sum_congr rfl
        intro s hs
        congr 2
        omega
      rw [shift,ih]
      have hq : (((q+3)%2 : ℕ) : ℤ)=1-((q%2 : ℕ) : ℤ) := by omega
      have ha : (((a+1)%2 : ℕ) : ℤ)=1-((a%2 : ℕ) : ℤ) := by omega
      rw [hq,ha]
      push_cast
      ring
  have hlower:=palindromic_suffix_signed_bound.2 n
  rw [hF] at hlower
  have hu:=sparse_family_upper a b 0 ha hao hbo (by dsimp [b];omega) (by decide)
  dsimp only at hu
  change PL (List.ofFn (fun i : Fin (n+0) => u_pd i)) ≤ _ at hu
  simp only [Nat.add_zero,show b=2*a-1 from rfl,if_true] at hu
  have hne : PL (List.ofFn (fun i : Fin n => u_pd i)) ≠ a+b := by
    intro he
    have hfe : signedWeight (((n+1)/2 : ℕ) : ℤ)%2=0 := by rw [hF];omega
    have h:=marked_charge_obstruction n a q T hS hm hn hfe (he.trans hF.symm)
    rw [W,hQ,hao] at h
    have hq : q%2=1 := by dsimp [q];omega
    have ht : 0 ≤ T := by dsimp [T];positivity
    have he : ¬2*T-((n%2 : ℕ) : ℤ)<0 := by rw [hn];simp only [Nat.cast_zero,sub_zero];linarith
    rw [if_neg he,hq] at h
    dsimp [b] at h
    push_cast at h
    omega
  change PL (List.ofFn (fun i : Fin n => u_pd i))=3*a
  dsimp [b] at hlower hne
  omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.diagonal_exact_family
