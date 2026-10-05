/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank
   mirror-E: none(waiver:unbounded-rational-kernel-rank)
   anchors: []
   utility: none
   digest: Sparse-family evaluations force infinite rational dimension of the PPL binary kernel. -/

/-
proof_shape: content (stronger_PPL_kernel_span; support expanded within this delivery)
escape_witness: Exact sparse-family costs produce unbounded unit triangular evaluation rank.
admission_basis: escape-witness
Direct frozen dependencies: D5/S1/Words/Palindromes/FridPrefix/PalindromicLength.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SparseExactDiagonal
import D5.S1.Words.Palindromes.PeriodDoubling.SparseExactOffDiagonal
import D5.S1.Words.Palindromes.PeriodDoubling.KernelSpan
namespace D5.S1.Words.Palindromes.PeriodDoubling

open D5.S1.Words.FridPrefix (PL PalFactors)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0
theorem stronger_PPL_kernel_span :
    let P : ℕ → ℕ := fun n => PL (List.ofFn (fun i : Fin n => u_pd i))
    ¬FiniteDimensional ℚ (Submodule.span ℚ (twoKernel (fun n => (P n : ℚ)))) := by
  dsimp only
  let P : ℕ → ℚ := fun n => (PL (List.ofFn (fun i : Fin n => u_pd i)) : ℚ)
  let a : ℕ → ℕ := fun i => 2*i+1
  let b : ℕ → ℕ := fun j => 4*j+1
  let r : ℕ → ℕ := fun c => ∑ k ∈ Finset.range c,2^(2*k+1)
  let A : ℕ → ℕ := fun p => ∑ k ∈ Finset.range p,2^(2+3*k)
  let N : ℕ → ℕ → ℕ := fun p c =>
    (∑ k ∈ Finset.range p,2^(2*c+2+3*k)) + r c
  let f : ℕ → ℕ → ℚ := fun j n => P (2^(2*b j)*n+r (b j))
  have residue (c : ℕ) : r c < 2^(2*c) := by
    induction c with
    | zero => simp [r]
    | succ c ih =>
      have hh : r (c+1)=r c+2^(2*c+1) := by dsimp [r];rw [Finset.sum_range_succ]
      have hp : 2^(2*(c+1))=4*2^(2*c) := by
        rw [show 2*(c+1)=2*c+2 by omega,pow_add]
        ring
      rw [hh,hp,pow_succ]
      omega
  have address (p c : ℕ) : 2^(2*c)*A p+r c=N p c := by
    dsimp [A,N]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [←pow_add]
    congr 1
    omega
  change ¬FiniteDimensional ℚ (Submodule.span ℚ (twoKernel P))
  have triangular_evaluation_span_infinite (S : Set (ℕ → ℚ))
      (f : ℕ → ℕ → ℚ) (x : ℕ → ℕ) (a b : ℕ → ℚ)
      (hf : ∀ j, f j ∈ S)
      (habove : ∀ i j, i < j → f j (x i) = a i + b j)
      (hdiag : ∀ i, f i (x i) = a i + b i + 1) :
      ¬FiniteDimensional ℚ (Submodule.span ℚ S) := by
    classical
    intro hfinite
    letI := hfinite
    let E : (ℕ → ℚ) →ₗ[ℚ] (ℕ → ℚ) := LinearMap.funLeft ℚ ℚ x
    let W : Submodule ℚ (ℕ → ℚ) :=
      (Submodule.span ℚ S).map E ⊔ Submodule.span ℚ {a, fun _ => 1}
    have hpair : ({a, fun _ : ℕ => (1 : ℚ)} : Set (ℕ → ℚ)).Finite := by simp
    haveI : FiniteDimensional ℚ (Submodule.span ℚ {a, fun _ : ℕ => (1 : ℚ)}) :=
      FiniteDimensional.span_of_finite ℚ hpair
    haveI : FiniteDimensional ℚ W := inferInstance
    let g : ℕ → ℕ → ℚ := fun j i => f j (x i) - a i - b j
    have hmem (j : ℕ) : g j ∈ W := by
      have hfj : E (f j) ∈ W := Submodule.mem_sup_left
        (Submodule.mem_map.mpr ⟨f j, Submodule.subset_span (hf j), rfl⟩)
      have ha : a ∈ W := Submodule.mem_sup_right (Submodule.subset_span (by simp))
      have hb : (fun _ : ℕ => (1 : ℚ)) ∈ W :=
        Submodule.mem_sup_right (Submodule.subset_span (by simp))
      have hd := W.sub_mem (W.sub_mem hfj ha) (W.smul_mem (b j) hb)
      have heq : g j = E (f j) - a - b j • (fun _ : ℕ => (1 : ℚ)) := by
        funext i
        simp [g, E]
      rw [heq]
      exact hd
    have hzero (i j : ℕ) (hij : i < j) : g j i = 0 := by
      dsimp [g]
      rw [habove i j hij]
      ring
    have hone (i : ℕ) : g i i = 1 := by
      dsimp [g]
      rw [hdiag i]
      ring
    have hlin : LinearIndependent ℚ g := by
      apply linearIndependent_iff'.mpr
      intro t c hsum i hi
      induction i using Nat.strong_induction_on with
      | h i ih =>
        have he : (∑ j ∈ t, c j * g j i) = 0 := by
          have h := congrArg (fun v : ℕ → ℚ => v i) hsum
          simpa using h
        rw [Finset.sum_eq_single i] at he
        · simpa [hone] using he
        · intro j hj hji
          rcases lt_or_gt_of_ne hji with hjlt | hjgt
          · rw [ih j hjlt hj, zero_mul]
          · rw [hzero i j hjgt, mul_zero]
        · exact fun hni => (hni hi).elim
    let v : ℕ → W := fun j => ⟨g j, hmem j⟩
    have hv : LinearIndependent ℚ v := hlin.of_comp W.subtype
    have hc := hv.lt_aleph0_of_finiteDimensional
    simpa using hc
  refine triangular_evaluation_span_infinite (twoKernel P) f (fun i=>A (a i))
    (fun i=>(a i : ℚ)) (fun j=>(b j : ℚ)) ?_ ?_ ?_
  · intro j
    exact ⟨2*b j,r (b j),residue (b j),rfl⟩
  · intro i j hij
    dsimp [f]
    rw [address]
    have he:=offdiagonal_exact_family (a i) (b j) (by dsimp [a];omega)
      (by dsimp [a];omega) (by dsimp [b];omega) (by dsimp [a,b];omega)
    dsimp only at he
    change PL (List.ofFn (fun k : Fin (N (a i) (b j)) => u_pd k))=a i+b j at he
    dsimp only [P]
    rw [he]
    push_cast
    rfl
  · intro i
    dsimp [f]
    rw [address]
    have he:=diagonal_exact_family (a i) (by dsimp [a];omega) (by dsimp [a];omega)
    dsimp only at he
    have hb : b i=2*a i-1 := by dsimp [a,b];omega
    rw [hb]
    change PL (List.ofFn (fun k : Fin (N (a i) (2*a i-1)) => u_pd k))=3*a i at he
    dsimp only [P]
    rw [he]
    dsimp [a]
    have hsub : 2*(2*i+1)-1=4*i+1 := by omega
    rw [hsub]
    push_cast
    ring

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.stronger_PPL_kernel_span
