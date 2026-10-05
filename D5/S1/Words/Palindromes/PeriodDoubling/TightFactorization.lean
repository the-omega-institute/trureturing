/- GID: D5/S1/Words/Palindromes/PeriodDoubling/TightFactorization
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/TightFactorization
   mirror-E: none(waiver:tight-cut-path-characterization)
   anchors: []
   utility: none
   digest: Equality in the signed-weight bound is equivalent to a path of tight palindrome cuts. -/

/-
proof_shape: content (tight_factorization_iff)
escape_witness: Strong induction constructs and reconstructs a complete path of tight cuts.
admission_basis: escape-witness
Direct frozen dependencies: none; SignedCutLowerBound is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SignedCutLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- Equality with the signed-weight lower bound is equivalent to a path of tight cuts. -/
theorem tight_factorization_iff (n : ℕ) :
    PL (List.ofFn (fun i : Fin n => u_pd i)) = signedWeight (((n+1)/2 : ℕ) : ℤ) ↔
    ∃ cuts : List ℕ, (n :: cuts).getLast? = some 0 ∧
      (n :: cuts).IsChain (fun s t => t < s ∧
        List.Palindrome (List.ofFn (fun i : Fin (s-t) => u_pd (t+i))) ∧
        signedWeight (((s+1)/2 : ℕ) : ℤ) = signedWeight (((t+1)/2 : ℕ) : ℤ) + 1) := by
  let P : ℕ → ℕ := fun k => PL (List.ofFn (fun i : Fin k => u_pd i))
  let F : ℕ → ℕ := fun k => signedWeight (((k+1)/2 : ℕ) : ℤ)
  let Rel : ℕ → ℕ → Prop := fun s t => t < s ∧
    List.Palindrome (List.ofFn (fun i : Fin (s-t) => u_pd (t+i))) ∧ F s = F t+1
  change P n = F n ↔ ∃ cuts : List ℕ, (n::cuts).getLast? = some 0 ∧ (n::cuts).IsChain Rel
  have split (n j : ℕ) (hj : j ≤ n) :
      (List.ofFn (fun i : Fin n => u_pd i)).take j =
        List.ofFn (fun i : Fin j => u_pd i) ∧
      (List.ofFn (fun i : Fin n => u_pd i)).drop j =
        List.ofFn (fun i : Fin (n-j) => u_pd (j+i)) := by
    constructor
    · apply List.ext_getElem
      · simp only [List.length_take, List.length_ofFn]; omega
      · intro i hi hi'
        simp only [List.getElem_take, List.getElem_ofFn]
    · apply List.ext_getElem
      · simp only [List.length_drop, List.length_ofFn]
      · intro i hi hi'
        simp only [List.getElem_drop, List.getElem_ofFn]
  have minimum (w : List Bool) : PalFactors w (PL w) := by
    apply (Nat.sInf_mem (s := { k | PalFactors w k }))
    refine ⟨w.length, w.map (fun a => [a]), ?_, by simp, ?_⟩
    · induction w with
      | nil => rfl
      | cons a w ih => simpa using congrArg (List.cons a) ih
    · intro p hp
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨by simp, List.Palindrome.singleton a⟩
  have hzero : P 0 = F 0 := by
    have hP : P 0 = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.sInf_le
      exact ⟨[], rfl, rfl, by simp⟩
    have hF : F 0 = 0 := signed_weight_arithmetic.1
    exact hP.trans hF.symm
  have upper (n j : ℕ) (hj : j < n)
      (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
      P n ≤ P j+1 := by
    obtain ⟨ps,hflat,hlen,hps⟩ := minimum (List.ofFn (fun i : Fin j => u_pd i))
    let tail := List.ofFn (fun i : Fin (n-j) => u_pd (j+i))
    have hjoin : List.ofFn (fun i : Fin n => u_pd i) =
        List.ofFn (fun i : Fin j => u_pd i) ++ tail := by
      have he := List.take_append_drop j (List.ofFn (fun i : Fin n => u_pd i))
      rw [(split n j hj.le).1, (split n j hj.le).2] at he
      exact he.symm
    apply Nat.sInf_le
    refine ⟨ps ++ [tail], ?_, ?_, ?_⟩
    · simpa [List.flatten_append, hflat, tail] using hjoin.symm
    · simpa [P, hlen]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hps p hp
      · have he : p = tail := List.mem_singleton.mp hp
        subst p
        refine ⟨?_, hpal⟩
        intro he'
        have hl := congrArg List.length he'
        simp only [tail, List.length_ofFn, List.length_nil] at hl
        omega
  constructor
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      intro heq
      by_cases hn : n = 0
      · subst n
        exact ⟨[], by simp, List.IsChain.singleton 0⟩
      · let w := List.ofFn (fun i : Fin n => u_pd i)
        have hwlen : w.length = n := by simp [w]
        have hw : w ≠ [] := by
          intro he
          have hlen := congrArg List.length he
          rw [hwlen, List.length_nil] at hlen
          exact hn hlen
        obtain ⟨j,hj,hpal,hopt⟩ := optimal_suffix_cut w hw
        rw [hwlen] at hj
        have hp : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))) := by
          simpa [(split n j hj.le).2, w] using hpal
        have hcost : P n = P j+1 := by
          dsimp [P]
          rw [← (split n j hj.le).1]
          exact hopt
        have hcut : F n ≤ F j+1 := palindromic_suffix_signed_bound.1 n j hj hp
        have hlow : F j ≤ P j := palindromic_suffix_signed_bound.2 j
        have heqj : P j = F j := by omega
        have hdiff : F n = F j+1 := by omega
        obtain ⟨cuts,hlast,hchain⟩ := ih j hj heqj
        refine ⟨j::cuts, ?_, List.isChain_cons_cons.mpr ⟨⟨hj,hp,hdiff⟩,hchain⟩⟩
        simpa only [List.getLast?_cons_cons] using hlast
  · induction n using Nat.strong_induction_on with
    | h n ih =>
      rintro ⟨cuts,hlast,hchain⟩
      cases cuts with
      | nil =>
        have hn : n = 0 := by simpa using hlast
        subst n
        exact hzero
      | cons j cuts =>
        obtain ⟨⟨hj,hpal,hdiff⟩,hrest⟩ := List.isChain_cons_cons.mp hchain
        have heqj := ih j hj ⟨cuts, by simpa only [List.getLast?_cons_cons] using hlast, hrest⟩
        have hupper := upper n j hj hpal
        have hlow : F n ≤ P n := palindromic_suffix_signed_bound.2 n
        omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.tight_factorization_iff
