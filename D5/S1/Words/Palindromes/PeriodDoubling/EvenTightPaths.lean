/- GID: D5/S1/Words/Palindromes/PeriodDoubling/EvenTightPaths
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/EvenTightPaths
   mirror-E: none(waiver:only-odd-cuts-at-even-tight-endpoints)
   anchors: []
   utility: none
   digest: A tight path from an even class-S endpoint of even weight to zero uses only odd cuts. -/

/-
proof_shape: content (even_tight_path_has_only_odd_cuts)
escape_witness: Path induction balances length, weight and parity against the one-even-cut bound.
admission_basis: escape-witness
Direct frozen dependencies: none; TightPathEvenCuts is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.TightPathEvenCuts
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

theorem even_tight_path_has_only_odd_cuts (n : ℕ) (cuts : List ℕ)
    (hS : classS n) (hn : n%2=0)
    (hF : signedWeight (((n+1)/2 : ℕ) : ℤ)%2=0)
    (hlast : (n::cuts).getLast?=some 0)
    (hchain : (n::cuts).IsChain (fun s t => t < s ∧
      List.Palindrome (List.ofFn (fun i : Fin (s-t) => u_pd (t+i))) ∧
      signedWeight (((s+1)/2 : ℕ) : ℤ)=signedWeight (((t+1)/2 : ℕ) : ℤ)+1)) :
    (n::cuts).IsChain (fun s t => s%2 ≠ t%2) := by
  let F : ℕ → ℕ := fun n => signedWeight (((n+1)/2 : ℕ) : ℤ)
  let Rel : ℕ → ℕ → Prop := fun s t => t < s ∧
    List.Palindrome (List.ofFn (fun i : Fin (s-t) => u_pd (t+i))) ∧ F s=F t+1
  have balance (n : ℕ) (cuts : List ℕ) (hlast : (n::cuts).getLast?=some 0)
      (hc : (n::cuts).IsChain Rel) : F n=cuts.length ∧
      (n+(((n::cuts).zip cuts).filter (fun e => e.1%2 == e.2%2)).length)%2=cuts.length%2 := by
    induction cuts generalizing n with
    | nil =>
      have hn : n=0 := by simpa using hlast
      subst n
      exact ⟨signed_weight_arithmetic.1,by simp⟩
    | cons j cuts ih =>
      obtain ⟨⟨_,_,hstep⟩,hrest⟩:=List.isChain_cons_cons.mp hc
      have hjlast : (j::cuts).getLast?=some 0 := by simpa only [List.getLast?_cons_cons] using hlast
      obtain ⟨hcost,hpar⟩:=ih j hjlast hrest
      refine ⟨by simp only [List.length_cons];omega,?_⟩
      by_cases he : n%2=j%2
      · simp only [List.zip_cons_cons,List.filter_cons,beq_iff_eq]
        rw [if_pos he,List.length_cons]
        simp only [List.length_cons]
        omega
      · simp only [List.zip_cons_cons,List.filter_cons,beq_iff_eq]
        rw [if_neg he]
        simp only [List.length_cons]
        omega
  obtain ⟨hc,hp⟩:=balance n cuts hlast hchain
  change signedWeight (((n+1)/2 : ℕ) : ℤ)=cuts.length at hc
  have hb:=tight_path_at_most_one_even_cut n cuts hS hchain
  have he0 : (((n::cuts).zip cuts).filter (fun e => e.1%2 == e.2%2)).length=0 := by
    omega
  have allodd (n : ℕ) (cuts : List ℕ)
      (hz : (((n::cuts).zip cuts).filter (fun e => e.1%2 == e.2%2)).length=0) :
      (n::cuts).IsChain (fun s t => s%2 ≠ t%2) := by
    induction cuts generalizing n with
    | nil => exact List.IsChain.singleton _
    | cons j cuts ih =>
      have he : n%2 ≠ j%2 := by
        intro hh
        simp only [List.zip_cons_cons,List.filter_cons,beq_iff_eq] at hz
        rw [if_pos hh,List.length_cons] at hz
        omega
      have htail : (((j::cuts).zip cuts).filter (fun e => e.1%2 == e.2%2)).length=0 := by
        simpa [he] using hz
      exact List.isChain_cons_cons.mpr ⟨he,ih j htail⟩
  exact allodd n cuts he0

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.even_tight_path_has_only_odd_cuts
