/- GID: D5/S1/Words/Palindromes/PeriodDoubling/PrefixInputShape
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/PrefixInputShape
   mirror-E: none(waiver:unbounded-marker-input-grammar)
   anchors: []
   utility: none
   digest: Completed marker paths read a positive spacing-three prefix above an arbitrary tail. -/

/-
proof_shape: content (prefix_path_input_shape)
escape_witness: Five-mode induction extracts the number and positions of the positive marked digits.
admission_basis: escape-witness
Direct frozen dependencies: none; PrefixPathRealization and BaseSignedStreams are delivered here.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.PrefixPathRealization
import D5.S1.Words.Palindromes.PeriodDoubling.BaseSignedStreams
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open MarkedPrefixCertificates

/-- Completed markers recognize an arbitrary tail followed by positive digits spaced by three. -/
theorem prefix_path_input_shape {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (p : prefixRawAutomaton.Path s t xs) (hs : s[1]?.getD 0 = 0)
    (ht : t[1]?.getD 0 = 4) :
    ∃ (lower : List ℤ) (m k : ℕ), 0 < m ∧
      pathOutputs (fun _ _ (q : List ℤ) =>
        (BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) p =
        lower ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0 := by
  have edge {s q : List ℤ} {a : ℤ × ℤ × ℤ × ℤ}
      (he : (q,a) ∈ successors s) (mode : Fin 5)
      (hm : s[1]?.getD 0 = (mode.val : ℤ)) :
      let d := (BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0
      if mode.val=0 then q[1]?.getD 0=0 ∨ (q[1]?.getD 0=1 ∧ d=1)
      else if mode.val=1 then q[1]?.getD 0=2 ∧ d=0
      else if mode.val=2 then q[1]?.getD 0=3 ∧ d=0
      else if mode.val=3 then (q[1]?.getD 0=1 ∧ d=1) ∨ (q[1]?.getD 0=4 ∧ d=0)
      else q[1]?.getD 0=4 ∧ d=0 := by
    obtain ⟨e,he,hmem⟩ := List.mem_flatMap.mp he
    unfold nextMarker at hmem
    dsimp only at hmem
    fin_cases mode <;> simp only [hm] at hmem <;> norm_num only at hmem ⊢
    all_goals simp only [ite_true,ite_false,false_or,true_or] at hmem ⊢
    · split at hmem
      · simp at hmem
      · split at hmem
        · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨rfl,by simpa using ‹_ ∧ _ ∧ _›.1⟩
        · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
          obtain ⟨rfl,ha⟩ := hmem
          exact Or.inl rfl
    · split at hmem
      · simp at hmem
      · split at hmem
        · simp at hmem
        · rename_i hd
          simp only [List.mem_singleton,Prod.mk.injEq] at hmem
          obtain ⟨rfl,ha⟩ := hmem
          simpa using (show (2:ℤ)=2 ∧ (BaseCertificates.baseTable e.1).1[10]?.getD 0=0 from ⟨rfl,by simpa using hd⟩)
    · split at hmem
      · simp at hmem
      · split at hmem
        · simp at hmem
        · rename_i hd
          simp only [List.mem_singleton,Prod.mk.injEq] at hmem
          obtain ⟨rfl,ha⟩ := hmem
          simpa using (show (3:ℤ)=3 ∧ (BaseCertificates.baseTable e.1).1[10]?.getD 0=0 from ⟨rfl,by simpa using hd⟩)
    · split at hmem
      · simp at hmem
      · split at hmem
        · simp at hmem
        · rename_i hd
          simp only [List.mem_singleton,Prod.mk.injEq] at hmem
          obtain ⟨rfl,ha⟩ := hmem
          by_cases h1 : (BaseCertificates.baseTable e.1).1[10]?.getD 0=1
          · left; simpa [h1]
          · right
            have h0 : (BaseCertificates.baseTable e.1).1[10]?.getD 0=0 := by simpa [h1] using hd
            simpa [h0]
    · split at hmem
      · simp at hmem
      · split at hmem
        · simp at hmem
        · rename_i hd
          simp only [List.mem_singleton,Prod.mk.injEq] at hmem
          obtain ⟨rfl,ha⟩ := hmem
          simpa using (show (4:ℤ)=4 ∧ (BaseCertificates.baseTable e.1).1[10]?.getD 0=0 from ⟨rfl,by simpa using hd⟩)
  let G : Fin 5 → List ℤ → Prop := fun mode ds =>
    if mode.val=0 then ∃ (lower : List ℤ) (m k : ℕ), 0<m ∧
      ds=lower ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else if mode.val=1 then ∃ m k : ℕ,
      ds=[0,0] ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else if mode.val=2 then ∃ m k : ℕ,
      ds=[0] ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else if mode.val=3 then ∃ m k : ℕ,
      ds=(List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else ∃ k : ℕ, ds=List.replicate k 0
  have go {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : prefixRawAutomaton.Path s t xs) :
      ∀ (mode : Fin 5), s[1]?.getD 0=(mode.val : ℤ) → t[1]?.getD 0=4 →
        G mode (pathOutputs (fun _ _ (q : List ℤ) =>
          (BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) p) := by
    induction p with
    | nil s =>
      intro mode hs ht
      have hv : mode.val=4 := by omega
      dsimp [G]
      simp only [hv,show (4:ℕ)≠0 by decide,show (4:ℕ)≠1 by decide,
        show (4:ℕ)≠2 by decide,show (4:ℕ)≠3 by decide,ite_false]
      exact ⟨0,rfl⟩
    | cons q s t a xs he p ih =>
      intro mode hs ht
      have hed := edge he mode hs
      fin_cases mode <;> dsimp only at hed <;> norm_num only at hed <;>
        simp only [ite_true,ite_false] at hed
      · rcases hed with hq | ⟨hq,hd⟩
        · obtain ⟨lower,m,k,hm,hr⟩ := ih 0 hq ht
          refine ⟨(BaseCertificates.baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0::lower,m,k,hm,?_⟩
          simp only [pathOutputs,List.cons_append,hr]
        · obtain ⟨m,k,hr⟩ := ih 1 hq ht
          refine ⟨[],m+1,k,by omega,?_⟩
          simp only [pathOutputs,hd,hr,List.replicate_succ,List.flatten_cons,
            List.nil_append,List.cons_append]
      · obtain ⟨m,k,hr⟩ := ih 2 hed.1 ht
        refine ⟨m,k,?_⟩
        simp only [pathOutputs,hed.2,hr,List.cons_append,List.nil_append]
      · obtain ⟨m,k,hr⟩ := ih 3 hed.1 ht
        refine ⟨m,k,?_⟩
        simp only [pathOutputs,hed.2,hr,List.cons_append,List.nil_append]
      · rcases hed with ⟨hq,hd⟩ | ⟨hq,hd⟩
        · obtain ⟨m,k,hr⟩ := ih 1 hq ht
          refine ⟨m+1,k,?_⟩
          simp only [pathOutputs,hd,hr,List.replicate_succ,List.flatten_cons,
            List.nil_append,List.cons_append]
        · obtain ⟨k,hr⟩ := ih 4 hq ht
          refine ⟨0,k,?_⟩
          simp only [pathOutputs,hd,hr,List.replicate_succ,List.replicate_zero,
            List.flatten_nil,List.nil_append]
      · obtain ⟨k,hr⟩ := ih 4 hed.1 ht
        refine ⟨k+1,?_⟩
        simp only [pathOutputs,hed.2,hr,List.replicate_succ]
  exact go p 0 hs ht

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.prefix_path_input_shape
