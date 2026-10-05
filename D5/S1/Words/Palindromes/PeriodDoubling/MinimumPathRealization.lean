/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MinimumPathRealization
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MinimumPathRealization
   mirror-E: none(waiver:complete-lowest-position-product-realization)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/MinimumPositionCertificate.minimumTable
   digest: Every base path lifts to the product with the literal lowest-position escape flag. -/

/-
proof_shape: content (minimum_path_realization)
escape_witness: Complete successor verification and unbounded product-path construction track each flag.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.MinimumPositionCertificate
import D5.S1.Words.Palindromes.PeriodDoubling.BaseSignedStreams
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates MinimumPositionCertificate

private def realizationRowCheck (i : ℕ) : Bool :=
  let row:=minimumTable i
  let actual:=row.2.2.1.map fun e => ((minimumTable e.1).1,(minimumTable e.1).2.1,e.2)
  decide (row.1 < 1492) && (successors i).all actual.contains &&
    row.2.2.1.all (fun e => decide (e.1 < 1710))
private def realizationBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => realizationRowCheck (start+k)
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem minimum_path_realization {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ (baseAutomaton true).start) (p : (baseAutomaton true).Path s t xs) :
    ∃ u v : Fin 1710, u ∈ minimumAutomaton.start ∧
      (minimumTable u.val).1=s.val ∧ (minimumTable v.val).1=t.val ∧
      Nonempty (minimumAutomaton.Path u v xs) ∧
      (minimumTable v.val).2.1 =
        (pathOutputs (fun s _ q =>
          (baseTable s.val).1[14]?.getD 0 == 0 &&
          (baseTable q.val).1[10]?.getD 0 == 0 &&
          (baseTable q.val).1[12]?.getD 0 != 0) p).any id := by
  have checked (i : ℕ) (hi : i < 1710) : realizationRowCheck i=true := by
    have blocks : ∀ b : Fin 27, realizationBlockCheck (64*b.val) (min 64 (1710-64*b.val))=true := by
      intro b
      fin_cases b <;> decide
    have hb:=blocks ⟨i/64,by omega⟩
    dsimp [realizationBlockCheck] at hb
    have hk : i%64 ∈ List.range (min 64 (1710-64*(i/64))) := by
      simp only [List.mem_range];omega
    simpa only [show 64*(i/64)+i%64=i by omega] using List.all_eq_true.mp hb (i%64) hk
  let event : Fin 1492 → Fin 1492 → Bool := fun s q =>
    (baseTable s.val).1[14]?.getD 0 == 0 && (baseTable q.val).1[10]?.getD 0 == 0 &&
    (baseTable q.val).1[12]?.getD 0 != 0
  have lift {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton true).Path s t xs) (u : Fin 1710) (hu : (minimumTable u.val).1=s.val) :
      ∃ v : Fin 1710, (minimumTable v.val).1=t.val ∧ Nonempty (minimumAutomaton.Path u v xs) ∧
        (minimumTable v.val).2.1 =
          ((minimumTable u.val).2.1 || (pathOutputs (fun s _ q => event s q) p).any id) := by
    induction p generalizing u with
    | nil s => exact ⟨u,hu,⟨.nil u⟩,by simp [pathOutputs]⟩
    | cons q s t a xs he p ih =>
      have hr:=checked u.val u.isLt
      simp only [realizationRowCheck,Bool.and_eq_true] at hr
      have htrans:=hr
      have hedge : (q.val,a) ∈ (baseTable (minimumTable u.val).1).2.1 := by
        rw [hu];exact he
      have hexpected : (q.val,(minimumTable u.val).2.1 || event s q,a) ∈ successors u.val := by
        apply List.mem_map.mpr
        refine ⟨(q.val,a),hedge,?_⟩
        simp only [hu,event]
      have hcontains:=List.all_eq_true.mp htrans.1.2 _ hexpected
      have hmem : (q.val,(minimumTable u.val).2.1 || event s q,a) ∈
          ((minimumTable u.val).2.2.1).map (fun e => ((minimumTable e.1).1,(minimumTable e.1).2.1,e.2)) := by
        simpa only [List.contains_eq_mem,decide_eq_true_eq] using hcontains
      obtain ⟨e,he',heq⟩:=List.mem_map.mp hmem
      have hlt : e.1 < 1710 := of_decide_eq_true (List.all_eq_true.mp htrans.2 e he')
      let v : Fin 1710:=⟨e.1,hlt⟩
      have hv : (minimumTable v.val).1=q.val := congrArg Prod.fst heq
      have hflag : (minimumTable v.val).2.1=((minimumTable u.val).2.1 || event s q) :=
        congrArg (fun z : ℕ × Bool × ℤ × ℤ × ℤ × ℤ => z.2.1) heq
      have hlabel : e.2=a := congrArg (fun z : ℕ × Bool × ℤ × ℤ × ℤ × ℤ => z.2.2) heq
      obtain ⟨w,hw,⟨pw⟩,hfw⟩:=ih v hv
      refine ⟨w,hw,⟨.cons v u w a xs ?_ pw⟩,?_⟩
      · change (e.1,a) ∈ (minimumTable u.val).2.2.1
        rw [← hlabel];exact he'
      · rw [hfw,hflag]
        simp only [pathOutputs,List.any_cons,Bool.or_assoc,id_eq]
  have hslt : s.val < 7 := by
    change ([0,1,2,3,4,5,6] : List ℕ).contains s.val=true at hs
    simp only [List.contains_eq_mem,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false] at hs
    omega
  let u : Fin 1710:=⟨s.val,by omega⟩
  have hsrc : (minimumTable u.val).1=s.val ∧ (minimumTable u.val).2.1=false := by
    have hsmall : ∀ k : Fin 7, (minimumTable k.val).1=k.val ∧ (minimumTable k.val).2.1=false := by
      intro k
      fin_cases k <;> decide
    exact hsmall ⟨s.val,hslt⟩
  obtain ⟨v,hv,hp,hf⟩:=lift p u hsrc.1
  refine ⟨u,v,hslt,hsrc.1,hv,hp,?_⟩
  simpa only [hsrc.2,Bool.false_or,event] using hf

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.minimum_path_realization
