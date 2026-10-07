/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathSelection
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedPathSelection
   mirror-E: none(waiver:exact-selected-marker-decomposition)
   anchors: []
   utility: none
   digest: Completed good paths split at the selected digit and retain its exact phase snapshots. -/

/-
proof_shape: content (marked_path_selection)
escape_witness: Path induction finds the unique transition from the unmarked tail to the marker.
admission_basis: escape-witness
Direct frozen dependencies: none; MarkedSuffixAgreement shares this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.MarkedSuffixAgreement
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open MarkedPrefixCertificates BaseCertificates

/-- A good completed marker selects one transition and preserves its saved phase data. -/
theorem marked_path_selection {s t : List ℤ} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (p : prefixRawAutomaton.Path s t xs) (hs : s[1]?.getD 0=0)
    (ht : t[1]?.getD 0=4) (hgood : t[7]?.getD 0=0) :
    ∃ (u v : List ℤ) (as bs : List (ℤ × ℤ × ℤ × ℤ)) (a : ℤ × ℤ × ℤ × ℤ)
      (before : prefixRawAutomaton.Path s u as) (after : prefixRawAutomaton.Path v t bs),
      xs=as++a::bs ∧ u[1]?.getD 0=0 ∧ v[1]?.getD 0=1 ∧
      (v,a) ∈ successors u ∧ v[7]?.getD 0=0 ∧
      pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) p =
        pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) before ++
          (baseTable (v[0]?.getD 0).toNat).1[10]?.getD 0 ::
          pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) after ∧
      pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0) p =
        pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0) before ++
          (baseTable (v[0]?.getD 0).toNat).1[12]?.getD 0 ::
          pathOutputs (fun _ _ (q : List ℤ) => (baseTable (q[0]?.getD 0).toNat).1[10]?.getD 0) after ∧
      pathOutputs (fun _ _ (q : List ℤ) => q[1]?.getD 0) p =
        List.replicate as.length 0 ++ 1 :: pathOutputs (fun _ _ (q : List ℤ) => q[1]?.getD 0) after ∧
      (∀ k : ℕ, 3≤k → k≤6 → t[k]?.getD 0=v[k]?.getD 0) ∧
      (baseTable (v[0]?.getD 0).toNat).1[10]?.getD 0=1 ∧
      (baseTable (u[0]?.getD 0).toNat).1[10]?.getD 0=0 ∧
      (baseTable (u[0]?.getD 0).toNat).1[11]?.getD 0=0 ∧
      (baseTable (u[0]?.getD 0).toNat).1[12]?.getD 0=0 ∧
      (baseTable (u[0]?.getD 0).toNat).1[13]?.getD 0=0 ∧
      v[3]?.getD 0=(baseTable (u[0]?.getD 0).toNat).1[1]?.getD 0 ∧
      v[4]?.getD 0=(Bool.toNat ((baseTable (v[0]?.getD 0).toNat).1[12]?.getD 0 == 1) : ℤ) ∧
      v[5]?.getD 0=(Bool.toNat (
        (baseTable (u[0]?.getD 0).toNat).1[16]?.getD 0 < 0 ||
        ((baseTable (u[0]?.getD 0).toNat).1[16]?.getD 0 == 0 &&
        (baseTable (u[0]?.getD 0).toNat).1[2]?.getD 0 == 1)) : ℤ) ∧
      v[6]?.getD 0=(Bool.toNat (
        (baseTable (u[0]?.getD 0).toNat).1[17]?.getD 0 < 0 ||
        ((baseTable (u[0]?.getD 0).toNat).1[17]?.getD 0 == 0 &&
        (baseTable (u[0]?.getD 0).toNat).1[3]?.getD 0 == 1)) : ℤ) ∧
      ((baseTable (v[0]?.getD 0).toNat).1[12]?.getD 0=1 ∨
        ((baseTable (v[0]?.getD 0).toNat).1[12]?.getD 0=0 ∧
          v[5]?.getD 0=1 ∧ v[6]?.getD 0=0 ∧ u[2]?.getD 0≠0)) := by
  have edge {s q : List ℤ} {a : ℤ × ℤ × ℤ × ℤ}
      (he : (q,a) ∈ successors s) (hm : s[1]?.getD 0=0) :
      q[1]?.getD 0=0 ∨ q[1]?.getD 0=1 := by
    obtain ⟨e,he,hmem⟩ := List.mem_flatMap.mp he
    simp only [nextMarker,hm,ite_true] at hmem
    split at hmem
    · simp at hmem
    · split at hmem
      · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
        obtain ⟨rfl,ha⟩ := hmem
        exact Or.inl rfl
  have selected {u v : List ℤ} {a : ℤ × ℤ × ℤ × ℤ}
      (he : (v,a) ∈ successors u) (hu : u[1]?.getD 0=0)
      (hv : v[1]?.getD 0=1) (hg : v[7]?.getD 0=0) :
      (baseTable (v[0]?.getD 0).toNat).1[10]?.getD 0=1 ∧
      (baseTable (u[0]?.getD 0).toNat).1[10]?.getD 0=0 ∧
      (baseTable (u[0]?.getD 0).toNat).1[11]?.getD 0=0 ∧
      (baseTable (u[0]?.getD 0).toNat).1[12]?.getD 0=0 ∧
      (baseTable (u[0]?.getD 0).toNat).1[13]?.getD 0=0 ∧
      v[3]?.getD 0=(baseTable (u[0]?.getD 0).toNat).1[1]?.getD 0 ∧
      v[4]?.getD 0=(Bool.toNat ((baseTable (v[0]?.getD 0).toNat).1[12]?.getD 0 == 1) : ℤ) ∧
      v[5]?.getD 0=(Bool.toNat (
        (baseTable (u[0]?.getD 0).toNat).1[16]?.getD 0 < 0 ||
        ((baseTable (u[0]?.getD 0).toNat).1[16]?.getD 0 == 0 &&
        (baseTable (u[0]?.getD 0).toNat).1[2]?.getD 0 == 1)) : ℤ) ∧
      v[6]?.getD 0=(Bool.toNat (
        (baseTable (u[0]?.getD 0).toNat).1[17]?.getD 0 < 0 ||
        ((baseTable (u[0]?.getD 0).toNat).1[17]?.getD 0 == 0 &&
        (baseTable (u[0]?.getD 0).toNat).1[3]?.getD 0 == 1)) : ℤ) ∧
      ((baseTable (v[0]?.getD 0).toNat).1[12]?.getD 0=1 ∨
        ((baseTable (v[0]?.getD 0).toNat).1[12]?.getD 0=0 ∧
          v[5]?.getD 0=1 ∧ v[6]?.getD 0=0 ∧ u[2]?.getD 0≠0)) := by
    obtain ⟨e,he,hmem⟩ := List.mem_flatMap.mp he
    simp only [nextMarker,hu,ite_true] at hmem
    split at hmem
    · simp at hmem
    · split at hmem
      · rename_i hsel
        simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl,ha⟩ | ⟨rfl,ha⟩
        · norm_num at hv
        · simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,
            Option.getD_some,Int.toNat_natCast] at hg ⊢
          have hbad := hg
          simp only [Int.natCast_eq_zero,Bool.toNat_eq_zero,Bool.or_eq_false_iff] at hbad
          rcases hsel with ⟨hd,hs10,hs11⟩
          refine ⟨hd,hs10,hs11,?_,?_,trivial,trivial,trivial,trivial,?_⟩
          · simpa using hbad.1.1.1
          · simpa using hbad.1.1.2
          · by_cases hj : (baseTable e.1).1[12]?.getD 0=1
            · exact Or.inl hj
            · right
              have hj0 : (baseTable e.1).1[12]?.getD 0=0 := by
                have hh:=hbad.1.2
                simp [hj] at hh
                exact hh
              have hb := hbad.2
              simp [hj] at hb
              refine ⟨hj0,?_,by simpa using hb.1.2,by simpa using hb.2⟩
              have hphase : (baseTable (u[0]?.getD 0).toNat).1[16]?.getD 0 < 0 ∨
                  ((baseTable (u[0]?.getD 0).toNat).1[16]?.getD 0=0 ∧
                    (baseTable (u[0]?.getD 0).toNat).1[2]?.getD 0=1) := by
                by_cases hn : (baseTable (u[0]?.getD 0).toNat).1[16]?.getD 0 < 0
                · exact Or.inl hn
                · exact Or.inr (hb.1.1 (by omega))
              simpa using hphase
      · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
        obtain ⟨rfl,ha⟩ := hmem
        norm_num at hv
  induction p with
  | nil s => omega
  | cons q s t a xs he p ih =>
    rcases edge he hs with hq | hq
    · obtain ⟨u,v,as,bs,b,before,after,hxs,hu,hv,hstep,hflag,hinput,houtput,hmodes,hdata,hselected⟩ := ih hq ht hgood
      refine ⟨u,v,a::as,bs,b,.cons q s u a as he before,after,?_,hu,hv,hstep,hflag,?_,?_,?_,hdata,hselected⟩
      · simp only [List.cons_append,hxs]
      · simp only [pathOutputs,List.cons_append,hinput]
      · simp only [pathOutputs,List.cons_append,houtput]
      · simp only [pathOutputs,List.length_cons,List.replicate_succ,List.cons_append,hq,hmodes]
    · obtain ⟨hflag,hsuffix,hdata⟩ := marked_suffix_agreement p (Or.inl hq) hgood
      refine ⟨s,q,[],xs,a,.nil s,p,rfl,hs,hq,he,hflag,rfl,?_,?_,hdata,selected he hs hq hflag⟩
      · simpa only [pathOutputs,List.nil_append] using congrArg
          (List.cons ((baseTable (q[0]?.getD 0).toNat).1[12]?.getD 0)) hsuffix.symm
      · simp only [pathOutputs,List.length_nil,List.replicate_zero,List.nil_append,hq]
end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marked_path_selection
