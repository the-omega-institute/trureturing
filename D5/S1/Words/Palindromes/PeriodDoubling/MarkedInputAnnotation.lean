/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedInputAnnotation
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedInputAnnotation
   mirror-E: none(waiver:complete-marked-input-annotation)
   anchors: []
   utility: none
   digest: Accepted base paths with a marked input pattern admit completed marker annotations. -/

/-
proof_shape: content (marked_input_path_annotation)
escape_witness: Persistent class checks and five-mode construction annotate every input position.
admission_basis: escape-witness
Direct frozen dependencies: none; PrefixPathRealization and BaseClassStreams are delivered here.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.PrefixPathRealization
import D5.S1.Words.Palindromes.PeriodDoubling.BaseClassStreams
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace D5.S1.Words.Palindromes.PeriodDoubling
open MarkedPrefixCertificates BaseCertificates

/-- A signed tail with two separating zeros and a positive prefix lifts to the marker relation. -/
theorem marked_input_path_annotation {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (p : (baseAutomaton true).Path s t xs) (full : List ℤ)
    (hf : full[0]?.getD 0=(s.val : ℤ)) (hm : full[1]?.getD 0=0)
    (ht : t ∈ (baseAutomaton true).accept) (lower : List ℤ)
    (m k : ℕ) (hpos : 0<m)
    (hgap : ([(baseTable s.val).1[11]?.getD 0,(baseTable s.val).1[10]?.getD 0] ++ lower).reverse[0]?.getD 0=0 ∧
      ([(baseTable s.val).1[11]?.getD 0,(baseTable s.val).1[10]?.getD 0] ++ lower).reverse[1]?.getD 0=0)
    (hshape : pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[10]?.getD 0) p =
      lower ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0) :
    ∃ u : List ℤ, u[0]?.getD 0=(t.val : ℤ) ∧ u[1]?.getD 0=4 ∧
      ∃ pp : prefixRawAutomaton.Path full u xs,
        (pathOutputs (fun _ _ (q : List ℤ) => q[1]?.getD 0) pp).take lower.length =
          List.replicate lower.length 0 ∧
        (pathOutputs (fun _ _ (q : List ℤ) => q[1]?.getD 0) pp)[lower.length]? = some 1 := by
  have checked (i : ℕ) (hi : i<1492) : classRowCheck i=true := by
    have blocks : ∀ b : Fin 24,
        ((List.range (min 64 (1492-64*b.val))).all (fun k => classRowCheck (64*b.val+k)))=true := by
      intro b;fin_cases b <;> decide
    have hb := blocks ⟨i/64,by omega⟩
    have hk : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range];omega
    simpa only [show 64*(i/64)+i%64=i by omega] using List.all_eq_true.mp hb (i%64) hk
  have row (s q : Fin 1492) (a : ℤ × ℤ × ℤ × ℤ)
      (he : q ∈ (baseAutomaton true).step s a) :
      (baseTable q.val).1[11]?.getD 0=(baseTable s.val).1[10]?.getD 0 ∧
      ((baseTable q.val).1[18]?.getD 0=0 → (baseTable s.val).1[18]?.getD 0=0) := by
    have hc:=List.all_eq_true.mp (checked s.val s.isLt) (q.val,a) he
    dsimp [classRowCheck] at hc
    have hp:=of_decide_eq_true hc
    exact ⟨hp.1,fun h => (hp.2.2.2 h).1⟩
  have good {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton true).Path s t xs) (hflag : (baseTable t.val).1[18]?.getD 0=0) :
      (baseTable s.val).1[18]?.getD 0=0 ∧
      ∀ z ∈ pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[18]?.getD 0) p,z=0 := by
    induction p with
    | nil s => exact ⟨hflag,by simp [pathOutputs]⟩
    | cons q s t a xs he p ih =>
      have ih := ih hflag
      refine ⟨(row s q a he).2 ih.1,?_⟩
      intro z hz
      simp only [pathOutputs,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ih.1
      · exact ih.2 z hz
  have hflag : (baseTable t.val).1[18]?.getD 0=0 := by
    simp only [baseAutomaton,Set.mem_ofPred_eq,Bool.and_eq_true] at ht
    simpa only [beq_iff_eq,ite_true] using ht.2
  have hgood:= (good p hflag).2
  have step (full : List ℤ) (s q : Fin 1492) (a : ℤ × ℤ × ℤ × ℤ)
      (he : q ∈ (baseAutomaton true).step s a)
      (hf : full[0]?.getD 0=(s.val : ℤ)) (mode : Fin 5)
      (hm : full[1]?.getD 0=(mode.val : ℤ))
      (hgood : (baseTable q.val).1[18]?.getD 0=0)
      (hprev : mode.val=0 → (baseTable s.val).1[10]?.getD 0=0 ∧ (baseTable s.val).1[11]?.getD 0=0)
      (hd : let d := (baseTable q.val).1[10]?.getD 0
        if mode.val=0 then d=1 else if mode.val=3 then d=0 ∨ d=1 else d=0) :
      ∃ u : List ℤ, (u,a) ∈ successors full ∧ u[0]?.getD 0=(q.val : ℤ) ∧
        u[1]?.getD 0=(if mode.val=0 then 1 else if mode.val=1 then 2 else
          if mode.val=2 then 3 else if mode.val=3 ∧ (baseTable q.val).1[10]?.getD 0=1 then 1 else 4) := by
    have he' : (q.val,a) ∈ (baseTable (full[0]?.getD 0).toNat).2.1 := by
      change (q.val,a) ∈ (baseTable s.val).2.1 at he
      simpa only [hf,Int.toNat_natCast] using he
    suffices h : ∃ u : List ℤ, (u,a) ∈ nextMarker full (q.val,a) ∧ u[0]?.getD 0=(q.val : ℤ) ∧
        u[1]?.getD 0=(if mode.val=0 then 1 else if mode.val=1 then 2 else
          if mode.val=2 then 3 else if mode.val=3 ∧ (baseTable q.val).1[10]?.getD 0=1 then 1 else 4) by
      obtain ⟨u,hu,h0,h1⟩ := h
      exact ⟨u,List.mem_flatMap.mpr ⟨(q.val,a),he',hu⟩,h0,h1⟩
    fin_cases mode <;> dsimp only at hm hd hprev ⊢ <;> norm_num only at hm hd hprev ⊢ <;>
      simp only [ite_true,ite_false,false_and,true_and] at hd ⊢
    · obtain ⟨h10,h11⟩ := hprev trivial
      simp only [nextMarker]
      simp only [hgood,hf,Int.toNat_natCast,hm,hd,h10,h11,bne_self_eq_false,
        Bool.false_eq_true,ite_false,ite_true,and_self]
      refine ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self),rfl,rfl⟩
    · simp only [nextMarker]
      simp only [hgood,hf,Int.toNat_natCast,hm,hd,bne_self_eq_false,
        Bool.false_eq_true,ite_false,ite_true]
      norm_num only
      simp only [ite_true,ite_false,true_or,false_or]
      exact ⟨_,List.mem_cons_self,rfl,rfl⟩
    · simp only [nextMarker]
      simp only [hgood,hf,Int.toNat_natCast,hm,hd,bne_self_eq_false,
        Bool.false_eq_true,ite_false,ite_true]
      norm_num only
      simp only [ite_true,ite_false,true_or,false_or]
      exact ⟨_,List.mem_cons_self,rfl,rfl⟩
    · rcases hd with hd | hd
      all_goals
        simp only [nextMarker]
        simp only [hgood,hf,Int.toNat_natCast,hm,hd,bne_self_eq_false,
          Bool.false_eq_true,ite_false,ite_true]
        norm_num only
        simp only [ite_true,ite_false,true_or,false_or,Bool.false_and,Bool.and_false]
        exact ⟨_,List.mem_cons_self,rfl,rfl⟩
    · simp only [nextMarker]
      simp only [hgood,hf,Int.toNat_natCast,hm,hd,bne_self_eq_false,
        Bool.false_eq_true,ite_false,ite_true]
      norm_num only
      simp only [ite_true,ite_false,true_or,false_or]
      exact ⟨_,List.mem_cons_self,rfl,rfl⟩
  let G : Fin 5 → List ℤ → Prop := fun mode ds =>
    if mode.val=0 then ∃ m k : ℕ, 0<m ∧
      ds=(List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else if mode.val=1 then ∃ m k : ℕ,
      ds=[0,0] ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else if mode.val=2 then ∃ m k : ℕ,
      ds=[0] ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else if mode.val=3 then ∃ m k : ℕ,
      ds=(List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0
    else ∃ k : ℕ, ds=List.replicate k 0
  let next : Fin 5 → ℤ → Fin 5 := fun mode d =>
    if mode.val=0 then 1 else if mode.val=1 then 2 else
      if mode.val=2 then 3 else if mode.val=3 ∧ d=1 then 1 else 4
  have grammar (mode : Fin 5) (d : ℤ) (ds : List ℤ) (hg : G mode (d::ds)) :
      (if mode.val=0 then d=1 else if mode.val=3 then d=0 ∨ d=1 else d=0) ∧
      G (next mode d) ds := by
    fin_cases mode <;> dsimp [G] at hg ⊢ <;> norm_num only at hg ⊢ <;>
      try simp only [ite_true,ite_false] at hg ⊢
    · obtain ⟨m,k,hm,hv⟩ := hg
      cases m with
      | zero => omega
      | succ m =>
        simp only [List.replicate_succ,List.flatten_cons,List.cons_append,List.nil_append] at hv
        obtain ⟨hd,hs⟩ := List.cons.inj hv
        refine ⟨hd,?_⟩
        simpa [next,G] using (show G 1 ds from ⟨m,k,hs⟩)
    · obtain ⟨m,k,hv⟩ := hg
      obtain ⟨hd,hs⟩ := List.cons.inj hv
      exact ⟨hd,by simpa [next,G] using (show G 2 ds from ⟨m,k,hs⟩)⟩
    · obtain ⟨m,k,hv⟩ := hg
      obtain ⟨hd,hs⟩ := List.cons.inj hv
      exact ⟨hd,by simpa [next,G] using (show G 3 ds from ⟨m,k,hs⟩)⟩
    · obtain ⟨m,k,hv⟩ := hg
      cases m with
      | zero =>
        simp only [List.replicate_zero,List.flatten_nil,List.nil_append,List.replicate_succ] at hv
        obtain ⟨hd,hs⟩ := List.cons.inj hv
        refine ⟨Or.inl hd,?_⟩
        simpa [next,G,hd] using (show G 4 ds from ⟨k,hs⟩)
      | succ m =>
        simp only [List.replicate_succ,List.flatten_cons,List.cons_append,List.nil_append] at hv
        obtain ⟨hd,hs⟩ := List.cons.inj hv
        refine ⟨Or.inr hd,?_⟩
        simpa [next,G,hd] using (show G 1 ds from ⟨m,k,hs⟩)
    · obtain ⟨k,hv⟩ := hg
      cases k with
      | zero => simp at hv
      | succ k =>
        simp only [List.replicate_succ] at hv
        obtain ⟨hd,hs⟩ := List.cons.inj hv
        exact ⟨hd,by simpa [next,G] using (show G 4 ds from ⟨k,hs⟩)⟩
  have go {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton true).Path s t xs) :
      ∀ (full : List ℤ) (mode : Fin 5), full[0]?.getD 0=(s.val : ℤ) →
        full[1]?.getD 0=(mode.val : ℤ) →
        (mode.val=0 → (baseTable s.val).1[10]?.getD 0=0 ∧ (baseTable s.val).1[11]?.getD 0=0) →
        (∀ z ∈ pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[18]?.getD 0) p,z=0) →
        G mode (pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[10]?.getD 0) p) →
        ∃ u : List ℤ, u[0]?.getD 0=(t.val : ℤ) ∧ u[1]?.getD 0=4 ∧
          ∃ pp : prefixRawAutomaton.Path full u xs,
            mode.val=0 → (pathOutputs (fun _ _ (q : List ℤ) => q[1]?.getD 0) pp).head?=some 1 := by
    intro full mode hf hm hp hgood hshape
    induction p generalizing full mode with
    | nil s =>
      have hmode : mode.val=4 := by
        fin_cases mode <;> dsimp [G,pathOutputs] at hshape
        · obtain ⟨m,k,_,hs⟩ := hshape
          have hl := congrArg List.length hs
          simp at hl
        · obtain ⟨m,k,hs⟩ := hshape
          have hl := congrArg List.length hs
          simp at hl
        · obtain ⟨m,k,hs⟩ := hshape
          have hl := congrArg List.length hs
          simp at hl
        · obtain ⟨m,k,hs⟩ := hshape
          have hl := congrArg List.length hs
          simp at hl
        · rfl
      exact ⟨full,hf,by simpa only [hmode,Nat.cast_ofNat] using hm,⟨.nil full,fun h => by omega⟩⟩
    | cons q s t a xs he p ih =>
      obtain ⟨hd,hg⟩ := grammar mode ((baseTable q.val).1[10]?.getD 0)
        (pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[10]?.getD 0) p) hshape
      have hq : (baseTable q.val).1[18]?.getD 0=0 := hgood _ (by simp [pathOutputs])
      have hgood' : ∀ z ∈ pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[18]?.getD 0) p,z=0 := by
        intro z hz
        exact hgood z (by simp [pathOutputs,hz])
      obtain ⟨v,hv,hv0,hv1⟩ := step full s q a he hf mode hm hq hp hd
      have hv1' : v[1]?.getD 0=((next mode ((baseTable q.val).1[10]?.getD 0)).val : ℤ) := by
        rw [hv1]
        dsimp only [next]
        split <;> try rfl
        split <;> try rfl
        split <;> try rfl
        split <;> rfl
      have hp' : (next mode ((baseTable q.val).1[10]?.getD 0)).val=0 →
          (baseTable q.val).1[10]?.getD 0=0 ∧ (baseTable q.val).1[11]?.getD 0=0 := by
        intro h
        dsimp [next] at h
        split at h <;> try omega
        split at h <;> try omega
        split at h <;> try omega
        split at h <;> omega
      obtain ⟨u,hu0,hu1,pu,_⟩ := ih v (next mode ((baseTable q.val).1[10]?.getD 0)) hv0 hv1' hp' hgood' hg
      refine ⟨u,hu0,hu1,.cons v full u a xs hv pu,?_⟩
      intro hmode
      simpa only [pathOutputs,List.head?_cons,hmode,ite_true,Nat.cast_one] using
        congrArg some hv1
  have unmarked {s q : Fin 1492} {a : ℤ × ℤ × ℤ × ℤ}
      (he : q ∈ (baseAutomaton true).step s a) (full : List ℤ)
      (hf : full[0]?.getD 0=(s.val : ℤ)) (hm : full[1]?.getD 0=0)
      (hgood : (baseTable q.val).1[18]?.getD 0=0) :
      ∃ v : List ℤ, (v,a) ∈ successors full ∧ v[0]?.getD 0=(q.val : ℤ) ∧ v[1]?.getD 0=0 := by
    have he' : (q.val,a) ∈ (baseTable (full[0]?.getD 0).toNat).2.1 := by
      change (q.val,a) ∈ (baseTable s.val).2.1 at he
      simpa only [hf,Int.toNat_natCast] using he
    let v : List ℤ := [q.val,0,
      (Bool.toNat ((full[2]?.getD 0 != 0) &&
        (baseTable q.val).1[10]?.getD 0+(baseTable q.val).1[12]?.getD 0 == 0) : ℤ),0,0,0,0,0]
    refine ⟨v,List.mem_flatMap.mpr ⟨(q.val,a),he',?_⟩,rfl,rfl⟩
    simp only [nextMarker,hm,hf,Int.toNat_natCast,hgood,bne_self_eq_false,
      Bool.false_eq_true,ite_true,ite_false]
    split <;> exact List.mem_cons_self
  have lowerGo (lower : List ℤ) {s : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton true).Path s t xs) (full : List ℤ)
      (hf : full[0]?.getD 0=(s.val : ℤ)) (hm : full[1]?.getD 0=0)
      (hgood : ∀ z ∈ pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[18]?.getD 0) p,z=0)
      (hgap : ([(baseTable s.val).1[11]?.getD 0,(baseTable s.val).1[10]?.getD 0] ++ lower).reverse[0]?.getD 0=0 ∧
        ([(baseTable s.val).1[11]?.getD 0,(baseTable s.val).1[10]?.getD 0] ++ lower).reverse[1]?.getD 0=0)
      (hshape : pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[10]?.getD 0) p =
        lower ++ (List.replicate m [1,0,0]).flatten ++ List.replicate (k+1) 0) :
      ∃ u : List ℤ, u[0]?.getD 0=(t.val : ℤ) ∧ u[1]?.getD 0=4 ∧
        ∃ pp : prefixRawAutomaton.Path full u xs,
          (pathOutputs (fun _ _ (q : List ℤ) => q[1]?.getD 0) pp).take lower.length =
            List.replicate lower.length 0 ∧
          (pathOutputs (fun _ _ (q : List ℤ) => q[1]?.getD 0) pp)[lower.length]? = some 1 := by
    induction lower generalizing s xs full with
    | nil =>
      have hp : (baseTable s.val).1[10]?.getD 0=0 ∧ (baseTable s.val).1[11]?.getD 0=0 := by
        simpa only [List.append_nil,List.reverse_cons,List.reverse_nil,List.nil_append,
          List.singleton_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] using hgap
      obtain ⟨u,hu0,hu1,pp,hfirst⟩ := go p full 0 hf hm (fun _ => hp) hgood
        ⟨m,k,hpos,by simpa only [List.nil_append] using hshape⟩
      refine ⟨u,hu0,hu1,pp,rfl,?_⟩
      simpa only [List.length_nil,← List.head?_eq_getElem?] using hfirst rfl
    | cons d lower ih =>
      cases p with
      | nil s => simp [pathOutputs] at hshape
      | cons q s t a xs he p =>
        have hq : (baseTable q.val).1[18]?.getD 0=0 := hgood _ (by simp [pathOutputs])
        obtain ⟨v,hv,hv0,hv1⟩ := unmarked he full hf hm hq
        have hg' : ∀ z ∈ pathOutputs (fun _ _ (q : Fin 1492) => (baseTable q.val).1[18]?.getD 0) p,z=0 := by
          intro z hz;exact hgood z (by simp [pathOutputs,hz])
        simp only [pathOutputs,List.cons_append] at hshape
        obtain ⟨hqd,hshape'⟩:=List.cons.inj hshape
        have hp' : ([(baseTable q.val).1[11]?.getD 0,(baseTable q.val).1[10]?.getD 0] ++ lower).reverse[0]?.getD 0=0 ∧
            ([(baseTable q.val).1[11]?.getD 0,(baseTable q.val).1[10]?.getD 0] ++ lower).reverse[1]?.getD 0=0 := by
          rw [(row s q a he).1,hqd]
          have truncate (l : List ℤ) (x y z : ℤ) (i : Fin 2) :
              (l++[x,y])[i.val]?.getD 0=(l++[x,y,z])[i.val]?.getD 0 := by
            cases l with
            | nil => fin_cases i <;> rfl
            | cons b bs =>
              fin_cases i
              · rfl
              · cases bs <;> rfl
          simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
            List.singleton_append,List.append_assoc] at hgap ⊢
          exact ⟨(truncate lower.reverse d ((baseTable s.val).1[10]?.getD 0)
            ((baseTable s.val).1[11]?.getD 0) 0).trans hgap.1,
            (truncate lower.reverse d ((baseTable s.val).1[10]?.getD 0)
            ((baseTable s.val).1[11]?.getD 0) 1).trans hgap.2⟩
        obtain ⟨u,hu0,hu1,pu,hbefore,hselected⟩ := ih p v hv0 hv1 hg' hp' hshape'
        refine ⟨u,hu0,hu1,.cons v full u a xs hv pu,?_,?_⟩
        · simpa only [pathOutputs,List.length_cons,List.take_succ_cons,List.replicate_succ,hv1]
            using congrArg (List.cons (0:ℤ)) hbefore
        · simpa only [pathOutputs,List.length_cons,List.getElem?_cons_succ] using hselected
  exact lowerGo lower p full hf hm hgood hgap hshape

end D5.S1.Words.Palindromes.PeriodDoubling
#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marked_input_path_annotation
