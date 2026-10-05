/- GID: D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/EndpointNecessity
   mirror-E: none(waiver:reflected-digit-language)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result; instance=D5/S1/Words/Palindromes/FridPrefix/LanguageData.certificate
   digest: Palindrome reflection excludes every mismatch and forces endpoint acceptance. -/

/-
proof_shape: content (palindrome_endpoint).
escape_witness: construction of reflected unequal-letter witnesses and all-word monitor induction.
admission_basis: escape-witness.
Direct frozen dependencies:
  D5/S0/Automata/BinaryZeckendorfLanguage.NoAdjacentOnes
    statement_id: sha256:87b15f790efca613794d25fe2bc822ee2420eb2ab847760e509a3059c25a8f17
  D5/S0/Conventions/WDigits.wdigits
    statement_id: sha256:aa2180b1084af7cbefca6a68881fef42788c73bdfa5199bf42d3e0334fe883d6
  D5/S0/Conventions/WDigits.wdigits_unique
    statement_id: sha256:aa2180b1084af7cbefca6a68881fef42788c73bdfa5199bf42d3e0334fe883d6
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair_append_digit
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates
    statement_id: sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
  D5/S1/Digit/ZeckendorfRawWindow.support
    statement_id: sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
  D5/S1/Words/GoldenFactorComplexity.goldenFactor
    statement_id: sha256:df6050c1b101dcd4fec43d349d0113d19f3b79299ce649379ef3d12887619f3e
  D5/S1/Words/GoldenWord.goldenWord
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/GoldenWord.goldenWord_eq_zeckendorf_criterion
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.MismatchWitness
import D5.S1.Words.Palindromes.FridPrefix.EndpointAutomaton
import D5.S1.Words.GoldenFactorComplexity

namespace D5.S1.Words.FridPrefix
open D5.S1.Words.FridPrefix.Language
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S0.Conventions

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem palindrome_endpoint (u v : List (Fin 2)) (hu : NoAdjacentOnes u)
    (hv : NoAdjacentOnes v) (hlen : u.length=v.length)
    (hij : (fibPair u).1 < (fibPair v).1)
    (hpal : List.Palindrome (goldenFactor ((fibPair v).1-(fibPair u).1) (fibPair u).1)) :
    u.zip v ∈ endpoint.accepts := by
  let paired (u v : List (Fin 2)) : List (Fin 4) :=
    (u.zip v).map (fun p => ⟨2*p.1.val+p.2.val,by omega⟩)
  have projections (u v : List (Fin 2)) (hl : u.length=v.length) :
      ((paired u v).map Fin.val).map (fun a => Fin.ofNat 2 (a/2))=u ∧
      ((paired u v).map Fin.val).map (fun a => Fin.ofNat 2 a)=v := by
    induction u generalizing v with
    | nil => have he : v=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
             subst v; exact ⟨rfl,rfl⟩
    | cons a u ih =>
      cases v with
      | nil => simp at hl
      | cons b v =>
        have hi := ih v (by simpa using hl)
        simp only [paired,List.zip_cons_cons,List.map_cons]
        have hx : Fin.ofNat 2 ((2*a.val+b.val)/2)=a := Fin.ext (by
          change ((2*a.val+b.val)/2)%2=a.val
          omega)
        have hy : Fin.ofNat 2 (2*a.val+b.val)=b := Fin.ext (by
          change (2*a.val+b.val)%2=b.val
          omega)
        simpa only [paired,hx,hy,List.cons.injEq,true_and] using hi
  have step_valid (s : Signature) (px py a b : Fin 2)
      (hs : s.valid=true) (hx : s.previousX=px.val) (hy : s.previousY=py.val)
      (hcx : px=0 ∨ a=0) (hcy : py=0 ∨ b=0)
      (ho : s.strict=true ∨ a≤b) :
      let t := Language.step s ⟨2*a.val+b.val,by omega⟩
      t.valid=true ∧ t.previousX=a.val ∧ t.previousY=b.val ∧
      t.strict=(s.strict || decide (a<b)) ∧
      t.bad=maskStep badRows s.bad (2*a.val+b.val) ∧
      t.endpoint=maskStep endpointMasks s.endpoint (2*a.val+b.val) := by
    fin_cases px <;> fin_cases py <;> fin_cases a <;> fin_cases b <;>
      cases hstrict : s.strict <;> simp_all [Language.step]
  have monitor (u v : List (Fin 2)) (hl : u.length=v.length) (s : Signature)
      (px py : Fin 2) (hx : s.previousX=px.val) (hy : s.previousY=py.val)
      (hcu : NoAdjacentOnes (px::u)) (hcv : NoAdjacentOnes (py::v))
      (hs : s.valid=true) (ho : s.strict=true ∨ List.Lex (· < ·) u v) :
      let t := (paired u v).foldl Language.step s
      t.valid=true ∧ t.strict=true ∧
      t.bad=((paired u v).map Fin.val).foldl (maskStep badRows) s.bad ∧
      t.endpoint=((paired u v).map Fin.val).foldl (maskStep endpointMasks) s.endpoint := by
    induction u generalizing v s px py with
    | nil =>
      have he : v=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
      subst v
      have hst : s.strict=true := by rcases ho with h | h; exact h; cases h
      exact ⟨hs,hst,rfl,rfl⟩
    | cons a u ih =>
      cases v with
      | nil => simp at hl
      | cons b v =>
        have hcx := (List.isChain_cons_cons.mp hcu).1
        have hcy := (List.isChain_cons_cons.mp hcv).1
        have hhead : s.strict=true ∨ a≤b := by
          rcases ho with h | h
          · exact Or.inl h
          · cases h with
            | rel h => exact Or.inr (le_of_lt h)
            | cons h => exact Or.inr (le_refl _)
        let t := Language.step s ⟨2*a.val+b.val,by omega⟩
        have hstep := step_valid s px py a b hs hx hy hcx hcy hhead
        have horder : t.strict=true ∨ List.Lex (· < ·) u v := by
          rw [hstep.2.2.2.1]
          rcases ho with h | h
          · left; simp [h]
          · cases h with
            | rel h => left; simp [h]
            | cons h => exact Or.inr h
        have hi := ih v (by simpa using hl) t a b hstep.2.1 hstep.2.2.1
          hcu.tail hcv.tail hstep.1 horder
        rw [hstep.2.2.2.2.1,hstep.2.2.2.2.2] at hi
        simpa only [paired,t,List.zip_cons_cons,List.map_cons,List.foldl_cons] using hi
  have hcanon_u : NoAdjacentOnes (0::u) := by
    exact List.isChain_cons.mpr ⟨by simp,hu⟩
  have hcanon_v : NoAdjacentOnes (0::v) := by
    exact List.isChain_cons.mpr ⟨by simp,hv⟩
  have hm := monitor u v hlen initial 0 0 rfl rfl hcanon_u hcanon_v rfl
    (Or.inr ((canonical_lex_value u v hu hv hlen).mp hij))
  have hbfalse : hasAccept (((paired u v).map Fin.val).foldl (maskStep badRows) badStart)
      badAccept = false := by
    by_contra hn
    have hbtrue : hasAccept (((paired u v).map Fin.val).foldl (maskStep badRows) badStart)
        badAccept = true := Bool.eq_true_of_not_eq_false hn
    obtain ⟨U,V,hUlen,hVlen,hU,hV,hX,hY,hXu,hUy,hXv,hVy,heq,hneq⟩ :=
      mismatch_witness ((paired u v).map Fin.val) (by
        intro a ha; obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha; exact c.isLt) hbtrue
    have hproj := projections u v hlen
    simp only [hproj.1,hproj.2] at hXu hUy hXv hVy heq
    have letter (w : List (Fin 2)) (hw : NoAdjacentOnes w) :
        goldenWord (fibPair w).1 = !decide (w.getLastD 0=1) := by
      have hc := source_word_coordinates w hw
      have hs : support w=wdigits (fibPair w).1 := wdigits_unique hc.1 hc.2.2.1
      have low : ∀ z : List (Fin 2), 2 ∈ support z ↔ z.getLastD 0=1 := by
        intro z
        induction z with
        | nil => simp [support]
        | cons a z ih =>
          cases z with
          | nil => fin_cases a <;> simp [support]
          | cons b z =>
            by_cases ha : a=0
            · simpa [support,ha] using ih
            · simp only [support,if_neg ha,List.mem_cons,List.length_cons,
                show (a::b::z).getLastD 0 = (b::z).getLastD 0 from rfl]
              have hn : 2 ≠ (b::z).length+2 := by simp
              simpa [support,ha] using ih
      simp only [goldenWord_eq_zeckendorf_criterion,← hs,low]
      by_cases h : w.getLastD 0=1 <;> simp [h]
    let i := (fibPair u).1
    let j := (fibPair v).1
    let a := (fibPair U).1
    let b := (fibPair V).1
    have hab : goldenWord a=goldenWord b := by
      have ha : a-i < (goldenFactor (j-i) i).length := by
        simp only [goldenFactor,List.length_ofFn]; dsimp [i,j,a]; omega
      have hb : b-i < (goldenFactor (j-i) i).length := by
        simp only [goldenFactor,List.length_ofFn]; dsimp [i,j,b]; omega
      have hr := List.getElem_reverse (l := goldenFactor (j-i) i) (i := a-i)
        (by simpa using ha)
      simp only [show (goldenFactor (j-i) i).reverse=goldenFactor (j-i) i from hpal.reverse_eq] at hr
      have hidx : (goldenFactor (j-i) i).length-1-(a-i)=b-i := by
        simp only [goldenFactor,List.length_ofFn]; dsimp [i,j,a,b]; omega
      simp only [hidx] at hr
      have hai : i ≤ a := hXu
      have hbi : i ≤ b := hXv
      simpa only [goldenFactor,List.getElem_ofFn,Nat.add_sub_of_le hai,
        Nat.add_sub_of_le hbi] using hr
    have hbits : decide (U.getLastD 0=1)=decide (V.getLastD 0=1) := by
      rw [letter U hU,letter V hV] at hab
      exact Bool.not_inj hab
    have he : U.getLastD 0=V.getLastD 0 := by
      generalize U.getLastD 0=x at hbits ⊢
      generalize V.getLastD 0=y at hbits ⊢
      fin_cases x <;> fin_cases y <;> simp_all
    exact hneq he
  have hend : hasAccept (((paired u v).map Fin.val).foldl (maskStep endpointMasks)
      endpointStart) endpointAccept = true := by
    have hc := every_word (paired u v) hm.1 hm.2.1
    rw [hm.2.2.1,hm.2.2.2] at hc
    change hasAccept (((paired u v).map Fin.val).foldl (maskStep badRows) badStart)
      badAccept = !hasAccept (((paired u v).map Fin.val).foldl (maskStep endpointMasks)
      endpointStart) endpointAccept at hc
    rw [hbfalse] at hc
    cases h : hasAccept (((paired u v).map Fin.val).foldl (maskStep endpointMasks)
        endpointStart) endpointAccept
    · rw [h] at hc
      exact False.elim (Bool.noConfusion hc)
    · rfl
  have hbounds : ∀ q : Fin 17, ∀ a : Fin 4,
      (endpointMasks[q.val]!).getD a.val 0 < 2^17 := by decide +kernel
  have hsteps : ∀ q : Fin 17, ∀ a : Fin 4, ∀ t : Fin 17,
      ((endpointMasks[q.val]!).getD a.val 0).testBit t.val = true →
      t ∈ endpoint.step q (Fin.ofNat 2 (a.val/2),Fin.ofNat 2 a.val) := by
    simp only [endpoint,Set.mem_ofPred_eq]
    decide +kernel
  have transfer {q t : ℕ} {w : List ℕ}
      (path : (maskNFA endpointMasks endpointStart).Path q t w)
      (hq : q<17) (hw : ∀ a ∈ w, a<4) :
      ∃ ht : t<17, Nonempty (endpoint.Path ⟨q,hq⟩ ⟨t,ht⟩
        (w.map (fun a => (Fin.ofNat 2 (a/2),Fin.ofNat 2 a)))) := by
    induction path with
    | nil q => exact ⟨hq,⟨NFA.Path.nil _⟩⟩
    | cons r q t a w hm path ih =>
      have ha : a<4 := hw a (by simp)
      have htrans : ((endpointMasks[q]!).getD a 0).testBit r=true := hm.2
      have hb := hbounds ⟨q,hq⟩ ⟨a,ha⟩
      have hr : r<17 := by
        by_contra hn
        have hpow : 2^17 ≤ 2^r := Nat.pow_le_pow_right (by decide) (by omega)
        have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hpow)
        rw [hf] at htrans; contradiction
      obtain ⟨ht,⟨pt⟩⟩ := ih hr (fun b hb => hw b (List.mem_cons_of_mem _ hb))
      exact ⟨ht,⟨NFA.Path.cons _ _ _ _ _ (hsteps ⟨q,hq⟩ ⟨a,ha⟩ ⟨r,hr⟩ htrans) pt⟩⟩
  have hn : (((paired u v).map Fin.val).foldl (maskStep endpointMasks) endpointStart &&&
      endpointAccept) ≠ 0 := by simpa only [hasAccept,bne_iff_ne] using hend
  obtain ⟨t,ht⟩ := Nat.exists_testBit_of_ne_zero hn
  rw [Nat.testBit_and,Bool.and_eq_true] at ht
  obtain ⟨s,hs,⟨path⟩⟩ := mask_path endpointMasks _ endpointStart t ht.1
  have hs0 : s=0 := by simpa only [endpointStart,Nat.testBit_one_eq_true_iff_self_eq_zero] using hs
  subst s
  obtain ⟨htb,⟨p⟩⟩ := transfer path (by decide) (by
    intro a ha; obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha; exact c.isLt)
  have final : ∀ t : Fin 17, endpointAccept.testBit t.val=true → t ∈ endpoint.accept := by
    simp only [endpoint,Set.mem_ofPred_eq]
    decide +kernel
  apply NFA.accepts_iff_exists_path.mpr
  refine ⟨0,rfl,⟨t,htb⟩,final ⟨t,htb⟩ ht.2,?_⟩
  have hpairs : (((paired u v).map Fin.val).map
      (fun a => (Fin.ofNat 2 (a/2),Fin.ofNat 2 a)))=u.zip v := by
    apply List.ext_getElem
    · simp [paired]
    · intro i hi hi'
      simp only [List.getElem_map]
      apply Prod.ext <;> apply Fin.ext <;> simp [paired] <;> omega
  rw [hpairs] at p
  exact ⟨p⟩

end D5.S1.Words.FridPrefix
