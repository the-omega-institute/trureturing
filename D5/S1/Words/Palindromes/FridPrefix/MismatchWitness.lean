/- GID: D5/S1/Words/Palindromes/FridPrefix/MismatchWitness
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/MismatchWitness
   mirror-E: none(waiver:reflected-letter-witness-construction)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity.palindrome_endpoint; instance=D5/S1/Words/Palindromes/FridPrefix/MismatchWitness.badCoordinates
   digest: Each accepted mismatch mask supplies canonical reflected unequal-letter numerals. -/

/-
proof_shape: content (mismatch_witness).
escape_witness: actual witness reconstruction with four comparisons and two joint carry registers.
admission_basis: escape-witness.
Direct frozen dependencies:
  D5/S0/Automata/BinaryZeckendorfLanguage.NoAdjacentOnes
    statement_id: sha256:87b15f790efca613794d25fe2bc822ee2420eb2ab847760e509a3059c25a8f17
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair_append_digit
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates
    statement_id: sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
  D5/S1/Digit/ZeckendorfRawWindow.support
    statement_id: sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.LanguageMonitor
import D5.S1.Words.Palindromes.FridPrefix.NumeralSemantics

namespace D5.S1.Words.FridPrefix.Language
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S0.Automata.BinaryZeckendorfLanguage

/-- Last four bits, strict comparison flags, and signed carry registers. -/
def badCoordinates : Array (ℕ × ℕ × ℤ × ℤ) := #[
  (0,0,0,0),
  (4,10,1,0),
  (5,6,0,0),
  (6,9,0,0),
  (7,5,-1,0),
  (15,0,0,0),
  (0,10,0,1),
  (1,14,-1,1),
  (2,11,-1,1),
  (3,15,-2,1),
  (11,10,-1,1),
  (0,6,0,0),
  (2,7,-1,0),
  (10,6,0,0),
  (0,9,0,0),
  (1,13,-1,0),
  (9,9,0,0),
  (0,5,0,-1),
  (8,5,1,-1),
  (3,15,-1,1),
  (0,14,1,0),
  (2,15,0,0),
  (6,15,1,0),
  (10,14,1,0),
  (0,11,1,0),
  (1,15,0,0),
  (5,15,1,0),
  (9,11,1,0),
  (0,15,1,-1),
  (4,15,2,-1),
  (8,15,2,-1),
  (12,15,3,-1),
  (0,10,1,0),
  (4,14,1,0),
  (6,15,0,0),
  (7,7,-1,0),
  (14,14,1,0),
  (15,6,0,0),
  (0,7,0,-1),
  (4,15,1,-1),
  (8,7,1,-1),
  (12,15,2,-1),
  (13,7,1,-1),
  (4,11,1,0),
  (5,15,0,0),
  (7,13,-1,0),
  (13,11,1,0),
  (15,9,0,0),
  (0,13,0,-1),
  (8,13,1,-1),
  (14,13,1,-1),
  (12,15,1,-1),
  (0,5,-1,0),
  (4,15,0,0),
  (5,7,-1,0),
  (6,13,-1,0),
  (0,15,1,0),
  (0,14,0,1),
  (2,15,-1,1),
  (7,15,-1,1),
  (11,14,-1,1),
  (0,15,0,0),
  (1,15,-1,0),
  (4,15,1,0),
  (8,15,1,0),
  (9,15,0,0),
  (13,15,1,0),
  (0,15,0,1),
  (1,15,-1,1),
  (0,11,0,1),
  (11,11,-1,1),
  (2,15,-1,0),
  (10,15,0,0),
  (14,15,1,0),
  (0,15,-1,0),
  (5,15,-1,0),
  (6,15,-1,0),
  (8,15,0,0),
  (9,15,-1,0),
  (10,15,-1,0),
  (12,15,1,0),
  (13,15,0,0),
  (14,15,0,0),
  (15,15,-1,0),
  (0,15,-1,1),
  (1,15,-2,1),
  (2,15,-2,1),
  (3,15,-3,1),
  (8,15,0,1),
  (9,15,-1,1),
  (10,15,-1,1),
  (11,15,-2,1),
  (4,15,0,1),
  (5,15,-1,1),
  (6,15,-1,1),
  (7,15,-2,1),
  (1,15,-2,2),
  (2,15,-2,2),
  (3,15,-3,2),
  (0,7,-1,0),
  (0,13,-1,0),
  (11,15,-1,0),
  (11,15,-1,1),
  (9,15,1,0),
  (7,15,-1,0),
  (15,15,0,0),
  (0,15,0,-1),
  (8,15,1,-1),
  (14,15,1,-1),
  (10,15,1,0),
  (13,15,1,-1),
  (3,15,-1,0),
  (7,15,0,0),
  (11,15,0,0),
  (15,15,1,0),
  (2,15,0,-1),
  (6,15,1,-1),
  (10,15,1,-1),
  (14,15,2,-1),
  (1,15,0,-1),
  (5,15,1,-1),
  (9,15,1,-1),
  (13,15,2,-1),
  (4,15,2,-2),
  (8,15,2,-2),
  (12,15,3,-2),
  (2,15,1,0),
  (1,15,1,0),
  (0,15,2,-1),
  (4,15,3,-1),
  (8,15,3,-1),
  (8,15,-1,0),
  (4,15,-1,0),
  (0,15,-2,1),
  (1,15,-3,1),
  (2,15,-3,1),
  (15,15,-1,1),
  (15,15,1,-1)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 100000 in
theorem mismatch_witness (symbols : List ℕ)
    (hsymbols : ∀ a ∈ symbols, a < 4)
    (ha : hasAccept (symbols.foldl (maskStep badRows) badStart) badAccept = true) :
    ∃ U V : List (Fin 2),
      U.length = symbols.length ∧ V.length = symbols.length ∧
      NoAdjacentOnes U ∧ NoAdjacentOnes V ∧
      let X := symbols.map (fun a => Fin.ofNat 2 (a/2))
      let Y := symbols.map (fun a => Fin.ofNat 2 a)
      NoAdjacentOnes X ∧ NoAdjacentOnes Y ∧
      (fibPair X).1 ≤ (fibPair U).1 ∧ (fibPair U).1 < (fibPair Y).1 ∧
      (fibPair X).1 ≤ (fibPair V).1 ∧ (fibPair V).1 < (fibPair Y).1 ∧
      (fibPair X).1+(fibPair Y).1=(fibPair U).1+(fibPair V).1+1 ∧
      U.getLastD 0 ≠ V.getLastD 0 := by
  let coord (q : ℕ) := badCoordinates[q]!
  let prev (q r : ℕ) := (coord q).1.testBit r
  let flag (q r : ℕ) := (coord q).2.1.testBit r
  let ca (q : ℕ) := (coord q).2.2.1
  let cb (q : ℕ) := (coord q).2.2.2
  let compare (q t r l h : ℕ) : Prop :=
    (flag q r = false → l ≤ h) ∧ flag t r = (flag q r || decide (l < h))
  have finite_steps : ∀ q : Fin 138, ∀ a : Fin 4, ∀ t : Fin 138,
      ((badRows[q.val]!).getD a.val 0).testBit t.val = true →
      ∃ u v : Fin 2,
        prev t 3 = decide (a.val/2=1) ∧ prev t 2 = decide (a.val%2=1) ∧
        prev t 1 = decide (u.val=1) ∧ prev t 0 = decide (v.val=1) ∧
        (prev q 3 = true → a.val/2=0) ∧ (prev q 2 = true → a.val%2=0) ∧
        (prev q 1 = true → u.val=0) ∧ (prev q 0 = true → v.val=0) ∧
        compare q t 0 (a.val/2) u.val ∧ compare q t 1 u.val (a.val%2) ∧
        compare q t 2 (a.val/2) v.val ∧ compare q t 3 v.val (a.val%2) ∧
        ca t = cb q+((a.val/2 : ℕ) : ℤ)+((a.val%2 : ℕ) : ℤ)-u.val-v.val ∧
        cb t = ca q+cb q := by
    unfold compare
    decide +kernel
  have finite_bounds : ∀ q : Fin 138, ∀ a : Fin 4,
      (badRows[q.val]!).getD a.val 0 < 2^138 := by decide +kernel
  have finite_terminal : ∀ t : Fin 138, badAccept.testBit t.val = true →
      flag t 1 = true ∧ flag t 3 = true ∧ ca t+2*cb t=1 ∧ prev t 1 ≠ prev t 0 := by
    decide +kernel
  have nonzero : (symbols.foldl (maskStep badRows) badStart &&& badAccept) ≠ 0 := by
    simpa only [hasAccept,bne_iff_ne] using ha
  obtain ⟨t, ht⟩ := Nat.exists_testBit_of_ne_zero nonzero
  rw [Nat.testBit_and, Bool.and_eq_true] at ht
  obtain ⟨s,hs,⟨path⟩⟩ := mask_path badRows symbols badStart t ht.1
  have hs0 : s=0 := by simpa only [badStart,Nat.testBit_one_eq_true_iff_self_eq_zero] using hs
  subst s
  let X (w : List ℕ) := w.map (fun a => Fin.ofNat 2 (a/2))
  let Y (w : List ℕ) := w.map (fun a => Fin.ofNat 2 a)
  let ord (b : Bool) (u v : List (Fin 2)) : Prop := if b then List.Lex (· < ·) u v else u=v
  let invariant (q : ℕ) (w : List ℕ) (U V : List (Fin 2)) : Prop :=
    q < 138 ∧ U.length=w.length ∧ V.length=w.length ∧
    NoAdjacentOnes (X w) ∧ NoAdjacentOnes (Y w) ∧ NoAdjacentOnes U ∧ NoAdjacentOnes V ∧
    decide ((X w).getLastD 0=1)=prev q 3 ∧ decide ((Y w).getLastD 0=1)=prev q 2 ∧
    decide (U.getLastD 0=1)=prev q 1 ∧ decide (V.getLastD 0=1)=prev q 0 ∧
    ord (flag q 0) (X w) U ∧ ord (flag q 1) U (Y w) ∧
    ord (flag q 2) (X w) V ∧ ord (flag q 3) V (Y w) ∧
    ((fibPair (X w)).1 : ℤ)+(fibPair (Y w)).1-(fibPair U).1-(fibPair V).1=ca q+2*cb q ∧
    ((fibPair (X w)).2 : ℤ)+(fibPair (Y w)).2-(fibPair U).2-(fibPair V).2=2*ca q+3*cb q
  have lex_extend (u v : List (Fin 2)) (a b : Fin 2) (hl : u.length=v.length)
      (h : List.Lex (· < ·) u v) : List.Lex (· < ·) (u++[a]) (v++[b]) := by
    induction h with
    | nil => simp at hl
    | rel h => exact List.Lex.rel h
    | cons h ih => exact List.Lex.cons (ih (by simpa using hl))
  have ord_extend (u v : List (Fin 2)) (a b : Fin 2) (old new : Bool)
      (hl : u.length=v.length) (h : ord old u v)
      (hc : (old=false → a≤b) ∧ new=(old || decide (a<b))) :
      ord new (u++[a]) (v++[b]) := by
    cases old
    · simp only [ord,Bool.false_eq_true,↓reduceIte] at h
      subst v
      have hab := hc.1 rfl
      rw [hc.2]
      by_cases he : a=b
      · subst b; simp [ord]
      · have hlt : a<b := lt_of_le_of_ne hab he
        simp only [decide_eq_true hlt,Bool.false_or,ord,↓reduceIte]
        exact List.Lex.append_left _ (List.Lex.rel hlt) u
    · simp only [ord,↓reduceIte] at h
      rw [hc.2]
      simp only [Bool.true_or,ord,↓reduceIte]
      exact lex_extend u v a b hl h
  have canonical_extend (u : List (Fin 2)) (a : Fin 2) (p : Bool)
      (hu : NoAdjacentOnes u) (hp : decide (u.getLastD 0=1)=p)
      (h : p=true → a=0) : NoAdjacentOnes (u++[a]) := by
    rw [NoAdjacentOnes,List.isChain_append]
    refine ⟨hu,by simp,?_⟩
    intro b hb c hc
    have hc' : c=a := by simpa using hc.symm
    subst c
    by_cases hb0 : b=0
    · exact Or.inl hb0
    · have hb1 : b=1 := by fin_cases b <;> simp_all
      have hg : u.getLastD 0=1 := by
        have hopt : u.getLast? = some b := Option.mem_def.mp hb
        rw [List.getLastD_eq_getLast?,hopt]
        exact hb1
      have hp1 : p=true := by rw [← hp]; exact decide_eq_true hg
      exact Or.inr (h hp1)
  have path_invariant {q t : ℕ} {rest : List ℕ}
      (path : (maskNFA badRows badStart).Path q t rest)
      (hrest : ∀ a ∈ rest, a<4) (before : List ℕ) (U V : List (Fin 2))
      (hi : invariant q before U V) : ∃ U' V', invariant t (before++rest) U' V' := by
    induction path generalizing before U V with
    | nil q => exact ⟨U,V,by simpa using hi⟩
    | cons r q t a rest hm path ih =>
      obtain ⟨hq,hUl,hVl,hX,hY,hU,hV,hpx,hpy,hpu,hpv,hxu,huy,hxv,hvy,hval,hshift⟩ := hi
      have ha : a<4 := hrest a (by simp)
      have htrans : ((badRows[q]!).getD a 0).testBit r=true := hm.2
      have hmBound := finite_bounds ⟨q,hq⟩ ⟨a,ha⟩
      have hr : r<138 := by
        by_contra hn
        have hr' : 138≤r := by omega
        have hp : 2^138 ≤ 2^r := Nat.pow_le_pow_right (by decide) hr'
        have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hmBound hp)
        rw [hf] at htrans
        contradiction
      obtain ⟨u,v,hx,hy,hu,hv,hcx,hcy,hcu,hcv,cu,uy,cv,vy,hca,hcb⟩ :=
        finite_steps ⟨q,hq⟩ ⟨a,ha⟩ ⟨r,hr⟩ htrans
      let x : Fin 2 := Fin.ofNat 2 (a/2)
      let y : Fin 2 := Fin.ofNat 2 a
      have hxval : x.val=a/2 := by dsimp [x]; omega
      have hyval : y.val=a%2 := rfl
      have step_inv : invariant r (before++[a]) (U++[u]) (V++[v]) := by
        simp only [invariant,X,Y,List.map_append,List.map_singleton,List.length_append,
          List.length_singleton,List.getLastD_concat]
        -- The concrete update preserves four canonical words, four comparisons and both carries.
        refine ⟨hr,by omega,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · exact canonical_extend _ x _ hX hpx (fun h => Fin.ext (by simpa [hxval] using hcx h))
        · exact canonical_extend _ y _ hY hpy (fun h => Fin.ext (by simpa [hyval] using hcy h))
        · exact canonical_extend _ u _ hU hpu (fun h => Fin.ext (hcu h))
        · exact canonical_extend _ v _ hV hpv (fun h => Fin.ext (hcv h))
        · change decide (x=1)=prev r 3
          simpa only [Fin.ext_iff,Fin.val_one,hxval] using hx.symm
        · change decide (y=1)=prev r 2
          simpa only [Fin.ext_iff,Fin.val_one,hyval] using hy.symm
        · simpa only [Fin.ext_iff,Fin.val_one] using hu.symm
        · simpa only [Fin.ext_iff,Fin.val_one] using hv.symm
        · exact ord_extend _ _ x u _ _ (by simp [X,hUl]) hxu (by simpa only [compare,Fin.le_iff_val_le_val,Fin.lt_def,hxval] using cu)
        · exact ord_extend _ _ u y _ _ (by simp [Y,hUl]) huy (by simpa only [compare,Fin.le_iff_val_le_val,Fin.lt_def,hyval] using uy)
        · exact ord_extend _ _ x v _ _ (by simp [X,hVl]) hxv (by simpa only [compare,Fin.le_iff_val_le_val,Fin.lt_def,hxval] using cv)
        · exact ord_extend _ _ v y _ _ (by simp [Y,hVl]) hvy (by simpa only [compare,Fin.le_iff_val_le_val,Fin.lt_def,hyval] using vy)
        · rw [fibPair_append_digit,fibPair_append_digit,fibPair_append_digit,fibPair_append_digit]
          simp only [Prod.fst,Nat.cast_add] at *
          dsimp only [X,Y] at hval hshift
          have hxcast : ((Fin.ofNat 2 (a/2)).val : ℤ)=((a/2 : ℕ) : ℤ) := congrArg Nat.cast hxval
          have hycast : ((Fin.ofNat 2 a).val : ℤ)=((a%2 : ℕ) : ℤ) := congrArg Nat.cast hyval
          omega
        · rw [fibPair_append_digit,fibPair_append_digit,fibPair_append_digit,fibPair_append_digit]
          simp only [Prod.snd,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at *
          dsimp only [X,Y] at hval hshift
          have hxcast : ((Fin.ofNat 2 (a/2)).val : ℤ)=((a/2 : ℕ) : ℤ) := congrArg Nat.cast hxval
          have hycast : ((Fin.ofNat 2 a).val : ℤ)=((a%2 : ℕ) : ℤ) := congrArg Nat.cast hyval
          omega
      have hi' := ih (fun b hb => hrest b (List.mem_cons_of_mem _ hb))
        (before++[a]) (U++[u]) (V++[v]) step_inv
      simpa [List.append_assoc] using hi'
  have hi0 : invariant 0 [] [] [] := by
    simp [invariant,ord,X,Y,NoAdjacentOnes,prev,flag,coord,ca,cb,badCoordinates,fibPair]
  obtain ⟨U,V,hfin⟩ := path_invariant path hsymbols [] [] [] hi0
  simp only [List.nil_append] at hfin
  obtain ⟨htb,hUl,hVl,hX,hY,hU,hV,hpx,hpy,hpu,hpv,hxu,huy,hxv,hvy,hval,hshift⟩ := hfin
  obtain ⟨f1,f3,hend,hdiff⟩ := finite_terminal ⟨t,htb⟩ ht.2
  refine ⟨U,V,hUl,hVl,hU,hV,hX,hY,?_,?_,?_,?_,?_,?_⟩
  · cases h : flag t 0
    · have he : X symbols=U := by simpa [ord,h] using hxu
      change (fibPair (X symbols)).1 ≤ (fibPair U).1
      rw [he]
    · exact le_of_lt ((canonical_lex_value _ _ hX hU (by simp [X,hUl])).mpr (by simpa [ord,h] using hxu))
  · exact (canonical_lex_value _ _ hU hY (by simp [Y,hUl])).mpr (by simpa [ord,f1] using huy)
  · cases h : flag t 2
    · have he : X symbols=V := by simpa [ord,h] using hxv
      change (fibPair (X symbols)).1 ≤ (fibPair V).1
      rw [he]
    · exact le_of_lt ((canonical_lex_value _ _ hX hV (by simp [X,hVl])).mpr (by simpa [ord,h] using hxv))
  · exact (canonical_lex_value _ _ hV hY (by simp [Y,hVl])).mpr (by simpa [ord,f3] using hvy)
  · change (fibPair (X symbols)).1+(fibPair (Y symbols)).1 =
      (fibPair U).1+(fibPair V).1+1
    have hend' : ca t+2*cb t=1 := hend
    have hz : ((fibPair (X symbols)).1 : ℤ)+(fibPair (Y symbols)).1 =
        (fibPair U).1+(fibPair V).1+1 := by omega
    exact_mod_cast hz
  · intro he
    rw [← hpu,← hpv,he] at hdiff
    contradiction

end D5.S1.Words.FridPrefix.Language
