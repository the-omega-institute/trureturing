/- GID: D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength
   mirror-E: none(waiver:frid-prefix-settlement)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result; instance=D5/S1/Words/Palindromes/FridPrefix/RankA.rankA
   digest: Every Frid prefix has minimum nonempty palindromic factorisation length exactly 2k+1. -/

/-
proof_shape: content (result).
escape_witness: all-word reflected-mismatch exclusion, product-potential inequalities and the rank cycle.
admission_basis: escape-witness (#13044; Proved).
Direct frozen dependencies:
  D5/S0/Automata/BinaryZeckendorfLanguage.NoAdjacentOnes
    statement_id: sha256:87b15f790efca613794d25fe2bc822ee2420eb2ab847760e509a3059c25a8f17
  D5/S0/Conventions/WDigits.wdigits
    statement_id: sha256:aa2180b1084af7cbefca6a68881fef42788c73bdfa5199bf42d3e0334fe883d6
  D5/S0/Conventions/WDigits.wdigits_unique
    statement_id: sha256:aa2180b1084af7cbefca6a68881fef42788c73bdfa5199bf42d3e0334fe883d6
  D5/S0/Tower/GoldenGapWord.fibWord
    statement_id: sha256:cdb325ce53ff53959ea3b3de305df2d88f1d96e3874184a481eab5e31ab99105
  D5/S1/Digit/GoldenBase4AutomataOracle.zeckendorfMSDWord
    statement_id: sha256:f990811fc98754f8e49e726dbf288e55de8d9aad4a9c0ea717c835a7ba4cd55c
  D5/S1/Digit/GoldenBase4AutomataOracle.zeckendorfWordLength
    statement_id: sha256:f990811fc98754f8e49e726dbf288e55de8d9aad4a9c0ea717c835a7ba4cd55c
  D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_value
    statement_id: sha256:c9eb04d540060a6fcc48cfdae6a854fc9f415cdf25074b548701230488fe7948
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Digit/GoldenBase4IntervalMachine.fibPair_append_digit
    statement_id: sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
  D5/S1/Digit/GoldenZeckendorfLanguage.zeckendorfMSDWord_noAdjacentOnes
    statement_id: sha256:2baef40b44d5e279f984bb35fae6a9d5722c4b323008612d55ec215ec508b085
  D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates
    statement_id: sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
  D5/S1/Digit/ZeckendorfRawWindow.support
    statement_id: sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
  D5/S1/Words/GoldenFactorComplexity.goldenFactor
    statement_id: sha256:df6050c1b101dcd4fec43d349d0113d19f3b79299ce649379ef3d12887619f3e
  D5/S1/Words/GoldenWord.fibWord_length
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/GoldenWord.goldenWord
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/GoldenWord.goldenWord_eq_zeckendorf_criterion
    statement_id: sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
  D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore
    statement_id: sha256:21d1068a7fe4ff64e5c470d35523b7f9db5c4856b9455f35c2d32bcee8a691ed
  D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore_length
    statement_id: sha256:21d1068a7fe4ff64e5c470d35523b7f9db5c4856b9455f35c2d32bcee8a691ed
  D5/S1/Words/Palindromes/GoldenPalindromicPrefix.fibPalCore_palindrome
    statement_id: sha256:21d1068a7fe4ff64e5c470d35523b7f9db5c4856b9455f35c2d32bcee8a691ed
  D5/S1/Words/Powers/WordPower.length_wordPower
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
  D5/S1/Words/Powers/WordPower.wordPower
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
  D5/S1/Words/Powers/WordPower.wordPower_succ
    statement_id: sha256:a0ef906082beca39a4e1b33ef15215caf1af27b940976e0e624e541a11caad48
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.FridUpper
import D5.S1.Words.Palindromes.FridPrefix.PotentialBound
import D5.S1.Words.Palindromes.FridPrefix.RankProductA
import D5.S1.Words.Palindromes.FridPrefix.RankCyclesA
import D5.S1.Words.Palindromes.FridPrefix.ChunkTransport
import D5.S1.Digit.GoldenBase4DenseInput
import D5.S1.Digit.GoldenZeckendorfLanguage
import D5.S1.Words.Palindromes.FridPrefix.EndpointNecessity

namespace D5.S1.Words.FridPrefix
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Digit.GoldenBase4DenseInput
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit.GoldenZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S0.Conventions
open D5.S1.Words.Powers

/-- Exact minimum number of nonempty palindrome factors for Frid's prefix family. -/
def claim : Prop := ∀ k : ℕ, 1 ≤ k → PL (goldenFactor (N k) 0)=2*k+1

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- Frid's Fibonacci-prefix conjecture, with its matching upper bound. -/
theorem result : claim := by
  unfold claim
  intro k hk
  classical
  let W := 6*k
  let target : List (Fin 2) := wordPower (2*k-1) [1,0,0] ++ [1,0,1]
  have target_len : target.length=W := by
    simp only [target,List.length_append,length_wordPower,List.length_cons,List.length_nil]
    dsimp [W]; omega
  have target_canonical : NoAdjacentOnes target := by
    have aux (m : ℕ) : NoAdjacentOnes (wordPower m [1,0,0] ++ [1,0,1]) := by
      induction m with
      | zero => simp [wordPower,NoAdjacentOnes,List.isChain_cons]
      | succ m ih =>
        rw [wordPower_succ]
        simpa [NoAdjacentOnes,List.isChain_cons] using ih
    exact aux _
  have target_value : (fibPair target).1=N k := rfl
  have target_bound : N k < Nat.fib (W+2) := by
    have hc := source_word_coordinates target target_canonical
    rw [← target_value,← hc.2.2.1,← target_len]
    apply hc.1.sum_fib_lt
    intro a ha
    rcases List.mem_append.mp (List.mem_of_mem_head? ha) with h | h
    · exact hc.2.1 a h
    · simp only [List.mem_singleton] at h
      omega
  have encoding (i : ℕ) (hi : i≤N k) : ∃ w : List (Fin 2),
      w.length=W ∧ NoAdjacentOnes w ∧ (fibPair w).1=i := by
    have hib : i < Nat.fib (W+2) := lt_of_le_of_lt hi target_bound
    have hwlen : (zeckendorfMSDWord i).length ≤ W := by
      rw [length_zeckendorfMSDWord]
      cases hz : wdigits i with
      | nil => simp [zeckendorfWordLength,hz,W]; omega
      | cons a l =>
        have hg : Nat.greatestFib i < W+2 := Nat.greatestFib_lt.mpr hib
        have ha : a ≤ Nat.greatestFib i := by
          have he := decode_wdigits i
          rw [hz] at he
          have hf : Nat.fib a ≤ i := by simp only [List.map_cons,List.sum_cons] at he; omega
          exact Nat.le_greatestFib.mpr hf
        simp only [zeckendorfWordLength,hz]
        omega
    let w := List.replicate (W-(zeckendorfMSDWord i).length) 0 ++ zeckendorfMSDWord i
    have hwc : NoAdjacentOnes w := by
      have pad (z : ℕ) : NoAdjacentOnes (List.replicate z 0 ++ zeckendorfMSDWord i) := by
        induction z with
        | zero => simpa using zeckendorfMSDWord_noAdjacentOnes i
        | succ z ih => simpa [List.replicate_succ,NoAdjacentOnes,List.isChain_cons] using ih
      exact pad _
    have hwv : (fibPair w).1=i := by
      have pad (z : ℕ) : (fibPair (List.replicate z 0 ++ zeckendorfMSDWord i)).1=i := by
        induction z with
        | zero => simpa using zeckendorfMSDWord_value i
        | succ z ih => simpa [List.replicate_succ,fibPair] using ih
      exact pad _
    refine ⟨w,?_,hwc,hwv⟩
    simp only [w,List.length_append,List.length_replicate]; omega
  have partition (w : List (Fin 2)) (m : ℕ) (hl : w.length=6*m) :
      ∃ us : List (List (Fin 2)), us.flatten=w ∧ us.length=m ∧ ∀ u ∈ us,u.length=6 := by
    induction m generalizing w with
    | zero =>
      have he : w=[] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst w; exact ⟨[],rfl,rfl,by simp⟩
    | succ m ih =>
      have htake : (w.take 6).length=6 := by simp; omega
      have hdrop : (w.drop 6).length=6*m := by simp; omega
      obtain ⟨us,hflat,hlen,hs⟩ := ih (w.drop 6) hdrop
      refine ⟨w.take 6::us,?_,by simp [hlen],?_⟩
      · simp only [List.flatten_cons,hflat,List.take_append_drop]
      · intro u hu; rcases List.mem_cons.mp hu with rfl | hu; exact htake; exact hs u hu
  have enc (i : ℕ) (hi : i≤N k) : ∃ us : List (List (Fin 2)),
      us.length=k ∧ (∀ u∈us,u.length=6) ∧ NoAdjacentOnes us.flatten ∧
        (fibPair us.flatten).1=i := by
    obtain ⟨w,hwl,hwc,hwv⟩ := encoding i hi
    obtain ⟨us,hflat,hus,hlens⟩ := partition w k hwl
    exact ⟨us,hus,hlens,hflat.symm ▸ hwc,hflat.symm ▸ hwv⟩
  let B (i : ℕ) : List (List (Fin 2)) := if h : i≤N k then Classical.choose (enc i h) else []
  have B_spec (i : ℕ) (hi : i≤N k) :
      (B i).length=k ∧ (∀ u∈B i,u.length=6) ∧ NoAdjacentOnes (B i).flatten ∧
        (fibPair (B i).flatten).1=i := by
    simpa only [B,dif_pos hi] using Classical.choose_spec (enc i hi)
  have word_unique (u v : List (Fin 2)) (hu : NoAdjacentOnes u) (hv : NoAdjacentOnes v)
      (hl : u.length=v.length) (he : (fibPair u).1=(fibPair v).1) : u=v := by
    apply Std.Trichotomous.trichotomous (r := List.Lex (· < ·))
    · intro h; have hc := (canonical_lex_value u v hu hv hl).mpr h; omega
    · intro h; have hc := (canonical_lex_value v u hv hu hl.symm).mpr h; omega
  have blocks_unique (us vs : List (List (Fin 2)))
      (hu : ∀ u∈us,u.length=6) (hv : ∀ v∈vs,v.length=6) (he : us.flatten=vs.flatten) : us=vs := by
    induction us generalizing vs with
    | nil =>
      cases vs with
      | nil => rfl
      | cons v vs =>
        have hl := congrArg List.length he
        have hv6 := hv v (by simp)
        simp only [List.flatten_nil,List.flatten_cons,List.length_nil,List.length_append] at hl
        omega
    | cons u us ih =>
      cases vs with
      | nil =>
        have hl := congrArg List.length he
        have hu6 := hu u (by simp)
        simp only [List.flatten_nil,List.flatten_cons,List.length_nil,List.length_append] at hl
        omega
      | cons v vs =>
        have hu6 := hu u (by simp)
        have hv6 := hv v (by simp)
        have heads : u=v := by
          have h := congrArg (List.take 6) he
          have hU : (u++us.flatten).take 6=u := by rw [←hu6,List.take_left]
          have hV : (v++vs.flatten).take 6=v := by rw [←hv6,List.take_left]
          simpa only [List.flatten_cons,hU,hV] using h
        have tails : us.flatten=vs.flatten := by
          have h := congrArg (List.drop 6) he
          have hU : (u++us.flatten).drop 6=us.flatten := by rw [←hu6,List.drop_left]
          have hV : (v++vs.flatten).drop 6=vs.flatten := by rw [←hv6,List.drop_left]
          simpa only [List.flatten_cons,hU,hV] using h
        exact congrArg₂ List.cons heads (ih vs
          (fun w hw => hu w (List.mem_cons_of_mem _ hw))
          (fun w hw => hv w (List.mem_cons_of_mem _ hw)) tails)
  have flat_length (us : List (List (Fin 2))) (hu : ∀ u∈us,u.length=6) :
      us.flatten.length=6*us.length := by
    induction us with
    | nil => rfl
    | cons u us ih =>
      have hh := hu u (by simp)
      have ht := ih (fun v hv => hu v (List.mem_cons_of_mem _ hv))
      simp only [List.flatten_cons,List.length_append,List.length_cons]
      omega
  let seeds : List (List (Fin 2)) :=
    List.replicate (k-1) [1,0,0,1,0,0] ++ [[1,0,0,1,0,1]]
  have seeds_spec : seeds.length=k ∧ (∀ u∈seeds,u.length=6) ∧ seeds.flatten=target := by
    have powers (m : ℕ) : (List.replicate m ([1,0,0,1,0,0] : List (Fin 2))).flatten = wordPower (2*m) [1,0,0] := by
      induction m with
      | zero => rfl
      | succ m ih =>
        simp only [List.replicate_succ,List.flatten_cons,ih]
        rw [show 2*(m+1)=2*m+1+1 by omega,wordPower_succ,wordPower_succ]
        simp only [List.cons_append,List.nil_append]
    refine ⟨by simp [seeds]; omega,?_,?_⟩
    · intro u hu; simp only [seeds,List.mem_append,List.mem_replicate,List.mem_singleton] at hu
      rcases hu with ⟨_,rfl⟩ | rfl <;> rfl
    · dsimp [target]
      simp only [seeds,List.flatten_append,List.flatten_singleton,powers]
      rw [show 2*k-1=2*(k-1)+1 by omega,wordPower_succ]
      have comm (m : ℕ) : wordPower m ([1,0,0] : List (Fin 2)) ++ [1,0,0] =
          [1,0,0] ++ wordPower m [1,0,0] := by
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [wordPower_succ]
          simp only [List.append_assoc]
          rw [ih]
      change wordPower (2*(k-1)) ([1,0,0] : List (Fin 2)) ++ ([1,0,0] ++ [1,0,1]) =
        ([1,0,0] ++ wordPower (2*(k-1)) [1,0,0]) ++ [1,0,1]
      rw [←List.append_assoc,comm]
  have B_target : B (N k)=seeds := by
    have hb := B_spec (N k) (le_refl _)
    apply blocks_unique _ _ hb.2.1 seeds_spec.2.1
    apply word_unique _ _ hb.2.2.1
    · simpa only [seeds_spec.2.2] using target_canonical
    · rw [flat_length _ hb.2.1,hb.1,seeds_spec.2.2,target_len]
    · rw [hb.2.2.2,seeds_spec.2.2,target_value]
  let zeros : List (List (Fin 2)) := List.replicate k (List.replicate 6 0)
  have zeros_spec : zeros.length=k ∧ (∀u∈zeros,u.length=6) ∧
      NoAdjacentOnes zeros.flatten ∧ (fibPair zeros.flatten).1=0 := by
    have flatten_zero (m : ℕ) : (List.replicate m (List.replicate 6 (0 : Fin 2))).flatten =
        List.replicate (6*m) 0 := by
      induction m with
      | zero => rfl
      | succ m ih => rw [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]; congr 1; omega
    have canon (m : ℕ) : NoAdjacentOnes (List.replicate m (0 : Fin 2)) := by
      induction m with
      | zero => simp [NoAdjacentOnes]
      | succ m ih => simpa [List.replicate_succ,NoAdjacentOnes,List.isChain_cons] using ih
    have val (m : ℕ) : (fibPair (List.replicate m 0)).1=0 := by
      induction m with
      | zero => rfl
      | succ m ih => simpa [List.replicate_succ,fibPair] using ih
    refine ⟨by simp [zeros],?_,?_,?_⟩
    · intro u hu; obtain ⟨_,rfl⟩ := List.mem_replicate.mp hu; rfl
    · rw [flatten_zero]; exact canon _
    · rw [flatten_zero]; exact val _
  have B_zero : B 0=zeros := by
    have hb := B_spec 0 (Nat.zero_le _)
    apply blocks_unique _ _ hb.2.1 zeros_spec.2.1
    apply word_unique _ _ hb.2.2.1 zeros_spec.2.2.1
    · rw [flat_length _ hb.2.1,flat_length _ zeros_spec.2.1,hb.1,zeros_spec.1]
    · rw [hb.2.2.2,zeros_spec.2.2.2]
  let S (i : ℕ) : ℤ := chunkScore rankA ((B i).map (fun w => Nat.ofDigits 2 (w.reverse.map Fin.val)))
  have hz : S 0=0 := by
    change chunkScore rankA ((B 0).map (fun w => Nat.ofDigits 2 (w.reverse.map Fin.val)))=0
    rw [show B 0=zeros from B_zero]
    have chunk0 : Nat.ofDigits 2 ((List.replicate 6 (0 : Fin 2)).reverse.map Fin.val)=0 := by decide +kernel
    simp only [zeros,List.map_replicate,chunk0]
    let advance (s : ℕ × ℤ) (x : ℕ) :=
      ((rankA.transitions.getD s.1 #[]).getD x 0,s.2+(rankA.weights.getD s.1 #[]).getD x 0)
    have h00 : advance (0,0) 0=(0,0) := by decide +kernel
    have loop (m : ℕ) : (List.replicate m 0).foldl advance (0,0)=(0,0) := by
      induction m with
      | zero => rfl
      | succ m ih => simpa only [List.replicate_succ,List.foldl_cons,h00] using ih
    exact congrArg Prod.snd (loop k)
  have he (i j : ℕ) (hij : i<j) (hj : j≤N k)
      (hp : List.Palindrome (goldenFactor (j-i) i)) : S j≤S i+1 := by
    have hi : i≤N k := by omega
    have bi := B_spec i hi
    have bj := B_spec j hj
    have hp' : List.Palindrome (goldenFactor
        ((fibPair (B j).flatten).1-(fibPair (B i).flatten).1) (fibPair (B i).flatten).1) := by
      simpa only [bi.2.2.2,bj.2.2.2] using hp
    have hbits := palindrome_endpoint _ _ bi.2.2.1 bj.2.2.1
      (by rw [flat_length _ bi.2.1,flat_length _ bj.2.1,bi.1,bj.1])
      (by simpa only [bi.2.2.2,bj.2.2.2] using hij) hp'
    have hchunks := endpoint_chunked (B i) (B j) (bi.1.trans bj.1.symm) bi.2.1 bj.2.1 hbits
    have hb := a_endpoint_score_bound _ hchunks
    let cv (w : List (Fin 2)) := Nat.ofDigits 2 (w.reverse.map Fin.val)
    have hf : ((B i).zip (B j)).map (fun p => cv p.1) = (B i).map cv := by
      have h := congrArg (List.map cv) (List.map_fst_zip (l₁ := B i) (l₂ := B j) (by omega))
      simpa only [List.map_map,Function.comp_def] using h
    have hs : ((B i).zip (B j)).map (fun p => cv p.2) = (B j).map cv := by
      have h := congrArg (List.map cv) (List.map_snd_zip (l₁ := B i) (l₂ := B j) (by omega))
      simpa only [List.map_map,Function.comp_def] using h
    change chunkScore rankA ((B j).map cv) ≤ chunkScore rankA ((B i).map cv)+1
    simpa only [List.map_map,Function.comp_def,←hf,←hs,cv] using hb
  have htarget : S (N k)=2*(k : ℤ)+1 := by
    change chunkScore rankA ((B (N k)).map (fun w => Nat.ofDigits 2 (w.reverse.map Fin.val)))=_
    rw [B_target]
    have c36 : Nat.ofDigits 2 ([1,0,0,1,0,0].reverse.map (Fin.val (n := 2)))=36 := by decide +kernel
    have c37 : Nat.ofDigits 2 ([1,0,0,1,0,1].reverse.map (Fin.val (n := 2)))=37 := by decide +kernel
    simp only [seeds,List.map_append,List.map_replicate,List.map_singleton,c36,c37]
    have hh := a_seed_cycle (k-1) 0
    simp only [List.replicate_zero,List.nil_append] at hh
    rw [hh]
    omega
  have lower := potential_pl_bound S hz (N k) he
  rw [htarget] at lower
  have upper := frid_upper k hk
  omega

end D5.S1.Words.FridPrefix
