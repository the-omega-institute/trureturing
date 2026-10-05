/- GID: D5/S1/Words/Palindromes/FridPrefix/CanonicalNecessity
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/CanonicalNecessity
   mirror-E: none(waiver:literal-canonical-endpoint-rule)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S1/Words/Palindromes/FridPrefix/CanonicalNecessity.frid_canonical_necessity; instance=D5/S1/Words/Palindromes/FridPrefix/EndpointAutomaton.endpointRows
   digest: Each Fibonacci palindrome selects a zero digit and complements all lower digits. -/

/-
proof_shape: content (frid_canonical_necessity).
escape_witness: reconstruction of the selected pivot and complementary legal numeral from a path.
admission_basis: escape-witness.
Direct frozen dependencies:
  D5/S0/Automata/BinaryZeckendorfLanguage; module statement_id sha256:87b15f790efca613794d25fe2bc822ee2420eb2ab847760e509a3059c25a8f17
    D5/S0/Automata/BinaryZeckendorfLanguage.NoAdjacentOnes: sha256:5f646bb806cb8cd8c7f639908d761f070355bdbbfede407d3acc033120cb2fce
  D5/S0/Conventions/WDigits; module statement_id sha256:aa2180b1084af7cbefca6a68881fef42788c73bdfa5199bf42d3e0334fe883d6
    D5/S0/Conventions/WDigits.wValue: sha256:87b43eccb6b23638293eebe3331575cd1a9422349bd7f7afe57703d1d8177f15
    D5/S0/Conventions/WDigits.wdigits: sha256:dbbd02d012e74f26be610b7e393f5377722c7d06adb53e7c4c73bbbb488f25a0
    D5/S0/Conventions/WDigits.wdigits_unique: sha256:a85c044d3f237c1d3c2a95a515470e2bcc94ebca613e89c39f603471e61bd20f
  D5/S1/Digit/GoldenBase4AutomataOracle; module statement_id sha256:f990811fc98754f8e49e726dbf288e55de8d9aad4a9c0ea717c835a7ba4cd55c
    D5/S1/Digit/GoldenBase4AutomataOracle.zeckendorfMSDWord: sha256:acb410a3ea49a128f721dc40e1297b58e930c4445b049527d09d30b129159dfa
    D5/S1/Digit/GoldenBase4AutomataOracle.zeckendorfWordLength: sha256:d567999b715031c71e756eecb88aa78e0e2d5c0ee1c4640ce1421c04fcbd5508
  D5/S1/Digit/GoldenBase4DenseInput; module statement_id sha256:c9eb04d540060a6fcc48cfdae6a854fc9f415cdf25074b548701230488fe7948
    D5/S1/Digit/GoldenBase4DenseInput.zeckendorfMSDWord_value: sha256:af5bc097afc0c12837ab22022f2fa9057009b6972f487b6c8e0cd9b1a12d60ea
  D5/S1/Digit/GoldenBase4IntervalMachine; module statement_id sha256:fa818cf4cfbb993ac00cef7564eb29f10e600559bada3288823702175e0943fa
    D5/S1/Digit/GoldenBase4IntervalMachine.fibPair: sha256:cbaa673b2d8bdcd2f56ac60fbd4b8496a29d1b3a9a6aa673af463265b40f3053
    D5/S1/Digit/GoldenBase4IntervalMachine.fibPair_append_digit: sha256:7a0a621968ae16cd10eaf33651c664ef339406e303978ed9f593bef57ffdf8c7
  D5/S1/Digit/GoldenZeckendorfLanguage; module statement_id sha256:2baef40b44d5e279f984bb35fae6a9d5722c4b323008612d55ec215ec508b085
    D5/S1/Digit/GoldenZeckendorfLanguage.zeckendorfMSDWord_noAdjacentOnes: sha256:53808d78bf10fcdcbf7d5a7e9aac002db41496b64bcb55cab8456c5b632a71be
  D5/S1/Digit/ZeckendorfRawWindow; module statement_id sha256:841fd6e8c2b015fd6ce98338ffd97a31a2b4aec15051a79663831dce874157da
    D5/S1/Digit/ZeckendorfRawWindow.source_word_coordinates: sha256:deeba6dbde4255f8972f23006c02b555aa13a8eb176d45ddc52b66429d5fc2b2
    D5/S1/Digit/ZeckendorfRawWindow.support: sha256:6e85f7358067b00dc6b9dd199d81bc985b8e710bf1a0136ac0450f0c136dec49
  D5/S1/Words/GoldenFactorComplexity; module statement_id sha256:df6050c1b101dcd4fec43d349d0113d19f3b79299ce649379ef3d12887619f3e
    D5/S1/Words/GoldenFactorComplexity.goldenFactor: sha256:45653c076830e3d013ea9e728d954ed6444072d1161a1656d45e0c92ab921ed8
  D5/S1/Words/GoldenWord; module statement_id sha256:5b627b7ad0e8bf353fc2f705e2a1b10313bd8a4217a1734f4074c6797bfc5c6a
    D5/S1/Words/GoldenWord.goldenWord: sha256:8f1246e0f7522a641bfb80a0177aa34160f096f22a06c1e4b8b73d07921da29b
    D5/S1/Words/GoldenWord.goldenWord_eq_zeckendorf_criterion: sha256:d9a6a3a64cfb0d977689cda13bc159abda2ae8ea746c279711077d4eac231078
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.EndpointNecessity
import D5.S1.Words.Palindromes.FridPrefix.CarryBounds
import D5.S1.Digit.GoldenBase4DenseInput
import D5.S1.Digit.GoldenZeckendorfLanguage

namespace D5.S1.Words.FridPrefix
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.GoldenBase4DenseInput
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit.GoldenZeckendorfLanguage
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S0.Conventions

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
set_option synthInstance.maxSize 100000 in
/-- Literal canonical zero-digit necessity for every nonempty Fibonacci palindrome. -/
theorem frid_canonical_necessity (i j : ℕ) (hij : i<j)
    (hpal : List.Palindrome (goldenFactor (j-i) i)) :
    ∃ m : ℕ, m+2 ∉ wdigits i ∧
      (j : ℤ) = (i : ℤ) + (wValue (m+2) : ℤ) - 2 -
        2 * ((((wdigits i).filter (fun r => r < m+2)).map Nat.fib).sum : ℤ) := by
  have rule (u v : List (Fin 2)) (hu : NoAdjacentOnes u)
      (hv : NoAdjacentOnes v) (hl : u.length=v.length)
      (ha : u.zip v ∈ endpoint.accepts) :
      ∃ m : ℕ, m+2 ∉ wdigits (fibPair u).1 ∧
        ((fibPair v).1 : ℤ) = (fibPair u).1 + (wValue (m+2) : ℤ) - 2 -
          2 * ((((wdigits (fibPair u).1).filter (fun r => r < m+2)).map Nat.fib).sum : ℤ) := by
    let coordinates : Array (Bool × (ℤ × ℤ)) := #[(false,(0,0)),(true,(1,0)),(false,(-1,0)),(true,(0,0)),(false,(1,0)),(false,(0,0)),(true,(-1,1)),(true,(1,-1)),(false,(1,-1)),(true,(0,0)),(false,(-1,1)),(true,(0,0)),(true,(-1,0)),(true,(-1,0)),(false,(-1,0)),(false,(1,0)),(true,(-1,0))]
    let mode (q : Fin 17) := (coordinates[q.val]!).1
    let carry (q : Fin 17) := (coordinates[q.val]!).2
    let complement : Fin 2 → Fin 2 := Fin.rev
    have finite : ∀ q t : Fin 17, ∀ x y : Fin 2,
        t ∈ endpoint.step q (x,y) → ∃ z : Fin 2,
          (mode q=false → (mode t=false ∧ z=x) ∨ (x=0 ∧ mode t=true ∧ z=1)) ∧
          (mode q=true → mode t=true ∧ z=complement x) ∧
          carry t=carryStep (carry q) ((z.val : ℤ)-y.val) := by
      simp only [endpoint,Set.mem_ofPred_eq]
      dsimp [mode,carry,coordinates,complement]
      decide +kernel
    have path_word {q t : Fin 17} {pairs : List (Fin 2 × Fin 2)}
        (path : endpoint.Path q t pairs) : ∃ zs : List (Fin 2),
        zs.length=pairs.length ∧
        (mode q=false → (mode t=false ∧ zs=pairs.map Prod.fst) ∨
          ∃ H L : List (Fin 2), pairs.map Prod.fst=H++0::L ∧ zs=H++1::L.map complement) ∧
        (mode q=true → mode t=true ∧ zs=pairs.map (fun d => complement d.1)) ∧
        ((pairs.zip zs).map (fun (d,z) => (z.val : ℤ)-d.2.val)).foldl carryStep (carry q)=carry t := by
      induction path with
      | nil q =>
        refine ⟨[],rfl,?_,?_,rfl⟩
        · intro h; exact Or.inl ⟨h,rfl⟩
        · intro h; exact ⟨h,rfl⟩
      | cons r q t d pairs hm path ih =>
        obtain ⟨z,hmode0,hmode1,hcarry⟩ := finite q r d.1 d.2 hm
        obtain ⟨zs,hzlen,hz0,hz1,hfold⟩ := ih
        refine ⟨z::zs,by simp [hzlen],?_,?_,?_⟩
        · intro hq
          rcases hmode0 hq with ⟨hr,hzx⟩ | ⟨hx,hr,hz⟩
          · rcases hz0 hr with ⟨ht,hzs⟩ | ⟨H,L,hH,hL⟩
            · exact Or.inl ⟨ht,by simp [hzx,hzs]⟩
            · right; refine ⟨d.1::H,L,?_,?_⟩
              · simp only [List.map_cons,hH,List.cons_append]
              · simp only [hzx,hL,List.cons_append]
          · have hs := (hz1 hr).2
            right; refine ⟨[],pairs.map Prod.fst,?_,?_⟩
            · simp [hx]
            · simp [hz,hs,List.map_map,Function.comp_def]
        · intro hq
          obtain ⟨hr,hz⟩ := hmode1 hq
          exact ⟨(hz1 hr).1,by simp [hz,(hz1 hr).2]⟩
        · simpa only [List.zip_cons_cons,List.map_cons,List.foldl_cons,←hcarry] using hfold
    obtain ⟨q,hq,t,ht,⟨path⟩⟩ := NFA.accepts_iff_exists_path.mp ha
    have hq0 : q=0 := Fin.ext hq
    subst q
    have hmode : mode t=true ∧ carry t=(0,0) := by
      have hmem : t.val ∈ [3,9,11] := ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with h | h | h
      · have he : t=(3 : Fin 17) := Fin.ext h; subst t; decide +kernel
      · have he : t=(9 : Fin 17) := Fin.ext h; subst t; decide +kernel
      · have he : t=(11 : Fin 17) := Fin.ext h; subst t; decide +kernel
    obtain ⟨zs,hzlen,hz0,hz1,hfold⟩ := path_word path
    have start : mode 0=false := by decide +kernel
    obtain ⟨H,L,hU,hZ⟩ : ∃ H L : List (Fin 2), u=H++0::L ∧ zs=H++1::L.map complement := by
      rcases hz0 start with ⟨h,_⟩ | hh
      · rw [hmode.1] at h; contradiction
      · simpa only [List.map_fst_zip (le_of_eq hl)] using hh
    have hcarry : ((zs.zip v).map (fun (z,y) => (z.val : ℤ)-y.val)).foldl carryStep (0,0)=(0,0) := by
      have hh : ((u.zip v).zip zs).map (fun (d,z) => (z.val : ℤ)-d.2.val)=
          (zs.zip v).map (fun (z,y) => (z.val : ℤ)-y.val) := by
        apply List.ext_getElem
        · simp; omega
        · intro i hi hi'; simp
      simpa only [hh,show carry 0=(0,0) from rfl,hmode.2] using hfold
    have registers (pairs : List (Fin 2 × Fin 2)) :
        let s := (pairs.map (fun d => (d.1.val : ℤ)-d.2.val)).foldl carryStep (0,0)
        ((fibPair (pairs.map Prod.fst)).1 : ℤ)-(fibPair (pairs.map Prod.snd)).1=s.1+2*s.2 ∧
        ((fibPair (pairs.map Prod.fst)).2 : ℤ)-(fibPair (pairs.map Prod.snd)).2=2*s.1+3*s.2 := by
      induction pairs using List.reverseRecOn with
      | nil => simp [fibPair,carryStep]
      | append_singleton d pairs ih =>
        simp only [List.map_append,List.map_singleton,fibPair_append_digit,List.foldl_append,
          List.foldl_cons,List.foldl_nil,carryStep]
        dsimp only at ih ⊢
        push_cast
        constructor <;> linarith [ih.1,ih.2]
    have same : (fibPair zs).1=(fibPair v).1 := by
      have hh := (registers (zs.zip v)).1
      have hvlen : zs.length=v.length := by simp at hzlen; omega
      simp only [List.map_fst_zip (le_of_eq hvlen),List.map_snd_zip (le_of_eq hvlen.symm),hcarry] at hh
      omega
    have common (H a b : List (Fin 2)) (hab : a.length=b.length) :
        ((fibPair (H++a)).1 : ℤ)-(fibPair (H++b)).1 =
          ((fibPair a).1 : ℤ)-(fibPair b).1 := by
      induction H with
      | nil => simp
      | cons d H ih =>
        simp only [List.cons_append,fibPair,List.length_append,hab]
        push_cast
        linarith
    have sum_complement (L : List (Fin 2)) :
        (fibPair L).1+(fibPair (L.map complement)).1+2=Nat.fib (L.length+3) := by
      induction L with
      | nil => norm_num [fibPair,Nat.fib]
      | cons a L ih =>
        have hc : a.val+(complement a).val=1 := by simp only [complement,Fin.val_rev]; omega
        simp only [List.map_cons,fibPair,List.length_map,List.length_cons]
        have hf := Nat.fib_add_two (n := L.length+2)
        have hr : a.val*Nat.fib (L.length+2)+(complement a).val*Nat.fib (L.length+2)=Nat.fib (L.length+2) := by
          rw [←Nat.add_mul,hc,Nat.one_mul]
        norm_num only [Nat.add_assoc] at hf ⊢
        omega
    have low (H L : List (Fin 2)) :
        L.length+2 ∉ support (H++0::L) ∧
        (support (H++0::L)).filter (fun r => r < L.length+2)=support L := by
      have bound : ∀ r ∈ support L, r < L.length+2 := by
        have h := source_word_coordinates u hu
        -- An arbitrary support has this positional bound without canonicity.
        intro r hr
        induction L with
        | nil => simp [support] at hr
        | cons a L ih =>
          by_cases ha : a=0
          · simp only [support,if_pos ha] at hr; have h := ih hr; simp; omega
          · simp only [support,if_neg ha,List.mem_cons] at hr
            rcases hr with rfl | hr
            · simp
            · have h := ih hr; simp; omega
      induction H with
      | nil =>
        simp only [List.nil_append,support,if_pos rfl]
        refine ⟨?_,?_⟩
        · intro hm; have h := bound _ hm; omega
        · exact List.filter_eq_self.mpr (by simpa using bound)
      | cons a H ih =>
        by_cases ha : a=0
        · simpa only [List.cons_append,support,if_pos ha] using ih
        · simp only [List.cons_append,support,if_neg ha,List.length_append,List.length_cons,
            List.mem_cons,List.filter_cons]
          have hn : ¬(H.length+(L.length+1)+2 < L.length+2) := by omega
          simp only [decide_eq_false hn,Bool.false_eq_true,not_false_eq_true,if_false]
          have he : L.length+2 ≠ H.length+(L.length+1)+2 := by omega
          simp only [he,false_or]
          exact ih
    have canonicalL : NoAdjacentOnes L := by
      rw [hU] at hu
      exact (List.isChain_append.mp hu).2.1.tail
    have hc := source_word_coordinates u (by simpa only [←hU] using hu)
    have hs : support u=wdigits (fibPair u).1 := wdigits_unique hc.1 hc.2.2.1
    have hlow := low H L
    have hvl := (source_word_coordinates L canonicalL).2.2.1
    refine ⟨L.length,?_,?_⟩
    · rw [←hs,hU]; exact hlow.1
    · rw [←hs,hU,hlow.2,hvl,←same,hZ]
      have hh := common H (1::L.map complement) (0::L) (by simp)
      simp only [fibPair,List.length_map,List.length_cons] at hh
      have hsum := sum_complement L
      have hf := Nat.fib_add_two (n := L.length+2)
      dsimp [wValue]
      simp only [Fin.val_one,Fin.val_zero,Nat.one_mul,Nat.zero_mul,Nat.zero_add] at hh
      push_cast at hh ⊢
      norm_num only [Nat.add_assoc] at hf hsum hh ⊢
      omega
  let W := max (zeckendorfMSDWord i).length (zeckendorfMSDWord j).length
  let encoding (n : ℕ) := List.replicate (W-(zeckendorfMSDWord n).length) 0 ++
    zeckendorfMSDWord n
  have spec (n : ℕ) (hn : (zeckendorfMSDWord n).length≤W) :
      (encoding n).length=W ∧ NoAdjacentOnes (encoding n) ∧ (fibPair (encoding n)).1=n := by
    have canon (z : ℕ) : NoAdjacentOnes (List.replicate z 0 ++ zeckendorfMSDWord n) := by
      induction z with
      | zero => simpa using zeckendorfMSDWord_noAdjacentOnes n
      | succ z ih => simpa [List.replicate_succ,NoAdjacentOnes,List.isChain_cons] using ih
    have value (z : ℕ) : (fibPair (List.replicate z 0 ++ zeckendorfMSDWord n)).1=n := by
      induction z with
      | zero => simpa using zeckendorfMSDWord_value n
      | succ z ih => simpa [List.replicate_succ,fibPair] using ih
    refine ⟨?_,canon _,value _⟩
    simp only [encoding,List.length_append,List.length_replicate]; omega
  have si := spec i (Nat.le_max_left _ _)
  have sj := spec j (Nat.le_max_right _ _)
  have ep := palindrome_endpoint (encoding i) (encoding j) si.2.1 sj.2.1
    (si.1.trans sj.1.symm) (by simpa only [si.2.2,sj.2.2] using hij)
    (by simpa only [si.2.2,sj.2.2] using hpal)
  simpa only [si.2.2,sj.2.2] using rule (encoding i) (encoding j) si.2.1 sj.2.1
    (si.1.trans sj.1.symm) ep

end D5.S1.Words.FridPrefix
