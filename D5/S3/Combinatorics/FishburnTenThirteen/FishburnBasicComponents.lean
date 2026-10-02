/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponents
   mirror-E: none(waiver:unique-normalized-sum-components)
   anchors: []
   utility: none
   digest: Unique sum components give a reversible first-block counting recurrence. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSum

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponents

open D5.S3.Combinatorics.Nonnesting
open NonnestingBasicSum FishburnDefs FishburnBasicSum

def assemble : List (List ℕ) → List ℕ
  | [] => []
  | block :: rest => directSum block.length block (assemble rest)

theorem unique_sum_components (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (patterns : List (List ℕ))
    (hpatterns : ∀ pattern ∈ patterns, pattern ≠ [] ∧ sumIndecomposable pattern ∧
      (∀ value ∈ pattern, 1 ≤ value) ∧
      ∀ rank, 1 ≤ rank → rank ≤ NonnestingDefs.letters pattern → rank ∈ pattern) :
    (∃! parts : List (List ℕ), assemble parts = p ∧
      (∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
      (p ∈ avoiders n patterns ↔
        ∀ block ∈ parts, block ∈ avoiders block.length patterns)) ∧
    (∀ components : List (List ℕ),
      (∀ block ∈ components, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
      (assemble components ∈ avoiders (assemble components).length patterns ↔
        ∀ block ∈ components, block ∈ avoiders block.length patterns)) ∧
    (avoiders 0 patterns).ncard = 1 ∧
    (∀ size, ((avoiders (size + 1) patterns).ncard =
      ∑ cut : Fin (size + 1),
        {block : List ℕ | block ∈ avoiders (cut.val + 1) patterns ∧
          sumIndecomposable block}.ncard * (avoiders (size - cut.val) patterns).ncard) ∧
      ∃ decomposition :
          (Σ cut : Fin (size + 1),
            {block : List ℕ | block ∈ avoiders (cut.val + 1) patterns ∧
              sumIndecomposable block} × avoiders (size - cut.val) patterns) ≃
            avoiders (size + 1) patterns,
        ∀ entry, (decomposition entry).val =
          directSum (entry.1.val + 1) entry.2.1.val entry.2.2.val) ∧
    (let sequences (size count : ℕ) : Set (List (List ℕ)) := {parts |
      (∀ block ∈ parts, block ≠ [] ∧ sumIndecomposable block ∧
        block ∈ avoiders block.length patterns) ∧
      (assemble parts).length = size ∧ parts.length = count}
     (∀ size, (sequences size 0).ncard = if size = 0 then 1 else 0) ∧
     ∀ size count, ((sequences (size + 1) (count + 1)).ncard =
       ∑ cut : Fin (size + 1),
         {block : List ℕ | block ∈ avoiders (cut.val + 1) patterns ∧
           sumIndecomposable block}.ncard * (sequences (size - cut.val) count).ncard) ∧
       ∃ decomposition :
           (Σ cut : Fin (size + 1),
             {block : List ℕ | block ∈ avoiders (cut.val + 1) patterns ∧
               sumIndecomposable block} × sequences (size - cut.val) count) ≃
             sequences (size + 1) (count + 1),
         (∀ entry, (decomposition entry).val = entry.2.1.val :: entry.2.2.val) ∧
         ∀ weight : List (List ℕ) → Polynomial ℚ,
           (∑ᶠ parts : sequences (size + 1) (count + 1), weight parts.val) =
             ∑ cut : Fin (size + 1),
               ∑ᶠ block : {block : List ℕ | block ∈ avoiders (cut.val + 1) patterns ∧
                 sumIndecomposable block},
                 ∑ᶠ rest : sequences (size - cut.val) count,
                   weight (block.val :: rest.val)) := by
  classical
  have hsplit (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (cut : ℕ) (hc : cut ≤ word.length)
      (hsep : ∀ a ∈ word.take cut, ∀ b ∈ word.drop cut, a < b) :
      (word.take cut).Perm (List.range' 1 cut) ∧
        ((word.drop cut).map (· - cut)).Perm (List.range' 1 (size - cut)) ∧
        word = directSum cut (word.take cut) ((word.drop cut).map (· - cut)) := by
    have hlen : word.length = size := by simpa using hp.length_eq
    have htake : (word.take cut).length = cut := by simp [List.length_take, hc]
    have hnd : (word.take cut).Nodup :=
      (hp.nodup_iff.mpr (List.nodup_range' 1)).sublist (List.take_sublist cut word)
    have hvalues (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ size := by
      have hr := hp.mem_iff.mp hv
      simp only [List.mem_range', Nat.one_mul] at hr
      obtain ⟨index, hi, heq⟩ := hr
      omega
    have hlow : ∀ value ∈ word.take cut, value ≤ cut := by
      intro value hv
      by_contra hlarge
      have hsmall : List.range' 1 cut ⊆ word.take cut := by
        intro small hs
        have hsmallbound : 1 ≤ small ∧ small ≤ cut := by
          simp only [List.mem_range', Nat.one_mul] at hs
          obtain ⟨index, hi, heq⟩ := hs
          omega
        have hmem : small ∈ word := by
          apply hp.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨small - 1, by omega, by omega⟩
        have happ : small ∈ word.take cut ++ word.drop cut := by simpa using hmem
        rcases List.mem_append.mp happ with hprefix | hsuffix
        · exact hprefix
        · have := hsep value hv small hsuffix
          omega
      have hsmallperm := ((List.nodup_range' 1).subperm hsmall).perm_of_length_le
        (by simp [htake])
      have hsmallvalue := hsmallperm.symm.mem_iff.mp hv
      simp only [List.mem_range', Nat.one_mul] at hsmallvalue
      obtain ⟨index, hi, heq⟩ := hsmallvalue
      omega
    have hprefix : (word.take cut).Perm (List.range' 1 cut) := by
      apply (hnd.subperm ?_).perm_of_length_le
      · simp [htake]
      · intro value hv
        have hpositive := (hvalues value ((List.take_sublist cut word).subset hv)).1
        have hupper := hlow value hv
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨value - 1, by omega, by omega⟩
    have hwhole : (List.range' 1 cut ++ word.drop cut).Perm
        (List.range' 1 cut ++ List.range' (1 + cut) (size - cut)) := by
      have hbase : (word.take cut ++ word.drop cut).Perm
          (List.range' 1 cut ++ List.range' (1 + cut) (size - cut)) := by
        rw [List.take_append_drop, List.range'_append_1]
        have hsum : cut + (size - cut) = size := by omega
        rwa [hsum]
      exact (hprefix.symm.append_right _).trans hbase
    have hsuffix : (word.drop cut).Perm (List.range' (1 + cut) (size - cut)) :=
      (List.perm_append_left_iff _).mp hwhole
    have hnormalized : ((word.drop cut).map (· - cut)).Perm
        (List.range' 1 (size - cut)) := by
      have hmapped := hsuffix.map (· - cut)
      rw [List.map_sub_range' (by omega : cut ≤ 1 + cut)] at hmapped
      simpa using hmapped
    have hrestore : shift cut ((word.drop cut).map (· - cut)) = word.drop cut := by
      simp only [shift, List.map_map]
      conv_rhs => rw [← List.map_id' (word.drop cut)]
      apply List.map_congr_left
      intro value hv
      have hvalue := hsuffix.mem_iff.mp hv
      simp only [List.mem_range', Nat.one_mul] at hvalue
      obtain ⟨index, hi, heq⟩ := hvalue
      dsimp [Function.comp_def]
      omega
    exact ⟨hprefix, hnormalized, by rw [directSum, hrestore, List.take_append_drop]⟩
  have hassembleperm (parts : List (List ℕ))
      (hparts : ∀ block ∈ parts, block.Perm (List.range' 1 block.length)) :
      (assemble parts).Perm (List.range' 1 (assemble parts).length) := by
    induction parts with
    | nil => simp [assemble]
    | cons block rest ih =>
      have hp := hparts block (by simp)
      have hrest := ih (fun component hc => hparts component (by simp [hc]))
      have hmapped := hrest.map (fun value => block.length + value)
      rw [List.map_add_range'] at hmapped
      have hshift : (shift block.length (assemble rest)).Perm
          (List.range' (1 + block.length) (assemble rest).length) := by
        simpa [shift, Nat.add_comm] using hmapped
      simpa [assemble, directSum, shift, List.range'_append_1] using hp.append hshift
  have happend (first second : List (List ℕ)) :
      assemble (first ++ second) =
        directSum (assemble first).length (assemble first) (assemble second) := by
    induction first with
    | nil => simp [assemble, directSum, shift]
    | cons block rest ih =>
      simp only [List.cons_append, assemble, ih, directSum, shift, List.length_append,
        List.length_map, List.map_append, List.map_map, List.append_assoc]
      congr 2
      apply List.map_congr_left
      intro value _
      simp [Nat.add_comm, Nat.add_left_comm]
  have hclosure (parts : List (List ℕ))
      (hparts : ∀ block ∈ parts, block ≠ [] ∧
        block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) :
      assemble parts ∈ avoiders (assemble parts).length patterns ↔
        ∀ block ∈ parts, block ∈ avoiders block.length patterns := by
    induction parts with
    | nil =>
      have hnil : [] ∈ avoiders 0 patterns := by
        refine ⟨by simp, ?_, ?_⟩
        · intro before later hgap hlater
          simp only [List.length_nil] at hlater
          omega
        · intro pattern hp hocc
          obtain ⟨values, _, _, hsub, _⟩ := hocc
          apply (hpatterns pattern hp).1
          simpa using List.sublist_nil.mp hsub
      simpa only [assemble, List.length_nil, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, iff_true] using hnil
    | cons block rest ih =>
      have hb := hparts block (by simp)
      have hr : ∀ component ∈ rest, component ≠ [] ∧
          component.Perm (List.range' 1 component.length) ∧ sumIndecomposable component :=
        fun component hc => hparts component (by simp [hc])
      have hrestperm := hassembleperm rest (fun component hc => (hr component hc).2.1)
      have hleft : ∀ value ∈ block, value ≤ block.length := by
        intro value hv
        have hm := hb.2.1.mem_iff.mp hv
        simp only [List.mem_range', Nat.one_mul] at hm
        obtain ⟨index, hi, heq⟩ := hm
        omega
      have hright : ∀ value ∈ assemble rest, 1 ≤ value := by
        intro value hv
        have hm := hrestperm.mem_iff.mp hv
        simp only [List.mem_range', Nat.one_mul] at hm
        obtain ⟨index, hi, heq⟩ := hm
        omega
      have hfish := isFishburn_directSum_iff block.length block (assemble rest) hleft hright
      have hocc (pattern : List ℕ) (hp : pattern ∈ patterns) :=
        occurs_directSum_iff block.length block (assemble rest) pattern hleft hright
          (hpatterns pattern hp).2.1 (hpatterns pattern hp).2.2.1
          (hpatterns pattern hp).2.2.2
      have hstep : assemble (block :: rest) ∈
          avoiders (assemble (block :: rest)).length patterns ↔
          block ∈ avoiders block.length patterns ∧
            assemble rest ∈ avoiders (assemble rest).length patterns := by
        constructor
        · intro hchild
          have hfishboth := hfish.mp hchild.2.1
          refine ⟨⟨hb.2.1, hfishboth.1, ?_⟩, ⟨hrestperm, hfishboth.2, ?_⟩⟩
          · intro pattern hp hbad
            exact hchild.2.2 pattern hp ((hocc pattern hp).mpr (Or.inl hbad))
          · intro pattern hp hbad
            exact hchild.2.2 pattern hp ((hocc pattern hp).mpr (Or.inr hbad))
        · rintro ⟨hblock, hrest⟩
          refine ⟨hassembleperm (block :: rest) (fun component hc => (hparts component hc).2.1),
            hfish.mpr ⟨hblock.2.1, hrest.2.1⟩, ?_⟩
          intro pattern hp hbad
          rcases (hocc pattern hp).mp hbad with hleftbad | hrightbad
          · exact hblock.2.2 pattern hp hleftbad
          · exact hrest.2.2 pattern hp hrightbad
      rw [hstep, ih hr]
      simp only [List.mem_cons, forall_eq_or_imp]
  have hdecomposition (n : ℕ) (p : List ℕ)
      (hperm : p.Perm (List.range' 1 n)) :
      ∃! parts : List (List ℕ), assemble parts = p ∧
        (∀ block ∈ parts, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
        (p ∈ avoiders n patterns ↔
          ∀ block ∈ parts, block ∈ avoiders block.length patterns) := by
    induction n using Nat.strong_induction_on generalizing p with
    | h size ih =>
      have hsize : p.length = size := by simpa using hperm.length_eq
      have hexists : ∃ parts : List (List ℕ), assemble parts = p ∧
          ∀ block ∈ parts, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
        by_cases hempty : p = []
        · exact ⟨[], by simp [assemble, hempty]⟩
        by_cases hindec : sumIndecomposable p
        · refine ⟨[p], ?_, ?_⟩
          · simp [assemble, directSum, shift]
          · intro block hblock
            simp only [List.mem_singleton] at hblock
            subst block
            exact ⟨hempty, by simpa [hsize] using hperm, hindec⟩
        · have hfailure : ∃ cut : Fin p.length, 0 < cut.val ∧
              ∀ first : Fin (p.take cut.val).length,
                ∀ second : Fin (p.drop cut.val).length,
                  (p.take cut.val).get first < (p.drop cut.val).get second := by
            simpa only [sumIndecomposable, not_forall, not_exists, not_le, exists_prop]
              using hindec
          obtain ⟨cut, hpositive, hcut⟩ := hfailure
          have hsep : ∀ a ∈ p.take cut.val, ∀ b ∈ p.drop cut.val, a < b := by
            intro a ha b hb
            obtain ⟨first, hfirst⟩ := List.mem_iff_get.mp ha
            obtain ⟨second, hsecond⟩ := List.mem_iff_get.mp hb
            simpa only [hfirst, hsecond] using hcut first second
          obtain ⟨hprefix, hsuffix, hrestore⟩ :=
            hsplit size p hperm cut.val (by omega) hsep
          obtain ⟨leftparts, hleftfull, _⟩ :=
            ih cut.val (by omega) (p.take cut.val) hprefix
          have hleftparts := And.intro hleftfull.1 hleftfull.2.1
          obtain ⟨rightparts, hrightfull, _⟩ :=
            ih (size - cut.val) (by omega) ((p.drop cut.val).map (· - cut.val)) hsuffix
          have hrightparts := And.intro hrightfull.1 hrightfull.2.1
          refine ⟨leftparts ++ rightparts, ?_, ?_⟩
          · rw [happend, hleftparts.1, hrightparts.1]
            simpa [List.length_take, Nat.min_eq_left (by omega : cut.val ≤ p.length)]
              using hrestore.symm
          · intro block hblock
            rcases List.mem_append.mp hblock with hleft | hright
            · exact hleftparts.2 block hleft
            · exact hrightparts.2 block hright
      obtain ⟨parts, hparts⟩ := hexists
      refine ⟨parts, ⟨hparts.1, hparts.2, ?_⟩, ?_⟩
      · have hc := hclosure parts hparts.2
        rwa [hparts.1, hsize] at hc
      intro other hotherfull
      have hother := And.intro hotherfull.1 hotherfull.2.1
      have hvalid (components : List (List ℕ))
          (hc : ∀ block ∈ components, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) :
          (assemble components).Perm (List.range' 1 (assemble components).length) :=
        hassembleperm components (fun block hb => (hc block hb).2.1)
      have hnonempty (block : List ℕ) (rest : List (List ℕ)) (hb : block ≠ []) :
          assemble (block :: rest) ≠ [] := by
        intro heq
        have hzero := congrArg List.length heq
        have hpositive := List.length_pos_iff_ne_nil.mpr hb
        simp only [assemble, directSum, shift, List.length_append, List.length_map,
          List.length_nil] at hzero
        omega
      cases parts with
      | nil =>
        cases other with
        | nil => rfl
        | cons block rest =>
          have hpempty : p = [] := by simpa [assemble] using hparts.1.symm
          exact False.elim
            (hnonempty block rest (hother.2 block (by simp)).1 (hother.1.trans hpempty))
      | cons first rest =>
        cases other with
        | nil =>
          have hpempty : p = [] := by simpa [assemble] using hother.1.symm
          exact False.elim
            (hnonempty first rest (hparts.2 first (by simp)).1 (hparts.1.trans hpempty))
        | cons second tail =>
          have hf := hparts.2 first (by simp)
          have hs := hother.2 second (by simp)
          have hr : ∀ block ∈ rest, block ≠ [] ∧
              block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block :=
            fun block hb => hparts.2 block (by simp [hb])
          have ht : ∀ block ∈ tail, block ≠ [] ∧
              block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block :=
            fun block hb => hother.2 block (by simp [hb])
          have hfirstle (block next : List ℕ) (suffix : List (List ℕ))
              (hb : block ≠ [] ∧ block.Perm (List.range' 1 block.length) ∧
                sumIndecomposable block)
              (hn : next ≠ [] ∧ next.Perm (List.range' 1 next.length) ∧
                sumIndecomposable next)
              (hsuf : ∀ component ∈ suffix, component ≠ [] ∧
                component.Perm (List.range' 1 component.length) ∧ sumIndecomposable component)
              (hsub : block.Sublist (assemble (next :: suffix))) :
              block.length ≤ next.length := by
            have hnextbound : ∀ value ∈ next, value ≤ next.length := by
              intro value hv
              have hm := hn.2.1.mem_iff.mp hv
              simp only [List.mem_range', Nat.one_mul] at hm
              obtain ⟨index, hi, heq⟩ := hm
              omega
            have hsufpos : ∀ value ∈ assemble suffix, 1 ≤ value := by
              intro value hv
              have hm := (hvalid suffix hsuf).mem_iff.mp hv
              simp only [List.mem_range', Nat.one_mul] at hm
              obtain ⟨index, hi, heq⟩ := hm
              omega
            have hsep : ∀ a ∈ next, ∀ b ∈ shift next.length (assemble suffix), a < b := by
              intro a ha b hb
              obtain ⟨value, hv, rfl⟩ := List.mem_map.mp hb
              have := hnextbound a ha
              have := hsufpos value hv
              omega
            rcases indecomposable_sublist_append block next (shift next.length (assemble suffix))
                hb.2.2 hsep hsub with hleft | hright
            · exact hleft.length_le
            · have hone : 1 ∈ block := by
                apply hb.2.1.mem_iff.mpr
                simp only [List.mem_range', Nat.one_mul]
                exact ⟨0, List.length_pos_iff_ne_nil.mpr hb.1, by omega⟩
              obtain ⟨value, hv, heq⟩ := List.mem_map.mp (hright.subset hone)
              have := hsufpos value hv
              have := List.length_pos_iff_ne_nil.mpr hn.1
              omega
          have hequal : assemble (first :: rest) = assemble (second :: tail) :=
            hparts.1.trans hother.1.symm
          have hfirstsub : first.Sublist (assemble (second :: tail)) := by
            rw [← hequal]
            exact List.sublist_append_left _ _
          have hsecondsub : second.Sublist (assemble (first :: rest)) := by
            rw [hequal]
            exact List.sublist_append_left _ _
          have hlength : first.length = second.length :=
            Nat.le_antisymm (hfirstle first second tail hf hs ht hfirstsub)
              (hfirstle second first rest hs hf hr hsecondsub)
          have hhead : first = second := by
            have htake := congrArg (List.take first.length) hequal
            simpa [assemble, directSum, hlength] using htake
          subst second
          have htailshift : shift first.length (assemble rest) =
              shift first.length (assemble tail) := List.append_cancel_left hequal
          have htail : assemble rest = assemble tail := by
            have hmapped := congrArg (List.map (· - first.length)) htailshift
            simpa [shift, List.map_map, Function.comp_def] using hmapped
          have htailperm := hvalid rest hr
          have hsmaller : (assemble rest).length < size := by
            have hsum := congrArg List.length hparts.1
            have hpositive := List.length_pos_iff_ne_nil.mpr hf.1
            simp only [assemble, directSum, shift, List.length_append, List.length_map] at hsum
            omega
          obtain ⟨canonical, _, hunique⟩ := ih (assemble rest).length hsmaller
            (assemble rest) htailperm
          have hrestid : rest = canonical := hunique rest ⟨rfl, hr, hclosure rest hr⟩
          have htailid : tail = canonical := hunique tail ⟨htail.symm, ht, by
            have hc := hclosure tail ht
            rwa [← htail] at hc⟩
          exact congrArg (first :: ·) (htailid.trans hrestid.symm)
  refine ⟨hdecomposition n p hperm, hclosure, ?_, ?_, ?_⟩
  · have hzero : avoiders 0 patterns = {[]} := by
      ext word
      constructor
      · intro hw
        have hlen := hw.1.length_eq
        simpa using List.eq_nil_of_length_eq_zero (by simpa using hlen)
      · intro hw
        have heq : word = [] := Set.mem_singleton_iff.mp hw
        subst word
        exact (hclosure [] (by simp)).mpr (by simp)
    rw [hzero, Set.ncard_singleton]
  · intro size
    let blocks (cut : Fin (size + 1)) : Set (List ℕ) :=
      {word | word ∈ avoiders (cut.val + 1) patterns ∧ sumIndecomposable word}
    let source := Σ cut : Fin (size + 1), blocks cut × avoiders (size - cut.val) patterns
    have hfinite (size : ℕ) : (avoiders size patterns).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro word hw
      exact List.mem_permutations.mpr hw.1
    let (cut : Fin (size + 1)) : Finite (blocks cut) :=
      ((hfinite (cut.val + 1)).subset (fun _ hw => hw.1)).to_subtype
    let (cut : Fin (size + 1)) : Finite (avoiders (size - cut.val) patterns) :=
      (hfinite _).to_subtype
    have hvalid (word : List ℕ) (size : ℕ) (hw : word ∈ avoiders size patterns) :
        word.length = size := by simpa using hw.1.length_eq
    have hparts (size : ℕ) (word : List ℕ) (hw : word ∈ avoiders size patterns) :
        ∃ parts, assemble parts = word ∧
          (∀ block ∈ parts, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) ∧
          ∀ block ∈ parts, block ∈ avoiders block.length patterns := by
      obtain ⟨parts, hp, _⟩ := hdecomposition size word hw.1
      exact ⟨parts, hp.1, hp.2.1, hp.2.2.mp hw⟩
    have hprepend (entry : source) (parts : List (List ℕ))
        (hp : assemble parts = entry.2.2.val)
        (hv : ∀ block ∈ parts, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) :
        ∀ block ∈ entry.2.1.val :: parts, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
      intro block hb
      rcases List.mem_cons.mp hb with rfl | htail
      · have hlen := hvalid _ _ entry.2.1.property.1
        exact ⟨List.length_pos_iff_ne_nil.mp (by omega),
          by simpa only [hlen] using entry.2.1.property.1.1, entry.2.1.property.2⟩
      · exact hv block htail
    let join (entry : source) : List ℕ :=
      directSum (entry.1.val + 1) entry.2.1.val entry.2.2.val
    have hjoin (entry : source) : join entry ∈ avoiders (size + 1) patterns := by
      obtain ⟨parts, hp, hv, hc⟩ := hparts _ _ entry.2.2.property
      have hlen := hvalid _ _ entry.2.1.property.1
      have htail := hvalid _ _ entry.2.2.property
      have heq : assemble (entry.2.1.val :: parts) = join entry := by
        simp only [assemble, hp, hlen, join]
      have hsize : (join entry).length = size + 1 := by
        dsimp [join, directSum, shift]
        simp only [List.length_append, List.length_map, hlen, htail]
        have := entry.1.isLt
        omega
      have ha := (hclosure (entry.2.1.val :: parts) (hprepend entry parts hp hv)).mpr
        (by
          intro block hb
          rcases List.mem_cons.mp hb with rfl | hrest
          · simpa only [hlen] using entry.2.1.property.1
          · exact hc block hrest)
      simpa only [heq, hsize] using ha
    let build (entry : source) : avoiders (size + 1) patterns := ⟨join entry, hjoin entry⟩
    have hinjective : Function.Injective build := by
      intro left right heq
      have hequal : join left = join right := congrArg Subtype.val heq
      obtain ⟨lp, hl, hlv, hlc⟩ := hparts _ _ left.2.2.property
      obtain ⟨rp, hr, hrv, hrc⟩ := hparts _ _ right.2.2.property
      have hleftlen := hvalid _ _ left.2.1.property.1
      have hrightlen := hvalid _ _ right.2.1.property.1
      have hleq : assemble (left.2.1.val :: lp) = join left := by
        simp only [assemble, hl, hleftlen, join]
      have hreq : assemble (right.2.1.val :: rp) = join left := by
        simpa only [assemble, hr, hrightlen, join] using hequal.symm
      obtain ⟨canonical, _, huniq⟩ := hdecomposition (size + 1) (join left) (hjoin left).1
      have hlcanon : left.2.1.val :: lp = canonical := huniq _
        ⟨hleq, hprepend left lp hl hlv, by
          have hc := hclosure (left.2.1.val :: lp) (hprepend left lp hl hlv)
          have hs := hvalid _ _ (hjoin left)
          simpa only [hleq, hs] using hc⟩
      have hrcanon : right.2.1.val :: rp = canonical := huniq _
        ⟨hreq, hprepend right rp hr hrv, by
          have hc := hclosure (right.2.1.val :: rp) (hprepend right rp hr hrv)
          have hs := hvalid _ _ (hjoin left)
          simpa only [hreq, hs] using hc⟩
      have hcons := List.cons.inj (hlcanon.trans hrcanon.symm)
      have hindex : left.1 = right.1 := by
        apply Fin.ext
        have hlength := congrArg List.length hcons.1
        omega
      have htail : left.2.2.val = right.2.2.val :=
        hl.symm.trans ((congrArg assemble hcons.2).trans hr)
      rcases left with ⟨li, lb, lt⟩
      rcases right with ⟨ri, rb, rt⟩
      dsimp at hindex hcons htail
      subst ri
      exact congrArg (Sigma.mk li) (Prod.ext (Subtype.ext hcons.1) (Subtype.ext htail))
    have hsurjective : Function.Surjective build := by
      intro word
      obtain ⟨parts, hp, hv, hc⟩ := hparts _ _ word.property
      cases parts with
      | nil =>
        have hlen := hvalid _ _ word.property
        have hempty : word.val = [] := by simpa [assemble] using hp.symm
        simp only [hempty, List.length_nil] at hlen
        omega
      | cons first rest =>
        have hf := hv first (by simp)
        have hfirst := hc first (by simp)
        have hrest : ∀ block ∈ rest, block ≠ [] ∧
            block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block :=
          fun block hb => hv block (by simp [hb])
        have hrestClass := (hclosure rest hrest).mpr
          (fun block hb => hc block (by simp [hb]))
        have hlen := hvalid _ _ word.property
        have hsum := congrArg List.length hp
        simp only [assemble, directSum, shift, List.length_append, List.length_map] at hsum
        have hpositive := List.length_pos_iff_ne_nil.mpr hf.1
        let cut : Fin (size + 1) := ⟨first.length - 1, by omega⟩
        have hcut : cut.val + 1 = first.length := by dsimp [cut]; omega
        have htail : (assemble rest).length = size - cut.val := by dsimp [cut]; omega
        let left : blocks cut := ⟨first, by
          exact ⟨by simpa only [hcut] using hfirst, hf.2.2⟩⟩
        let right : avoiders (size - cut.val) patterns := ⟨assemble rest, by
          simpa only [htail] using hrestClass⟩
        refine ⟨⟨cut, left, right⟩, Subtype.ext ?_⟩
        change directSum (cut.val + 1) first (assemble rest) = word.val
        simpa only [hcut, assemble] using hp
    refine ⟨?_, Equiv.ofBijective build ⟨hinjective, hsurjective⟩, fun _ => rfl⟩
    have hcard := Nat.card_congr (Equiv.ofBijective build ⟨hinjective, hsurjective⟩)
    rw [Nat.card_sigma] at hcard
    rw [← Nat.card_coe_set_eq, ← hcard]
    apply Finset.sum_congr rfl
    intro cut _
    rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  · dsimp only
    let sequences (size count : ℕ) : Set (List (List ℕ)) := {parts |
      (∀ block ∈ parts, block ≠ [] ∧ sumIndecomposable block ∧
        block ∈ avoiders block.length patterns) ∧
      (assemble parts).length = size ∧ parts.length = count}
    have hfinite (size : ℕ) : (avoiders size patterns).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro word hw
      exact List.mem_permutations.mpr hw.1
    have hgood (size count : ℕ) (parts : sequences size count) :
        ∀ block ∈ parts.val, block ≠ [] ∧
          block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block := by
      intro block hb
      have hp := parts.property.1 block hb
      exact ⟨hp.1, hp.2.2.1, hp.2.1⟩
    have hmember (size count : ℕ) (parts : sequences size count) :
        assemble parts.val ∈ avoiders size patterns := by
      have ha := (hclosure parts.val (hgood size count parts)).mpr
        (fun block hb => (parts.property.1 block hb).2.2)
      simpa only [parts.property.2.1] using ha
    have hsequencesFinite (size count : ℕ) : Finite (sequences size count) := by
      let : Finite (avoiders size patterns) := (hfinite size).to_subtype
      let serialize (parts : sequences size count) : avoiders size patterns :=
        ⟨assemble parts.val, hmember size count parts⟩
      apply Finite.of_injective serialize
      intro left right heq
      have hv : assemble left.val = assemble right.val := congrArg Subtype.val heq
      obtain ⟨canonical, _, hu⟩ :=
        hdecomposition size (assemble left.val) (hmember size count left).1
      have hl : left.val = canonical := hu _ ⟨rfl, hgood size count left, by
        simpa only [left.property.2.1] using hclosure left.val (hgood size count left)⟩
      have hr : right.val = canonical := hu _ ⟨hv.symm, hgood size count right, by
        simpa only [← hv, left.property.2.1] using
          hclosure right.val (hgood size count right)⟩
      exact Subtype.ext (hl.trans hr.symm)
    refine ⟨?_, ?_⟩
    · intro size
      change (sequences size 0).ncard = if size = 0 then 1 else 0
      have heq : sequences size 0 = {parts | parts = [] ∧ size = 0} := by
        ext parts
        constructor
        · intro hp
          have hn : parts = [] := List.eq_nil_of_length_eq_zero hp.2.2
          exact ⟨hn, by simpa only [hn, assemble, List.length_nil] using hp.2.1.symm⟩
        · rintro ⟨rfl, rfl⟩
          simp [sequences, assemble]
      rw [heq]
      by_cases hz : size = 0
      · have hsingleton : {parts : List (List ℕ) | parts = []} = {[]} := by
          ext parts
          simp
        simp only [hz, and_true, ite_true]
        rw [hsingleton, Set.ncard_singleton]
      · simp only [hz, and_false, Set.ofPred_false, Set.ncard_empty, ite_false]
    intro size count
    let blocks (cut : Fin (size + 1)) : Set (List ℕ) :=
      {word | word ∈ avoiders (cut.val + 1) patterns ∧ sumIndecomposable word}
    let source := Σ cut : Fin (size + 1), blocks cut × sequences (size - cut.val) count
    let (cut : Fin (size + 1)) : Finite (blocks cut) :=
      ((hfinite (cut.val + 1)).subset (fun _ hw => hw.1)).to_subtype
    let (cut : Fin (size + 1)) : Finite (sequences (size - cut.val) count) :=
      hsequencesFinite _ _
    let join (entry : source) : List (List ℕ) := entry.2.1.val :: entry.2.2.val
    have hjoin (entry : source) : join entry ∈ sequences (size + 1) (count + 1) := by
      have hlen : entry.2.1.val.length = entry.1.val + 1 := by
        simpa using entry.2.1.property.1.1.length_eq
      refine ⟨?_, ?_, ?_⟩
      · intro block hb
        rcases List.mem_cons.mp hb with rfl | htail
        · exact ⟨List.length_pos_iff_ne_nil.mp (by omega), entry.2.1.property.2,
            by simpa only [hlen] using entry.2.1.property.1⟩
        · exact entry.2.2.property.1 block htail
      · change (assemble (entry.2.1.val :: entry.2.2.val)).length = size + 1
        simp only [assemble, directSum, shift, List.length_append, List.length_map,
          hlen, entry.2.2.property.2.1]
        have := entry.1.isLt
        omega
      · change (entry.2.1.val :: entry.2.2.val).length = count + 1
        simpa only [List.length_cons] using congrArg (· + 1) entry.2.2.property.2.2
    let build (entry : source) : sequences (size + 1) (count + 1) :=
      ⟨join entry, hjoin entry⟩
    have hinjective : Function.Injective build := by
      intro left right heq
      have hc := List.cons.inj (congrArg Subtype.val heq)
      have hl : left.2.1.val.length = left.1.val + 1 := by
        simpa using left.2.1.property.1.1.length_eq
      have hr : right.2.1.val.length = right.1.val + 1 := by
        simpa using right.2.1.property.1.1.length_eq
      have hi : left.1 = right.1 := by
        apply Fin.ext
        have := congrArg List.length hc.1
        omega
      rcases left with ⟨lp, lb, lt⟩
      rcases right with ⟨rp, rb, rt⟩
      dsimp only at hi hc
      subst rp
      exact congrArg (Sigma.mk lp) (Prod.ext (Subtype.ext hc.1) (Subtype.ext hc.2))
    have hsurjective : Function.Surjective build := by
      intro parts
      cases heq : parts.val with
      | nil =>
        have hcount := parts.property.2.2
        simp only [heq, List.length_nil] at hcount
        omega
      | cons first rest =>
        have hv := parts.property.1
        have hlen := parts.property.2.1
        have hcount := parts.property.2.2
        rw [heq] at hv hlen hcount
        have hf := hv first (by simp)
        have hpositive := List.length_pos_iff_ne_nil.mpr hf.1
        simp only [assemble, directSum, shift, List.length_append, List.length_map] at hlen
        let cut : Fin (size + 1) := ⟨first.length - 1, by omega⟩
        have hcut : cut.val + 1 = first.length := by dsimp only [cut]; omega
        let left : blocks cut := ⟨first, by
          change first ∈ avoiders (cut.val + 1) patterns ∧ sumIndecomposable first
          simpa only [hcut] using And.intro hf.2.2 hf.2.1⟩
        let right : sequences (size - cut.val) count := ⟨rest,
          fun block hb => hv block (by simp [hb]), by dsimp only [cut]; omega,
          by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hcount⟩
        exact ⟨⟨cut, left, right⟩, Subtype.ext heq.symm⟩
    let decomposition := Equiv.ofBijective build ⟨hinjective, hsurjective⟩
    refine ⟨?_, decomposition, fun _ => rfl, ?_⟩
    · have hcard := Nat.card_congr decomposition
      rw [Nat.card_sigma] at hcard
      rw [← Nat.card_coe_set_eq, ← hcard]
      apply Finset.sum_congr rfl
      intro cut _
      rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    · intro weight
      let (cut : Fin (size + 1)) : Fintype (blocks cut) := Fintype.ofFinite _
      let (cut : Fin (size + 1)) : Fintype (sequences (size - cut.val) count) :=
        Fintype.ofFinite _
      rw [← finsum_comp_equiv decomposition]
      change (∑ᶠ entry : Σ cut : Fin (size + 1),
        blocks cut × sequences (size - cut.val) count,
        weight (entry.2.1.val :: entry.2.2.val)) = _
      simp only [finsum_eq_sum_of_fintype, Fintype.sum_sigma, Fintype.sum_prod_type]
      simp only [← finsum_eq_sum_of_fintype]
      rfl

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponents
