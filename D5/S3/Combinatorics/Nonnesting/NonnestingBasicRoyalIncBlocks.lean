/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks
   mirror-E: none(waiver:royal-increasing-block-classification)
   anchors: []
   utility: none
   digest: Classifies triple-avoiding permutations by increasing skew blocks. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncBlocks

open NonnestingBasicRoyalBlocks

def incBlocks : ℕ → List ℕ → List ℕ
  | _, [] => []
  | n, k :: ks => List.range' (n - k + 1) k ++ incBlocks (n - k) ks
theorem avoids_has_inc_blocks (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n))
    (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
    (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p) :
    ∃ ks : List ℕ, (∀ k ∈ ks, 0 < k) ∧ ks.sum = n ∧ p = incBlocks n ks := by
  classical
  have avoids_iff_skew_cuts (p : List ℕ) (hp : p.Nodup) :
      (¬ NonnestingDefs.Occurs [1, 3, 2] p ∧
        ¬ NonnestingDefs.Occurs [2, 1, 3] p) ↔
      ∀ t i k (ht : t + 1 < p.length) (hi : i ≤ t)
        (_hk : t < k) (hklen : k < p.length),
        p[t + 1] < p[t] → p[k] < p[i] := by
    constructor
    · rintro ⟨h132, h213⟩ t i k ht hi hk hklen hdesc
      exact descent_separates p hp h132 h213 t i k ht hdesc hi hk hklen
    · intro hcut
      have descent_between (a b : ℕ) (ha : a < p.length)
          (hb : b < p.length) (hab : a < b) (hval : p[b] < p[a]) :
          ∃ t, ∃ ht : t + 1 < p.length,
            a ≤ t ∧ t + 1 ≤ b ∧ p[t + 1] < p[t] := by
        by_contra hnone
        have hsteps : ∀ t (ht : t + 1 < p.length) (hat : a ≤ t) (htb : t < b),
            p[t] ≤ p[t + 1] := by
          intro t ht hat htb
          by_contra hstep
          have hdesc : p[t + 1] < p[t] := by omega
          exact hnone ⟨t, ht, hat, by omega, hdesc⟩
        have hfinal : p[a] ≤ p[b] := by
          let value (index : ℕ) : ℕ := p[min index b]!; have steps (index : ℕ) (lower : a ≤ index) :
              value index ≤ value (index + 1) := by
            by_cases upper : index < b
            · have step := hsteps index (by omega) lower upper
              simpa [value, Nat.min_eq_left (by omega : index ≤ b),
                Nat.min_eq_left (by omega : index + 1 ≤ b),
                List.getElem!_eq_getElem?_getD,
                List.getElem?_eq_getElem (by omega : index < p.length),
                List.getElem?_eq_getElem (by omega : index + 1 < p.length)] using step
            · simp [value, Nat.min_eq_right (by omega : b ≤ index),
                Nat.min_eq_right (by omega : b ≤ index + 1)]
          have bound := Nat.rel_of_forall_rel_succ_of_le_of_lt
            (· ≤ ·) steps (b := a) (c := b) (by rfl) hab
          simpa [value, Nat.min_eq_left (by omega : a ≤ b),
            List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] using bound
        omega
      constructor
      · intro hocc
        obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
        change List.Sublist [x 1, x 3, x 2] p at hsub
        obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
        have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
        have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
        have hi : i < p.length := (f 0).isLt; have hj : j < p.length := (f 1).isLt
        have hk : k < p.length := (f 2).isLt
        have hv0 : p[i] = x 1 := by simpa [i] using (hf (0 : Fin 3)).symm
        have hv1 : p[j] = x 3 := by simpa [j] using (hf (1 : Fin 3)).symm
        have hv2 : p[k] = x 2 := by simpa [k] using (hf (2 : Fin 3)).symm
        have hik : p[i] < p[k] := by
          rw [hv0, hv2]; exact hxlt 1 (by omega) (by decide)
        have hkj : p[k] < p[j] := by
          rw [hv2, hv1]; exact hxlt 2 (by omega) (by decide)
        obtain ⟨t, htt, hjt, htk, hdesc⟩ := descent_between j k hj hk hjk hkj
        have hsep := hcut t i k htt (by omega) (by omega) hk hdesc; omega
      · intro hocc
        obtain ⟨x, hxlt, _, hsub, _⟩ := hocc
        change List.Sublist [x 2, x 1, x 3] p at hsub
        obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        let i := (f 0).val; let j := (f 1).val; let k := (f 2).val
        have hij : i < j := f.strictMono (show (0 : Fin 3) < 1 by decide)
        have hjk : j < k := f.strictMono (show (1 : Fin 3) < 2 by decide)
        have hi : i < p.length := (f 0).isLt; have hj : j < p.length := (f 1).isLt
        have hk : k < p.length := (f 2).isLt
        have hv0 : p[i] = x 2 := by simpa [i] using (hf (0 : Fin 3)).symm
        have hv1 : p[j] = x 1 := by simpa [j] using (hf (1 : Fin 3)).symm
        have hv2 : p[k] = x 3 := by simpa [k] using (hf (2 : Fin 3)).symm
        have hji : p[j] < p[i] := by
          rw [hv1, hv0]; exact hxlt 1 (by omega) (by decide)
        have hik : p[i] < p[k] := by
          rw [hv0, hv2]; exact hxlt 2 (by omega) (by decide)
        obtain ⟨t, htt, hit, htj, hdesc⟩ := descent_between i j hi hj hij hji
        have hsep := hcut t i k htt hit (by omega) hk hdesc; omega
  have adjacent_ascent_no_intermediate (p : List ℕ) (hp : p.Nodup)
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
      (t : ℕ) (ht : t + 1 < p.length)
      (z : ℕ) (hz : z ∈ p) (hl : p[t] < z) (hr : z < p[t + 1]) : False := by
    have hcut := (avoids_iff_skew_cuts p hp).mp ⟨h132, h213⟩
    have descent_between (a b : ℕ) (ha : a < p.length)
        (hb : b < p.length) (hab : a < b) (hval : p[b] < p[a]) :
        ∃ s, ∃ hs : s + 1 < p.length,
          a ≤ s ∧ s + 1 ≤ b ∧ p[s + 1] < p[s] := by
      by_contra hnone
      have hsteps : ∀ s (hs : s + 1 < p.length) (has : a ≤ s) (hsb : s < b),
          p[s] ≤ p[s + 1] := by
        intro s hs has hsb
        by_contra hstep
        exact hnone ⟨s, hs, has, by omega, by omega⟩
      have hfinal : p[a] ≤ p[b] := by
        let value (index : ℕ) : ℕ := p[min index b]!; have steps (index : ℕ) (lower : a ≤ index) :
            value index ≤ value (index + 1) := by
          by_cases upper : index < b
          · have step := hsteps index (by omega) lower upper
            simpa [value, Nat.min_eq_left (by omega : index ≤ b),
              Nat.min_eq_left (by omega : index + 1 ≤ b),
              List.getElem!_eq_getElem?_getD,
              List.getElem?_eq_getElem (by omega : index < p.length),
              List.getElem?_eq_getElem (by omega : index + 1 < p.length)] using step
          · simp [value, Nat.min_eq_right (by omega : b ≤ index),
              Nat.min_eq_right (by omega : b ≤ index + 1)]
        have bound := Nat.rel_of_forall_rel_succ_of_le_of_lt
          (· ≤ ·) steps (b := a) (c := b) (by rfl) hab
        simpa [value, Nat.min_eq_left (by omega : a ≤ b),
          List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] using bound
      omega
    let i := p.idxOf z; have hi : i < p.length := List.idxOf_lt_length_of_mem hz
    have hzi : p[i] = z := by
      exact (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hz)).2
    have ht0 : t < p.length := by omega
    by_cases hit : i < t
    · obtain ⟨s, hs, his, hst, hdesc⟩ :=
        descent_between i t hi ht0 hit (by rw [hzi]; omega)
      have hsep := hcut s i (t + 1) hs his (by omega) ht hdesc; rw [hzi] at hsep; omega
    · have hti : t + 1 < i := by
        have hit' : i ≠ t := by
          intro heq
          have hz' : p[t] = z := by simpa [heq] using hzi
          omega
        have hsi : i ≠ t + 1 := by
          intro heq
          have hz' : p[t + 1] = z := by simpa [heq] using hzi
          omega
        omega
      obtain ⟨s, hs, hts, hsi, hdesc⟩ :=
        descent_between (t + 1) i ht hi hti (by rw [hzi]; omega)
      have hsep := hcut s t i hs (by omega) (by omega) hi hdesc; rw [hzi] at hsep; omega
  have ascent_run_is_interval (n : ℕ) (p : List ℕ)
      (hp : p.Perm (List.range' 1 n))
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
      (a b : ℕ) (hb : b < p.length)
      (hrun : ∀ j (hj : j + 1 < p.length), a ≤ j → j < b →
        p[j] < p[j + 1]) :
      ∀ d (hd : a + d ≤ b),
        p[a + d]'(by omega) = p[a]'(by omega) + d := by
    have hnodup : p.Nodup := (hp.nodup_iff).mpr List.nodup_range'
    have hnext (j : ℕ) (hj : j + 1 < p.length)
        (hinc : p[j] < p[j + 1]) : p[j + 1] = p[j] + 1 := by
      by_contra hne
      have hgap : p[j] + 1 < p[j + 1] := by omega
      have hupper : p[j + 1] < 1 + n :=
        (List.mem_range'_1.mp (hp.subset (List.getElem_mem hj))).2
      have hzrange : p[j] + 1 ∈ List.range' 1 n :=
        List.mem_range'_1.mpr ⟨by omega, by omega⟩
      have hz : p[j] + 1 ∈ p := hp.symm.subset hzrange
      exact adjacent_ascent_no_intermediate p hnodup h132 h213 j hj
        (p[j] + 1) hz (by omega) hgap
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hbd; have hprev := ih (by omega : a + d ≤ b)
      have hstep : p[a + d + 1] = p[a + d] + 1 :=
        hnext (a + d) (by omega) (hrun (a + d) (by omega) (by omega) (by omega))
      calc
        p[a + (d + 1)] = p[a + d + 1] := by simp [Nat.add_assoc]
        _ = p[a + d] + 1 := hstep
        _ = p[a] + (d + 1) := by rw [hprev]; omega
  have first_descent_prefix_values (n : ℕ) (p : List ℕ)
      (hp : p.Perm (List.range' 1 n))
      (h132 : ¬ NonnestingDefs.Occurs [1, 3, 2] p)
      (h213 : ¬ NonnestingDefs.Occurs [2, 1, 3] p)
      (t : ℕ) (ht : t + 1 < p.length) (hdesc : p[t + 1] < p[t])
      (hrun : ∀ j (hj : j + 1 < p.length), j < t → p[j] < p[j + 1]) :
      ∀ i (hi : i ≤ t), p[i]'(by omega) + t = n + i := by
    have hnodup : p.Nodup := (hp.nodup_iff).mpr List.nodup_range'
    have hcut := (avoids_iff_skew_cuts p hnodup).mp ⟨h132, h213⟩
    have hrun' : ∀ j (hj : j + 1 < p.length), 0 ≤ j → j < t →
        p[j] < p[j + 1] := by
      intro j hj _ hjt; exact hrun j hj hjt
    have hinterval := ascent_run_is_interval n p hp h132 h213 0 t
      (by omega) hrun'
    have hlast : p[t] = p[0] + t := by
      simpa using hinterval t (by omega)
    have hnpos : 0 < n := by
      have hlen := hp.length_eq; simp only [List.length_range'] at hlen; omega
    have hnmem : n ∈ p := hp.symm.subset
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    let r := p.idxOf n; have hr : r < p.length := List.idxOf_lt_length_of_mem hnmem
    have hrv : p[r] = n :=
      (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hnmem)).2
    have hlastle : p[t] < 1 + n :=
      (List.mem_range'_1.mp (hp.subset (List.getElem_mem (by omega : t < p.length)))).2
    have hmax : p[t] = n := by
      by_cases hrt : r ≤ t
      · have hrv' : p[r] = p[0] + r := by
          simpa using hinterval r (by simpa using hrt)
        omega
      · have hsep := hcut t 0 r ht (by omega) (by omega) hr hdesc
        have h0upper : p[0] < 1 + n :=
          (List.mem_range'_1.mp
            (hp.subset (List.getElem_mem (by omega : 0 < p.length)))).2
        omega
    intro i hi
    have hival : p[i] = p[0] + i := by
      simpa using hinterval i (by simpa using hi)
    omega
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    have hlen : p.length = n := by simpa using hp.length_eq
    have hnodup : p.Nodup := (hp.nodup_iff).mpr List.nodup_range'
    by_cases hn : n = 0
    · have hpnil : p = [] := List.eq_nil_of_length_eq_zero (by
        simpa [hn] using hlen)
      exact ⟨[], by simp, by simp [hn], by simp [hpnil, incBlocks]⟩
    · have hnpos : 0 < n := by omega
      by_cases hdes : ∃ t, ∃ ht : t + 1 < p.length, p[t + 1] < p[t]
      · let t := Nat.find hdes
        obtain ⟨ht, hdesc⟩ := Nat.find_spec hdes
        have hrun : ∀ j (hj : j + 1 < p.length), j < t → p[j] < p[j + 1] := by
          intro j hj hjt; have hnot : ¬ (∃ hj : j + 1 < p.length, p[j + 1] < p[j]) :=
            Nat.find_min hdes hjt
          have hne : p[j] ≠ p[j + 1] := by
            intro heq
            have := (hnodup.getElem_inj_iff
              (hi := (by omega : j < p.length)) (hj := hj)).mp heq
            omega
          by_contra hnotinc
          have hdesc' : p[j + 1] < p[j] := by omega
          exact hnot ⟨hj, hdesc'⟩
        have hprefix := first_descent_prefix_values n p hp h132 h213 t ht hdesc hrun
        have hprefixList : p.take (t + 1) = List.range' (n - t) (t + 1) := by
          apply List.ext_getElem
          · simp [List.length_take, hlen, Nat.min_eq_left (by omega : t + 1 ≤ n)]
          · intro i hi1 hi2
            have hpi := hprefix i (by
              simp only [List.length_take] at hi1
              omega)
            simp only [List.getElem_take, List.getElem_range']; omega
        have htn : t < n := by omega
        have hsuffix : (p.drop (t + 1)).Perm
            (List.range' 1 (n - t - 1)) := by
          have hsubset : List.range' 1 (n - t - 1) ⊆ p.drop (t + 1) := by
            intro a ha
            have harange : 1 ≤ a ∧ a < n - t := by
              have h := List.mem_range'_1.mp ha; omega
            have hap : a ∈ p := hp.symm.subset
              (List.mem_range'_1.mpr ⟨harange.1, by omega⟩)
            let r := p.idxOf a; have hr : r < p.length := List.idxOf_lt_length_of_mem hap
            have hrv : p[r] = a :=
              (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hap)).2
            have htr : t < r := by
              by_contra hnot
              have hpre := hprefix r (by omega : r ≤ t); rw [hrv] at hpre; omega
            apply List.mem_iff_getElem.mpr
            have hindex : r - (t + 1) < (p.drop (t + 1)).length := by
              simp only [List.length_drop]; omega
            refine ⟨r - (t + 1), hindex, ?_⟩
            rw [List.getElem_drop]
            have heq : t + 1 + (r - (t + 1)) = r := by omega
            simpa only [heq] using hrv
          have hsubperm := List.subperm_of_subset List.nodup_range' hsubset
          obtain ⟨q', hqperm, hqsub⟩ := List.subperm_iff.mp hsubperm
          have hqlen : q'.length = (List.range' 1 (n - t - 1)).length := by
            have hqdrop := hqperm.length_eq
            simp only [List.length_drop, List.length_range'] at hqdrop ⊢; omega
          have hq : List.range' 1 (n - t - 1) = q' :=
            hqsub.eq_of_length hqlen.symm
          simpa only [hq] using hqperm.symm
        let q := p.drop (t + 1); have hqavoid (σ : List ℕ) (hσ : ¬ NonnestingDefs.Occurs σ p) :
            ¬ NonnestingDefs.Occurs σ q := by
          intro hocc
          obtain ⟨x, hxlt, hxmem, hxsub, _⟩ := hocc
          apply hσ
          refine ⟨x, hxlt, ?_, ?_, by simp⟩
          · intro i hi hik
            exact List.mem_of_mem_drop (hxmem i hi hik)
          · exact hxsub.trans (List.drop_sublist _ _)
        have hsmall : n - t - 1 < n := by omega
        obtain ⟨ks, hpos, hsum, hform⟩ :=
          ih (n - t - 1) hsmall q hsuffix (hqavoid _ h132) (hqavoid _ h213)
        refine ⟨(t + 1) :: ks, ?_, ?_, ?_⟩
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · omega
          · exact hpos k hk
        · simp only [List.sum_cons]
          omega
        · have hsplit : p = p.take (t + 1) ++ q := by
            exact (List.take_append_drop (t + 1) p).symm
          rw [hsplit, hprefixList, hform]
          have hrem : n - t - 1 = n - (t + 1) := by omega
          simp [incBlocks, hrem]; omega
      · have hrun : ∀ j (hj : j + 1 < p.length), 0 ≤ j → j < n - 1 →
            p[j] < p[j + 1] := by
          intro j hj _ _
          have hne : p[j] ≠ p[j + 1] := by
            intro heq
            have := (hnodup.getElem_inj_iff
              (hi := (by omega : j < p.length)) (hj := hj)).mp heq
            omega
          by_contra hnot
          exact hdes ⟨j, hj, by omega⟩
        have hinterval := ascent_run_is_interval n p hp h132 h213 0 (n - 1)
          (by omega) hrun
        have hlast : p[n - 1] = p[0] + (n - 1) := by
          simpa using hinterval (n - 1) (by omega)
        have hlastupper : p[n - 1] < 1 + n :=
          (List.mem_range'_1.mp
            (hp.subset (List.getElem_mem (by omega : n - 1 < p.length)))).2
        have hfirstlower : 1 ≤ p[0] :=
          (List.mem_range'_1.mp
            (hp.subset (List.getElem_mem (by omega : 0 < p.length)))).1
        have hfirst : p[0] = 1 := by omega
        have hpeq : p = List.range' 1 n := by
          apply List.ext_getElem
          · simpa using hlen
          · intro i hi1 hi2
            have hpi := hinterval i (by omega : 0 + i ≤ n - 1)
            simp only [Nat.zero_add] at hpi; simp only [List.getElem_range']; omega
        refine ⟨[n], ?_, by simp, ?_⟩
        · intro k hk
          simp only [List.mem_singleton] at hk; subst k; exact hnpos
        · simpa [incBlocks] using hpeq
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncBlocks

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalIncBlocks.avoids_has_inc_blocks
