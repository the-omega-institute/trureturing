/- GID: D5/S3/Combinatorics/Circle/SparseNecklaceRounding/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SparseNecklaceRounding/Endpoint
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Uniform physical sparse-necklace rounding with at most p-1 strict corners. -/
import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.PhysicalStreams

/-! The complete physical rounding theorem and its fractional-path proof. -/
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.SparseNecklaceRounding
open SourceWidth RunFirstEarTransport
open scoped BigOperators
open private
  gap_list_length
  gap_list_sum
  gap_list_mem
  bits_fin_sum
  gap_prefix_sum
  bits_seed
  chain_start_drop
  chain_start_step
  chain_cut
  necklace_endpoints
  necklace_chain_coordinates
  indexed_intervals
  chain_gap_lower
  raw_inventory
  filterMap_label_values
  terminal_value_stream
  physical_inventory
  positive_coordinates
  terminal_coordinates
  threshold_step
  threshold_last
  threshold_strict
  threshold_blocks_inventory
  threshold_blocks_split_count
  threshold_blocks_strict_provenance
  threshold_blocks_final_not_split
  threshold_antitone
  threshold_spacing
  int_list_cast
  terminal_projection
  necklace_physical_totals
  terminal_mass_sum
  total_positive_mass
  threshold_terminal_length
  threshold_terminal_spacing
  threshold_terminal_positive
  necklace_blocks_inventory
  threshold_terminal_last
  necklace_split_bound
  necklace_split_provenance
  physicalCharge
  physical_charge_nonneg
  from D5.S3.Combinatorics.Circle.SparseNecklaceRounding.PhysicalStreams

private def positiveChain {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) : List (Fin (period gaps)) :=
  (List.range (chainGap gaps r - 1)).filterMap
    (fun t => labelAt (period gaps) (chainStart gaps r + t))

private theorem positive_chain_order {p : ℕ} (gaps : Fin p → ℕ) :
    positiveLabels gaps = (List.range p).reverse.flatMap (positiveChain gaps) := by
  simp only [positiveLabels,positiveIndices,List.filterMap_flatMap,List.filterMap_map]
  rfl

private theorem label_projection {β : Type*} (k : ℕ) (rs : List ℕ) (idx : ℕ → ℕ)
    (f : Fin k → β) (v : ℕ → β)
    (hv : ∀ r ∈ rs, ∃ hi : idx r < k, f ⟨idx r,hi⟩ = v r) :
    ((rs.filterMap (fun r => labelAt k (idx r))).map f) = rs.map v := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨hi,hf⟩ := hv r (by simp)
    have ht : ∀ s ∈ rs, ∃ hi : idx s < k, f ⟨idx s,hi⟩ = v s :=
      fun s hs => hv s (by simp [hs])
    simpa [labelAt,hi,hf] using congrArg (List.cons (v r)) (ih ht)

private theorem geometric_list (n : ℕ) (h : ℤ) :
    ((List.range n).map (fun t => (2 : ℤ)^t * h)).sum = ((2 : ℤ)^n - 1) * h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih]
    simp only [List.map_singleton,List.sum_singleton,pow_succ]
    ring

private theorem chain_mass_charge {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) :
    ((positiveChain gaps r).map (actualSource (period gaps) (necklaceSeed gaps))).sum =
      demand gaps r + cyclicHead gaps (r + 1) - cyclicHead gaps r ∧
    ((positiveChain gaps r).map (physicalCharge gaps)).sum + terminalCharge gaps r =
      winding gaps (r + 1) - winding gaps r := by
  rcases necklace_chain_coordinates gaps hg r hr with
    ⟨hk,hep,heb,hhp,hhb,hhp',hhb',hho,hho',hz0,hzh,hz'p,hz'h,hz'o,
      hstep,hzstep,hw,hn,htau,hnb,hnh,htaup,htaub,hP,hC,hdir,hpeak,hfresh,hpos,hneg⟩
  have hm := label_projection (period gaps) (List.range (chainGap gaps r - 1))
    (fun t => chainStart gaps r + t) (actualSource (period gaps) (necklaceSeed gaps))
    (fun t => (2 : ℤ)^t * cyclicHead gaps r) (by
      intro t ht
      obtain ⟨hi,hmp,hmb,hcp,hcb,hf,hg⟩ := hpos t (by have := List.mem_range.mp ht; omega)
      exact ⟨hi,hf⟩)
  have hc := label_projection (period gaps) (List.range (chainGap gaps r - 1))
    (fun t => chainStart gaps r + t) (physicalCharge gaps)
    (fun t => (2 : ℤ)^t * winding gaps r) (by
      intro t ht
      obtain ⟨hi,hmp,hmb,hcp,hcb,hf,hg⟩ := hpos t (by have := List.mem_range.mp ht; omega)
      refine ⟨hi,?_⟩
      dsimp only [physicalCharge]
      rw [hf,hg]
      ring)
  constructor
  · rw [positiveChain,hm,geometric_list]
    exact hP
  · rw [positiveChain,hc,geometric_list]
    exact hC

private theorem chain_suffix_totals {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r ≤ p) :
    ((((List.range p).drop r).flatMap (positiveChain gaps)).map
      (actualSource (period gaps) (necklaceSeed gaps))).sum =
        threshold gaps r + (necklaceSeed gaps : ℤ) - cyclicHead gaps r ∧
    ((((List.range p).drop r).flatMap (positiveChain gaps)).map
      (physicalCharge gaps)).sum +
      (((List.range p).drop r).map (terminalCharge gaps)).sum =
        (necklaceSeed gaps : ℤ) - winding gaps r := by
  by_cases he : r = p
  · subst r
    obtain ⟨h0,hp,z0,zp,s0,sp⟩ := necklace_endpoints gaps
    have hd : (List.range p).drop p = [] := by simp
    rw [hd]
    simp [hp,zp,threshold_last]
  · have hrp : r < p := by omega
    have ih := chain_suffix_totals gaps hg (r + 1) (by omega)
    have hi : r < (List.range p).length := by simpa using hrp
    rw [List.drop_eq_getElem_cons hi,List.getElem_range hi]
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    obtain ⟨hm,hc⟩ := chain_mass_charge gaps hg r hrp
    rw [hm,threshold_step gaps r hrp]
    constructor <;> linarith [ih.1,ih.2]
termination_by p - r


private def shiftCorner {k : ℕ} (d : ℕ) (c : CornerRecord k) : CornerRecord k :=
  { c with prefixLength := c.prefixLength + d }

private def blockCorners {k : ℕ} : List (RoundBlock (Fin k)) → List (CornerRecord k)
  | [] => []
  | .one _ :: bs => (blockCorners bs).map (shiftCorner 1)
  | .cut i j _ :: bs => ⟨2,i,j⟩ :: (blockCorners bs).map (shiftCorner 2)

private theorem block_corner_projections {k : ℕ} (bs : List (RoundBlock (Fin k))) :
    (blockCorners bs).map CornerRecord.prefixLength =
      (cornerPositions bs).map (fun n => n + 1) ∧
    (blockCorners bs).map (fun c => (c.positive,c.terminal)) = splitPairs bs ∧
    (blockCorners bs).length = (splitPairs bs).length := by
  induction bs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons b bs ih =>
    cases b with
    | one i =>
      refine ⟨?_,?_,?_⟩
      · have hs := congrArg (List.map (fun n : ℕ => n + 1)) ih.1
        simpa only [blockCorners,cornerPositions,List.map_map,Function.comp_def,shiftCorner] using hs
      · simpa only [blockCorners,splitPairs,List.map_map,Function.comp_def,shiftCorner] using ih.2.1
      · simpa only [blockCorners,splitPairs,List.length_map] using ih.2.2
    | cut i j t =>
      refine ⟨?_,?_,?_⟩
      · have hs := congrArg (List.map (fun n : ℕ => n + 2)) ih.1
        simp only [blockCorners,cornerPositions,List.map_cons,List.map_map,Function.comp_def,shiftCorner]
        congr 1
        simpa only [List.map_map,Function.comp_def,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs
      · simpa only [blockCorners,splitPairs,List.map_cons,List.map_map,Function.comp_def,shiftCorner]
          using congrArg (List.cons (i,j)) ih.2.1
      · simpa only [blockCorners,splitPairs,List.length_cons,List.length_map] using congrArg Nat.succ ih.2.2

private theorem block_corner_locations {k : ℕ} (bs : List (RoundBlock (Fin k))) :
    ∀ c ∈ blockCorners bs, ∃ u v u' v' : List (Fin k),
      plusWord bs = u ++ [c.positive,c.terminal] ++ v ∧
      minusWord bs = u' ++ [c.terminal,c.positive] ++ v' ∧
      c.prefixLength = u.length + 2 ∧ c.prefixLength = u'.length + 2 := by
  induction bs with
  | nil => simp [blockCorners]
  | cons b bs ih =>
    cases b with
    | one i =>
      intro c hc
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      obtain ⟨u,v,u',v',hwp,hwm,hu,hu'⟩ := ih d hd
      refine ⟨i::u,v,i::u',v',?_,?_,?_,?_⟩
      · simpa only [plusWord,shiftCorner,List.cons_append] using congrArg (List.cons i) hwp
      · simpa only [minusWord,shiftCorner,List.cons_append] using congrArg (List.cons i) hwm
      · dsimp only [shiftCorner]; simp only [List.length_cons]; omega
      · dsimp only [shiftCorner]; simp only [List.length_cons]; omega
    | cut i j t =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨[],plusWord bs,[],minusWord bs,rfl,rfl,rfl,rfl⟩
      · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
        obtain ⟨u,v,u',v',hwp,hwm,hu,hu'⟩ := ih d hd
        refine ⟨i::j::u,v,j::i::u',v',?_,?_,?_,?_⟩
        · simpa only [plusWord,shiftCorner,List.cons_append] using congrArg (fun w => i::j::w) hwp
        · simpa only [minusWord,shiftCorner,List.cons_append] using congrArg (fun w => j::i::w) hwm
        · dsimp only [shiftCorner]; simp only [List.length_cons]; omega
        · dsimp only [shiftCorner]; simp only [List.length_cons]; omega

private theorem int_prefix_cast {α : Type*} (f : α → ℤ) (w : List α) (n : ℕ) :
    prefixSum (fun i => (f i : ℚ)) w n = (((w.take n).map f).sum : ℤ) := by
  unfold prefixSum
  generalize w.take n = xs
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

private theorem new_prefix_succ {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (w : List (Fin (period gaps))) (n : ℕ) :
    newPrefix (period gaps) (necklaceSeed gaps) w (n + 1) =
      (necklaceSeed gaps : ℤ) + ((w.take n).map
        (fun i => actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc)).sum := by
  simp [newPrefix,earWord,List.map_map,Function.comp_def,
    (necklace_physical_totals hp gaps hg).2.2]

private theorem old_prefix_succ {k e : ℕ} (w : List (Fin k)) (n : ℕ) :
    oldPrefix k e w (n + 1) = ((w.take n).map (actualSource k e)).sum := by
  simp [oldPrefix]

private theorem ear0_perm (k : ℕ) (w : List (Fin k))
    (hw : w.Perm (List.finRange k)) :
    (earWord k w 0).Perm (List.finRange (k + 1)) := by
  have hp := (hw.map Fin.castSucc).cons (Fin.last k)
  have hq : (Fin.last k :: (List.finRange k).map Fin.castSucc).Perm
      ((List.finRange k).map Fin.castSucc ++ [Fin.last k]) := by
    simpa only [List.singleton_append] using
      (List.perm_append_comm : ([Fin.last k] ++ (List.finRange k).map Fin.castSucc).Perm
        ((List.finRange k).map Fin.castSucc ++ [Fin.last k]))
  simpa only [earWord,List.take_zero,List.map_nil,List.drop_zero,List.nil_append,
    List.singleton_append,← List.finRange_succ_last] using hp.trans hq

private theorem physical_error_card (m : ℕ) (P : Fin m → Prop) [DecidablePred P]
    (corners : List ℕ) (h : ∀ q, P q → q.val ∈ corners) :
    (Finset.univ.filter P).card ≤ corners.length := by
  have hc : (Finset.univ.filter P).card ≤ corners.toFinset.card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro q hq
      exact List.mem_toFinset.mpr (h q (Finset.mem_filter.mp hq).2)
    · intro a _ b _ he
      exact Fin.ext he
  exact hc.trans (List.toFinset_card_le _)


private theorem physical_rounding_of_fractional_fit {p : ℕ} (hp : 1 ≤ p)
    (gaps : Fin p → ℕ) (hg : ∀ j, 2 ≤ gaps j)
    (hfit : FractionalFits
      (fun i => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ))
      (fun i => (actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc : ℚ))
      ((modulus (period gaps) / 2 : ℤ) : ℚ) (modulus (period gaps))
      0 (necklaceSeed gaps) (necklaceBlocks gaps)) : PhysicalRounding gaps := by
  classical
  let k := period gaps
  let e := necklaceSeed gaps
  let N := modulus k
  let H := N / 2
  let f := actualSource k e
  let g := fun i : Fin k => actualSource (k + 1) (2 * e) i.castSucc
  let bs := necklaceBlocks gaps
  let wp := sigmaPlus gaps
  let wm := sigmaMinus gaps
  let cs := blockCorners bs
  have hwp : wp.Perm (List.finRange k) := necklace_blocks_inventory gaps hg
  have hnd : wp.Nodup := hwp.nodup_iff.mpr (List.nodup_finRange _)
  have hr := simultaneous_rounding (fun i => (f i : ℚ)) (fun i => (g i : ℚ))
    (H : ℚ) (N : ℚ) 0 (e : ℚ) bs hfit hnd
  rcases hr with ⟨hpm,hfs,hgs,hpairnd,hswap,hcornernd,hcornerlen,hcornerrange,
    hsigns,hprefix,hcornerloc,hpairloc,huppercard,hlowercard⟩
  have hwm : wm.Perm (List.finRange k) := hpm.symm.trans hwp
  have hpro := block_corner_projections bs
  have hcsp : cs.map CornerRecord.prefixLength =
      (cornerPositions bs).map (fun n => n + 1) := hpro.1
  have hcsij : cs.map (fun c => (c.positive,c.terminal)) = splitPairs bs := hpro.2.1
  have hlen : cs.length = (splitPairs bs).length := hpro.2.2
  have hcslen : cs.length ≤ p - 1 := hlen.trans_le (necklace_split_bound hp gaps hg)
  have hcsnd : (cs.map CornerRecord.prefixLength).Nodup := by
    rw [hcsp]
    exact hcornernd.map (by intro a b hab; dsimp at hab; omega)
  have hlabels : (cs.flatMap (fun c => [c.positive,c.terminal])).Nodup := by
    rw [← hcsij,List.flatMap_map] at hpairnd
    exact hpairnd
  have hcsmem : ∀ c ∈ cs, (c.positive,c.terminal) ∈ splitPairs bs := by
    intro c hc
    rw [← hcsij]
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  have hcsprops : ∀ c ∈ cs,
      0 < f c.positive ∧ 0 < g c.positive ∧ f c.terminal < 0 ∧ g c.terminal < 0 ∧
      IsStrictSplit gaps c.positive c.terminal ∧
      ∃ u v u' v' : List (Fin k), wp = u ++ [c.positive,c.terminal] ++ v ∧
        wm = u' ++ [c.terminal,c.positive] ++ v' ∧
        c.prefixLength = u.length + 2 ∧ c.prefixLength = u'.length + 2 := by
    intro c hc
    obtain ⟨h1,h2,h3,h4⟩ := hsigns (c.positive,c.terminal) (hcsmem c hc)
    dsimp only at h1 h2 h3 h4
    refine ⟨?_,?_,?_,?_,necklace_split_provenance gaps hg _ (hcsmem c hc),
      block_corner_locations bs c hc⟩
    · exact_mod_cast h1
    · exact_mod_cast h2
    · exact_mod_cast h3
    · exact_mod_cast h4
  have hpi : ∀ n : ℕ,
      0 ≤ ((wp.take n).map f).sum ∧
      0 ≤ (e : ℤ) + ((wp.take n).map g).sum ∧
      ((wm.take n).map f).sum ≤ H ∧
      (e : ℤ) + ((wm.take n).map g).sum ≤ N ∧
      (n ∉ cornerPositions bs →
        ((wp.take n).map f).sum ≤ H ∧
        (e : ℤ) + ((wp.take n).map g).sum ≤ N ∧
        0 ≤ ((wm.take n).map f).sum ∧
        0 ≤ (e : ℤ) + ((wm.take n).map g).sum) := by
    intro n
    have hh := hprefix n
    simp only [int_prefix_cast,zero_add] at hh
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2.1
    · exact_mod_cast hh.2.2.1
    · exact_mod_cast hh.2.2.2.1
    · intro hn
      have ht := hh.2.2.2.2 hn
      refine ⟨?_,?_,?_,?_⟩
      · exact_mod_cast ht.1
      · exact_mod_cast ht.2.1
      · exact_mod_cast ht.2.2.1
      · exact_mod_cast ht.2.2.2.1
  have hN : 0 ≤ N := by
    have hk := (necklace_chain_coordinates gaps hg 0 (by omega)).1
    exact le_of_lt (ZeroSumSubsets.source_cycle (by omega : 0 < k) e).1
  have hH : 0 ≤ H := Int.ediv_nonneg hN (by norm_num)
  have hplus : ∀ q, 0 ≤ oldPrefix k e wp q ∧ 0 ≤ newPrefix k e wp q := by
    intro q
    cases q with
    | zero => simp [oldPrefix,newPrefix]
    | succ n =>
      rw [old_prefix_succ,new_prefix_succ hp gaps hg]
      exact ⟨(hpi n).1,(hpi n).2.1⟩
  have hminus : ∀ q, oldPrefix k e wm q ≤ H ∧ newPrefix k e wm q ≤ N := by
    intro q
    cases q with
    | zero => simpa [oldPrefix,newPrefix] using And.intro hH hN
    | succ n =>
      rw [old_prefix_succ,new_prefix_succ hp gaps hg]
      exact ⟨(hpi n).2.2.1,(hpi n).2.2.2.1⟩
  have hbadplus : ∀ q, H < oldPrefix k e wp q ∨ N < newPrefix k e wp q →
      q ∈ cs.map CornerRecord.prefixLength := by
    intro q hq
    cases q with
    | zero => simp [oldPrefix,newPrefix] at hq; rcases hq with hq | hq <;> linarith
    | succ n =>
      have hn : n ∈ cornerPositions bs := by
        by_contra hn
        have hh := (hpi n).2.2.2.2 hn
        rw [old_prefix_succ,new_prefix_succ hp gaps hg] at hq
        rcases hq with hq | hq <;> linarith [hh.1,hh.2.1]
      rw [hcsp]
      exact List.mem_map.mpr ⟨n,hn,rfl⟩
  have hbadminus : ∀ q, oldPrefix k e wm q < 0 ∨ newPrefix k e wm q < 0 →
      q ∈ cs.map CornerRecord.prefixLength := by
    intro q hq
    cases q with
    | zero => simp [oldPrefix,newPrefix] at hq
    | succ n =>
      have hn : n ∈ cornerPositions bs := by
        by_contra hn
        have hh := (hpi n).2.2.2.2 hn
        rw [old_prefix_succ,new_prefix_succ hp gaps hg] at hq
        rcases hq with hq | hq <;> linarith [hh.2.2.1,hh.2.2.2]
      rw [hcsp]
      exact List.mem_map.mpr ⟨n,hn,rfl⟩
  have htotal (w : List (Fin k)) (hw : w.Perm (List.finRange k)) :
      oldPrefix k e w (k + 1) = 0 ∧ newPrefix k e w (k + 1) = 0 := by
    have hl : w.length = k := by simpa using hw.length_eq
    have ht : w.take k = w := List.take_of_length_le (by omega)
    have hf := (hw.map f).sum_eq.trans (necklace_physical_totals hp gaps hg).1
    have hg' := (hw.map g).sum_eq.trans (necklace_physical_totals hp gaps hg).2.1
    rw [old_prefix_succ,new_prefix_succ hp gaps hg,ht,hf,hg']
    simp
  unfold PhysicalRounding
  dsimp only
  refine ⟨wp,wm,cs,hwp,hwm,ear0_perm k wp hwp,ear0_perm k wm hwm,
    ?_,?_,(necklace_physical_totals hp gaps hg).2.2,
    (htotal wp hwp).1,(htotal wp hwp).2,(htotal wm hwm).1,(htotal wm hwm).2,
    hplus,hminus,hcslen,hcsnd,hlabels,hcsprops,?_,hbadplus,hbadminus,?_,?_⟩
  · simp [earWord]
  · simp [earWord]
  · rw [hcsij]; exact hswap
  · simpa only [List.length_map] using physical_error_card (k + 2)
      (fun q => H < oldPrefix k e wp q.val ∨ N < newPrefix k e wp q.val)
      (cs.map CornerRecord.prefixLength) (fun q hq => hbadplus q.val hq)
  · simpa only [List.length_map] using physical_error_card (k + 2)
      (fun q => oldPrefix k e wm q.val < 0 ∨ newPrefix k e wm q.val < 0)
      (cs.map CornerRecord.prefixLength) (fun q hq => hbadminus q.val hq)

private theorem partial_charge_covers_prefix {α : Type*} (mass charge : α → ℚ)
    (pos pre later post tail : List α) (i : α) (t : ℚ)
    (hpre : pre ++ i :: post = pos) (hlater : later ++ tail = pos)
    (hm : ∀ a ∈ pos, 0 < mass a) (hc : ∀ a ∈ pos, 0 ≤ charge a)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : (later.map mass).sum ≤ (pre.map mass).sum + t * mass i) :
    (later.map charge).sum ≤ (pre.map charge).sum + t * charge i := by
  have hpp : pre <+: pos := ⟨i::post,hpre⟩
  have hlp : later <+: pos := ⟨tail,hlater⟩
  have hi : i ∈ pos := by rw [← hpre]; simp
  by_cases hlen : later.length ≤ pre.length
  · obtain ⟨mid,hmid⟩ := List.prefix_of_prefix_length_le hlp hpp hlen
    have hmidpos : ∀ a ∈ mid, a ∈ pos := by
      intro a ha
      apply hpp.sublist.subset
      rw [← hmid]
      exact List.mem_append_right _ ha
    have hsum : 0 ≤ (mid.map charge).sum := List.sum_nonneg (by
      intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact hc b (hmidpos b hb))
    have hti : 0 ≤ t * charge i := mul_nonneg ht (hc i hi)
    rw [← hmid,List.map_append,List.sum_append]
    linarith
  · have hh : pre ++ [i] <+: pos := ⟨post,by simpa only [List.append_assoc,List.singleton_append] using hpre⟩
    have hle : (pre ++ [i]).length ≤ later.length := by simp only [List.length_append,List.length_singleton]; omega
    obtain ⟨mid,hmid⟩ := List.prefix_of_prefix_length_le hh hlp hle
    have hmidpos : ∀ a ∈ mid, a ∈ pos := by
      intro a ha
      apply hlp.sublist.subset
      rw [← hmid]
      exact List.mem_append_right _ ha
    have hmidsum : 0 ≤ (mid.map mass).sum := List.sum_nonneg (by
      intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact le_of_lt (hm b (hmidpos b hb)))
    have him : 0 < mass i := hm i hi
    have htf : t * mass i ≤ mass i := by nlinarith
    rw [← hmid,List.map_append,List.sum_append,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton] at hx
    have hz : (mid.map mass).sum = 0 := by linarith
    have hnil : mid = [] := by
      cases mid with
      | nil => rfl
      | cons a xs =>
        have ha : 0 < mass a := hm a (hmidpos a (by simp))
        have hs : 0 ≤ (xs.map mass).sum := List.sum_nonneg (by
          intro b hb; obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hb
          exact le_of_lt (hm c (hmidpos c (by simp [hc']))))
        simp only [List.map_cons,List.sum_cons] at hz
        linarith
    subst mid
    have hteq : t = 1 := by simp only [List.map_nil,List.sum_nil] at hx; nlinarith
    rw [← hmid]
    simp [hteq,List.map_append,List.sum_append]

private theorem state_rectangle_from_charge {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) (x C : ℚ)
    (hC0 : 0 ≤ C) (hCE : C ≤ (necklaceSeed gaps : ℚ))
    (hlo : (threshold gaps (r + 1) : ℚ) ≤ x)
    (hhi : x ≤ (threshold gaps r : ℚ))
    (hcover : (threshold gaps (r + 1) : ℚ) + (necklaceSeed gaps : ℚ) -
        (cyclicHead gaps (r + 1) : ℚ) < x →
      (necklaceSeed gaps : ℚ) - (winding gaps (r + 1) : ℚ) ≤ C) :
    Rectangle ((modulus (period gaps) / 2 : ℤ) : ℚ) (modulus (period gaps))
      (x - (threshold gaps (r + 1) : ℚ))
      ((necklaceSeed gaps : ℚ) + 2 * (x - (threshold gaps (r + 1) : ℚ)) - C) := by
  rcases necklace_chain_coordinates gaps hg r hr with
    ⟨hk,hep,heb,hhp,hhb,hhp',hhb',hho,hho',hz0,hzh,hz'p,hz'h,hz'o,
      hstep,hzstep,hw,hn,htau,hnb,hnh,htaup,htaub,hP,hC,hdir,hpeak,hfresh,rest⟩
  have heq : (threshold gaps r : ℚ) = (demand gaps r : ℚ) +
      (threshold gaps (r + 1) : ℚ) := by exact_mod_cast threshold_step gaps r hr
  have he : 3 * (necklaceSeed gaps : ℚ) ≤ (modulus (period gaps) : ℚ) := by exact_mod_cast heb
  have hh : (0 : ℚ) < cyclicHead gaps (r + 1) := by exact_mod_cast hhp'
  have hH : (demand gaps r : ℚ) ≤ ((modulus (period gaps) / 2 : ℤ) : ℚ) := by exact_mod_cast hnh
  have hpeakQ : 2 * (demand gaps r : ℚ) + (winding gaps (r + 1) : ℚ) ≤
      (modulus (period gaps) : ℚ) := by exact_mod_cast hpeak
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  by_cases hx : (threshold gaps (r + 1) : ℚ) + (necklaceSeed gaps : ℚ) -
      (cyclicHead gaps (r + 1) : ℚ) < x
  · have hc := hcover hx
    linarith
  · push_neg at hx
    linarith

private def laterPositive {p : ℕ} (gaps : Fin p → ℕ) (m : ℕ) : List (Fin (period gaps)) :=
  ((List.range p).drop m).reverse.flatMap (positiveChain gaps)

private def suffixTerminalCharge {p : ℕ} (gaps : Fin p → ℕ) (m : ℕ) : ℤ :=
  (((List.range p).drop m).map (terminalCharge gaps)).sum

private theorem later_positive_prefix {p : ℕ} (gaps : Fin p → ℕ) (m : ℕ) :
    laterPositive gaps m <+: positiveLabels gaps := by
  refine ⟨((List.range p).take m).reverse.flatMap (positiveChain gaps),?_⟩
  rw [positive_chain_order]
  unfold laterPositive
  rw [← List.flatMap_append,← List.reverse_append,List.take_append_drop]

private theorem later_positive_totals {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (m : ℕ) (hm : m ≤ p) :
    ((laterPositive gaps m).map (actualSource (period gaps) (necklaceSeed gaps))).sum =
      threshold gaps m + (necklaceSeed gaps : ℤ) - cyclicHead gaps m ∧
    ((laterPositive gaps m).map (physicalCharge gaps)).sum + suffixTerminalCharge gaps m =
      (necklaceSeed gaps : ℤ) - winding gaps m := by
  have hp : ((((List.range p).drop m).reverse).flatMap (positiveChain gaps)).Perm
      (((List.range p).drop m).flatMap (positiveChain gaps)) :=
    (List.reverse_perm _).flatMap_right (positiveChain gaps)
  have ht := chain_suffix_totals gaps hg m hm
  exact ⟨((hp.map _).sum_eq).trans ht.1,by
    change (((((List.range p).drop m).reverse).flatMap (positiveChain gaps)).map
      (physicalCharge gaps)).sum + (((List.range p).drop m).map (terminalCharge gaps)).sum = _
    rw [(hp.map (physicalCharge gaps)).sum_eq]
    exact ht.2⟩

private theorem terminal_charge_suffix_bounds {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (m : ℕ) :
    0 ≤ suffixTerminalCharge gaps m ∧
    suffixTerminalCharge gaps m ≤ suffixTerminalCharge gaps 0 := by
  have hall : ∀ r ∈ List.range p, 0 ≤ terminalCharge gaps r := by
    intro r hr
    obtain ⟨hi,hf,hg',hn,hnb,hnh,htau,rest⟩ :=
      terminal_coordinates gaps hg r (List.mem_range.mp hr)
    linarith
  have hd : 0 ≤ (((List.range p).drop m).map (terminalCharge gaps)).sum := List.sum_nonneg (by
    intro a ha; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
    exact hall r (List.mem_of_mem_drop hr))
  have ht : 0 ≤ (((List.range p).take m).map (terminalCharge gaps)).sum := List.sum_nonneg (by
    intro a ha; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
    exact hall r (List.mem_of_mem_take hr))
  have hs : ((List.range p).map (terminalCharge gaps)).sum =
      (((List.range p).take m).map (terminalCharge gaps)).sum +
      (((List.range p).drop m).map (terminalCharge gaps)).sum := by
    rw [← List.sum_append,← List.map_append,List.take_append_drop]
  refine ⟨hd,?_⟩
  simp only [suffixTerminalCharge,List.drop_zero]
  linarith

private theorem partial_charge_bounds {α : Type*} (c : α → ℚ)
    (pos pre post : List α) (i : α) (t : ℚ) (heq : pre ++ i :: post = pos)
    (hc : ∀ a ∈ pos, 0 ≤ c a) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (pre.map c).sum + t * c i ∧
    (pre.map c).sum + t * c i ≤ (pos.map c).sum := by
  have hi : i ∈ pos := by rw [← heq]; simp
  have hpre : 0 ≤ (pre.map c).sum := List.sum_nonneg (by
    intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hc b (by rw [← heq]; exact List.mem_append_left _ hb))
  have hpost : 0 ≤ (post.map c).sum := List.sum_nonneg (by
    intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hc b (by rw [← heq]; simp [hb]))
  have hti : 0 ≤ t * c i := mul_nonneg ht (hc i hi)
  have hti' : t * c i ≤ c i := by nlinarith [hc i hi]
  refine ⟨by linarith,?_⟩
  rw [← heq,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  linarith

private theorem fractional_positive_state_rectangle {p : ℕ} (hp : 1 ≤ p)
    (gaps : Fin p → ℕ) (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p)
    (pre post : List (Fin (period gaps))) (i : Fin (period gaps)) (t : ℚ)
    (hpre : pre ++ i :: post = positiveLabels gaps) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hlo : (threshold gaps (r + 1) : ℚ) ≤
      ((pre.map (fun j => (actualSource (period gaps) (necklaceSeed gaps) j : ℚ))).sum +
        t * actualSource (period gaps) (necklaceSeed gaps) i))
    (hhi : ((pre.map (fun j => (actualSource (period gaps) (necklaceSeed gaps) j : ℚ))).sum +
        t * actualSource (period gaps) (necklaceSeed gaps) i) ≤ (threshold gaps r : ℚ)) :
    let x := (pre.map (fun j => (actualSource (period gaps) (necklaceSeed gaps) j : ℚ))).sum +
      t * actualSource (period gaps) (necklaceSeed gaps) i
    let C := (pre.map (fun j => (physicalCharge gaps j : ℚ))).sum +
      t * physicalCharge gaps i + (suffixTerminalCharge gaps (r + 1) : ℚ)
    Rectangle ((modulus (period gaps) / 2 : ℤ) : ℚ) (modulus (period gaps))
      (x - (threshold gaps (r + 1) : ℚ))
      ((necklaceSeed gaps : ℚ) + 2 * (x - (threshold gaps (r + 1) : ℚ)) - C) := by
  dsimp only
  let f := fun j : Fin (period gaps) => (actualSource (period gaps) (necklaceSeed gaps) j : ℚ)
  let c := fun j : Fin (period gaps) => (physicalCharge gaps j : ℚ)
  have hc : ∀ a ∈ positiveLabels gaps, 0 ≤ c a := by
    intro a ha
    change (0 : ℚ) ≤ (physicalCharge gaps a : ℚ)
    exact_mod_cast physical_charge_nonneg gaps hg a
  have hm : ∀ a ∈ positiveLabels gaps, 0 < f a := by
    intro a ha
    change (0 : ℚ) < (actualSource (period gaps) (necklaceSeed gaps) a : ℚ)
    exact_mod_cast (positive_coordinates gaps hg a ha).1
  have hcb := partial_charge_bounds c _ pre post i t hpre hc ht ht1
  have htb := terminal_charge_suffix_bounds gaps hg (r + 1)
  have hzero := later_positive_totals gaps hg 0 (by omega)
  have hlzero : laterPositive gaps 0 = positiveLabels gaps := by
    simp only [laterPositive,List.drop_zero,positive_chain_order]
  rw [hlzero,(necklace_endpoints gaps).2.2.1] at hzero
  have htotal : ((positiveLabels gaps).map c).sum +
      (suffixTerminalCharge gaps 0 : ℚ) = (necklaceSeed gaps : ℚ) := by
    dsimp only [c]
    rw [int_list_cast]
    have hZ : ((positiveLabels gaps).map (physicalCharge gaps)).sum +
        suffixTerminalCharge gaps 0 = (necklaceSeed gaps : ℤ) := by simpa only [sub_zero] using hzero.2
    have hQ := congrArg (fun z : ℤ => (z : ℚ)) hZ
    simpa only [Int.cast_add,Int.cast_natCast] using hQ
  have ht0 : (0 : ℚ) ≤ suffixTerminalCharge gaps (r + 1) := by exact_mod_cast htb.1
  have htbound : (suffixTerminalCharge gaps (r + 1) : ℚ) ≤
      (suffixTerminalCharge gaps 0 : ℚ) := by exact_mod_cast htb.2
  apply state_rectangle_from_charge gaps hg r hr _ _ (by linarith [hcb.1])
    (by linarith [hcb.2]) hlo hhi
  intro hx
  obtain ⟨tail,hlater⟩ := later_positive_prefix gaps (r + 1)
  have hs := later_positive_totals gaps hg (r + 1) (by omega)
  have hmass : ((laterPositive gaps (r + 1)).map f).sum =
      (threshold gaps (r + 1) : ℚ) + (necklaceSeed gaps : ℚ) -
        (cyclicHead gaps (r + 1) : ℚ) := by
    dsimp only [f]
    rw [int_list_cast]
    exact_mod_cast hs.1
  have hcover := partial_charge_covers_prefix f c (positiveLabels gaps) pre
    (laterPositive gaps (r + 1)) post tail i t hpre hlater hm hc ht ht1
    (by rw [hmass]; exact le_of_lt hx)
  have hcharge : ((laterPositive gaps (r + 1)).map c).sum +
      (suffixTerminalCharge gaps (r + 1) : ℚ) =
        (necklaceSeed gaps : ℚ) - (winding gaps (r + 1) : ℚ) := by
    dsimp only [c]
    rw [int_list_cast]
    exact_mod_cast hs.2
  linarith

private def remainingTerminals {p : ℕ} (gaps : Fin p → ℕ) (m : ℕ) :
    List (Fin (period gaps) × ℚ) :=
  (List.range m).reverse.filterMap (fun r =>
    (labelAt (period gaps) (terminalIndex gaps r)).map
      (fun i => (i,(threshold gaps r : ℚ))))

private def consumedMass {p : ℕ} (gaps : Fin p → ℕ)
    (pre : List (Fin (period gaps))) : ℚ :=
  (pre.map (fun i => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ))).sum

private def consumedCharge {p : ℕ} (gaps : Fin p → ℕ)
    (pre : List (Fin (period gaps))) : ℚ :=
  (pre.map (fun i => (physicalCharge gaps i : ℚ))).sum

private def stageF {p : ℕ} (gaps : Fin p → ℕ) (pre : List (Fin (period gaps))) (m : ℕ) : ℚ :=
  consumedMass gaps pre - (threshold gaps m : ℚ)

private def stageY {p : ℕ} (gaps : Fin p → ℕ) (pre : List (Fin (period gaps))) (m : ℕ) : ℚ :=
  (necklaceSeed gaps : ℚ) + 2 * stageF gaps pre m -
    consumedCharge gaps pre - (suffixTerminalCharge gaps m : ℚ)

private theorem remaining_terminals_step {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p) :
    ∃ hi : terminalIndex gaps r < period gaps,
      remainingTerminals gaps (r + 1) =
        (⟨terminalIndex gaps r,hi⟩,(threshold gaps r : ℚ)) :: remainingTerminals gaps r ∧
      actualSource (period gaps) (necklaceSeed gaps) ⟨terminalIndex gaps r,hi⟩ = -demand gaps r ∧
      actualSource (period gaps + 1) (2 * necklaceSeed gaps)
        (⟨terminalIndex gaps r,hi⟩ : Fin (period gaps)).castSucc =
          -2 * demand gaps r - terminalCharge gaps r := by
  obtain ⟨hi,hf,hg,rest⟩ := terminal_coordinates gaps hg r hr
  refine ⟨hi,?_,hf,hg⟩
  simp [remainingTerminals,List.range_succ,List.reverse_append,labelAt,hi]

private theorem suffix_charge_step {p : ℕ} (gaps : Fin p → ℕ) (r : ℕ) (hr : r < p) :
    suffixTerminalCharge gaps r = terminalCharge gaps r + suffixTerminalCharge gaps (r + 1) := by
  have hi : r < (List.range p).length := by simpa using hr
  simp only [suffixTerminalCharge,List.drop_eq_getElem_cons hi,
    List.getElem_range hi,List.map_cons,List.sum_cons]

private theorem positive_stage_step {p : ℕ} (gaps : Fin p → ℕ)
    (pre : List (Fin (period gaps))) (i : Fin (period gaps)) (m : ℕ) :
    consumedMass gaps (pre ++ [i]) = consumedMass gaps pre +
      (actualSource (period gaps) (necklaceSeed gaps) i : ℚ) ∧
    stageF gaps (pre ++ [i]) m = stageF gaps pre m +
      (actualSource (period gaps) (necklaceSeed gaps) i : ℚ) ∧
    stageY gaps (pre ++ [i]) m = stageY gaps pre m +
      (actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc : ℚ) := by
  simp only [consumedMass,consumedCharge,stageF,stageY,List.map_append,List.sum_append,
    List.map_singleton,List.sum_singleton,physicalCharge,Int.cast_sub,Int.cast_mul,Int.cast_ofNat]
  constructor
  · trivial
  · constructor <;> ring

private theorem terminal_stage_step {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (pre : List (Fin (period gaps))) (r : ℕ) (hr : r < p)
    (j : Fin (period gaps)) (hj : j.val = terminalIndex gaps r) :
    stageF gaps pre r = stageF gaps pre (r + 1) +
      (actualSource (period gaps) (necklaceSeed gaps) j : ℚ) ∧
    stageY gaps pre r = stageY gaps pre (r + 1) +
      (actualSource (period gaps + 1) (2 * necklaceSeed gaps) j.castSucc : ℚ) := by
  obtain ⟨hi,hf,hg',rest⟩ := terminal_coordinates gaps hg r hr
  have he : (⟨terminalIndex gaps r,hi⟩ : Fin (period gaps)) = j := Fin.ext hj.symm
  rw [he] at hf hg'
  have hfq : (actualSource (period gaps) (necklaceSeed gaps) j : ℚ) = -(demand gaps r : ℚ) := by exact_mod_cast hf
  have hgq : (actualSource (period gaps + 1) (2 * necklaceSeed gaps) j.castSucc : ℚ) =
      -2 * (demand gaps r : ℚ) - (terminalCharge gaps r : ℚ) := by exact_mod_cast hg'
  simp only [stageF,stageY,threshold_step gaps r hr,suffix_charge_step gaps r hr,
    Int.cast_add,hfq,hgq]
  constructor <;> ring

private theorem fractional_stage_rectangle {p : ℕ} (hp : 1 ≤ p)
    (gaps : Fin p → ℕ) (hg : ∀ j, 2 ≤ gaps j) (r : ℕ) (hr : r < p)
    (pre post : List (Fin (period gaps))) (i : Fin (period gaps)) (t : ℚ)
    (hpre : pre ++ i :: post = positiveLabels gaps) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hlo : (threshold gaps (r + 1) : ℚ) ≤ consumedMass gaps pre +
      t * actualSource (period gaps) (necklaceSeed gaps) i)
    (hhi : consumedMass gaps pre + t * actualSource (period gaps) (necklaceSeed gaps) i ≤
      (threshold gaps r : ℚ)) :
    Rectangle ((modulus (period gaps) / 2 : ℤ) : ℚ) (modulus (period gaps))
      (stageF gaps pre (r + 1) + t * actualSource (period gaps) (necklaceSeed gaps) i)
      (stageY gaps pre (r + 1) +
        t * actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc) := by
  have hh := fractional_positive_state_rectangle hp gaps hg r hr pre post i t hpre ht ht1 hlo hhi
  dsimp only at hh
  convert hh using 1 <;>
    dsimp only [stageF,stageY,consumedMass,consumedCharge,physicalCharge] <;>
    push_cast <;> ring

private theorem positive_stream_charge_total {p : ℕ} (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    consumedCharge gaps (positiveLabels gaps) + (suffixTerminalCharge gaps 0 : ℚ) =
      (necklaceSeed gaps : ℚ) := by
  have ht := (later_positive_totals gaps hg 0 (by omega)).2
  have hz := (necklace_endpoints gaps).2.2.1
  have hl : laterPositive gaps 0 = positiveLabels gaps := by
    simp only [laterPositive,List.drop_zero,positive_chain_order]
  rw [hl,hz,sub_zero] at ht
  have hq := congrArg (fun z : ℤ => (z : ℚ)) ht
  simpa only [consumedCharge,int_list_cast,Int.cast_add,Int.cast_natCast] using hq

private theorem complete_stage_zero {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) :
    stageF gaps (positiveLabels gaps) 0 = 0 ∧
    stageY gaps (positiveLabels gaps) 0 = 0 := by
  have hm : consumedMass gaps (positiveLabels gaps) = (threshold gaps 0 : ℚ) := by
    rw [consumedMass,int_list_cast,total_positive_mass hp gaps hg]
  have hc := positive_stream_charge_total gaps hg
  constructor
  · simp only [stageF,hm,sub_self]
  · dsimp only [stageY,stageF]
    rw [hm]
    linarith

private theorem positive_prefix_mass_bound {p : ℕ} (hp : 1 ≤ p) (gaps : Fin p → ℕ)
    (hg : ∀ j, 2 ≤ gaps j) (pre post : List (Fin (period gaps)))
    (i : Fin (period gaps)) (hpre : pre ++ i :: post = positiveLabels gaps) :
    consumedMass gaps pre + (actualSource (period gaps) (necklaceSeed gaps) i : ℚ) ≤
      (threshold gaps 0 : ℚ) := by
  have hm : consumedMass gaps (positiveLabels gaps) = (threshold gaps 0 : ℚ) := by
    rw [consumedMass,int_list_cast,total_positive_mass hp gaps hg]
  have hpost : 0 ≤ consumedMass gaps post := List.sum_nonneg (by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    have hi : b ∈ positiveLabels gaps := by rw [← hpre]; simp [hb]
    exact_mod_cast le_of_lt (positive_coordinates gaps hg b hi).1)
  rw [← hpre] at hm
  simp only [consumedMass,List.map_append,List.sum_append,List.map_cons,List.sum_cons] at hm ⊢
  dsimp only [consumedMass] at hpost
  linarith

private theorem threshold_blocks_physical_fit {p : ℕ} (hp : 1 ≤ p)
    (gaps : Fin p → ℕ) (hg : ∀ j, 2 ≤ gaps j)
    (pre ps : List (Fin (period gaps))) (m : ℕ) (hm : m ≤ p)
    (hpre : pre ++ ps = positiveLabels gaps)
    (hlo : (threshold gaps m : ℚ) ≤ consumedMass gaps pre)
    (hhi : ∀ r, m = r + 1 → consumedMass gaps pre < (threshold gaps r : ℚ)) :
    FractionalFits
      (fun i => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ))
      (fun i => (actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc : ℚ))
      ((modulus (period gaps) / 2 : ℤ) : ℚ) (modulus (period gaps))
      (stageF gaps pre m) (stageY gaps pre m)
      (thresholdBlocks (fun i => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ))
        ps (remainingTerminals gaps m) (consumedMass gaps pre)) := by
  let f := fun i : Fin (period gaps) => (actualSource (period gaps) (necklaceSeed gaps) i : ℚ)
  let g := fun i : Fin (period gaps) =>
    (actualSource (period gaps + 1) (2 * necklaceSeed gaps) i.castSucc : ℚ)
  let H : ℚ := (modulus (period gaps) / 2 : ℤ)
  let N : ℚ := modulus (period gaps)
  change FractionalFits f g H N _ _ (thresholdBlocks f ps _ _)
  have htot : consumedMass gaps (positiveLabels gaps) = (threshold gaps 0 : ℚ) := by
    rw [consumedMass,int_list_cast,total_positive_mass hp gaps hg]
  have hNN : (0 : ℤ) ≤ modulus (period gaps) := by
    have hk := (necklace_chain_coordinates gaps hg 0 (by omega)).1
    exact le_of_lt (ZeroSumSubsets.source_cycle (by omega : 0 < period gaps) (necklaceSeed gaps)).1
  have hHH : (0 : ℤ) ≤ modulus (period gaps) / 2 := Int.ediv_nonneg hNN (by norm_num)
  induction ps generalizing pre m with
  | nil =>
    simp only [List.append_nil] at hpre
    subst pre
    have hm0 : m = 0 := by
      by_contra hm0
      obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hu := hhi r rfl
      have ha := threshold_antitone gaps hg 0 r (by omega) (by omega)
      have haq : (threshold gaps r : ℚ) ≤ (threshold gaps 0 : ℚ) := by exact_mod_cast ha
      rw [htot] at hu
      linarith
    subst m
    obtain ⟨hf,hy⟩ := complete_stage_zero hp gaps hg
    rw [hf,hy]
    simp only [remainingTerminals,List.range_zero,List.reverse_nil,List.filterMap_nil,
      thresholdBlocks,List.map_nil,FractionalFits,Rectangle]
    exact ⟨le_rfl,by dsimp only [H]; exact_mod_cast hHH,
      le_rfl,by dsimp only [N]; exact_mod_cast hNN⟩
  | cons i ps ih =>
    have hi : i ∈ positiveLabels gaps := by rw [← hpre]; simp
    obtain ⟨hfi,hfi3,hgi,hgib⟩ := positive_coordinates gaps hg i hi
    have hf : 0 < f i := by dsimp only [f]; exact_mod_cast hfi
    have hgf : 0 < g i := by dsimp only [g]; exact_mod_cast hgi
    have hf3 : 3 * f i ≤ N := by dsimp only [f,N]; exact_mod_cast hfi3
    have hend : consumedMass gaps pre + f i ≤ (threshold gaps 0 : ℚ) :=
      positive_prefix_mass_bound hp gaps hg pre ps i hpre
    have hpre' : (pre ++ [i]) ++ ps = positiveLabels gaps := by
      simpa only [List.append_assoc,List.singleton_append] using hpre
    cases m with
    | zero => linarith
    | succ r =>
      have hr : r < p := by omega
      obtain ⟨hit,hts,hfj,hgj⟩ := remaining_terminals_step gaps hg r hr
      let j : Fin (period gaps) := ⟨terminalIndex gaps r,hit⟩
      have hjf : f j = -(demand gaps r : ℚ) := by dsimp only [f,j]; exact_mod_cast hfj
      have hjg : g j = -2 * (demand gaps r : ℚ) - (terminalCharge gaps r : ℚ) := by
        dsimp only [g,j]; exact_mod_cast hgj
      have hn : (0 : ℚ) < demand gaps r := by
        have ht := terminal_coordinates gaps hg r hr
        exact_mod_cast ht.choose_spec.2.2.1
      have hjf0 : f j < 0 := by linarith
      have hjg0 : g j < 0 := by
        have htp : (1 : ℚ) ≤ terminalCharge gaps r := by
          obtain ⟨_,_,_,_,_,_,htp,rest⟩ := terminal_coordinates gaps hg r hr
          exact_mod_cast htp
        linarith
      have hu : consumedMass gaps pre < (threshold gaps r : ℚ) := hhi r rfl
      have hrect := fractional_stage_rectangle hp gaps hg r hr pre ps i 0 hpre
        (by norm_num) (by norm_num) (by simpa using hlo) (by simpa using le_of_lt hu)
      simp only [zero_mul,add_zero] at hrect
      have hpos := positive_stage_step gaps pre i (r + 1)
      have hterm := terminal_stage_step gaps hg (pre ++ [i]) r hr j rfl
      have hretF : stageF gaps (pre ++ [i]) r = stageF gaps pre (r + 1) + f i + f j := by
        rw [hterm.1,hpos.2.1]
      have hretY : stageY gaps (pre ++ [i]) r = stageY gaps pre (r + 1) + g i + g j := by
        rw [hterm.2,hpos.2.2]
      rw [hts]
      change FractionalFits f g H N _ _ (thresholdBlocks f (i::ps)
        ((j,(threshold gaps r : ℚ)) :: remainingTerminals gaps r) (consumedMass gaps pre))
      by_cases hd : (threshold gaps r : ℚ) < consumedMass gaps pre + f i
      · have hr0 : 0 < r := by
          by_contra hr0
          have he : r = 0 := by omega
          rw [he] at hd
          linarith
        let t := ((threshold gaps r : ℚ) - consumedMass gaps pre) / f i
        have ht : 0 < t := div_pos (sub_pos.mpr hu) hf
        have ht1 : t < 1 := (div_lt_one hf).mpr (by linarith)
        have hx : consumedMass gaps pre + t * f i = (threshold gaps r : ℚ) := by
          dsimp only [t]
          rw [div_mul_cancel₀ _ (ne_of_gt hf)]
          ring
        have hdb : (threshold gaps (r + 1) : ℚ) ≤ (threshold gaps r : ℚ) := by
          exact_mod_cast le_of_lt (threshold_strict gaps hg r hr)
        have hB := fractional_stage_rectangle hp gaps hg r hr pre ps i t hpre
          (le_of_lt ht) (le_of_lt ht1) (by
            change (threshold gaps (r + 1) : ℚ) ≤ consumedMass gaps pre + t * f i
            rw [hx]
            exact hdb) (by
            change consumedMass gaps pre + t * f i ≤ (threshold gaps r : ℚ)
            rw [hx])
        have hrpred : r - 1 + 1 = r := by omega
        have hprev : (threshold gaps r : ℚ) ≤ (threshold gaps (r - 1) : ℚ) := by
          exact_mod_cast threshold_antitone gaps hg (r - 1) r (by omega) (by omega)
        have hC := fractional_stage_rectangle hp gaps hg (r - 1) (by omega) pre ps i t hpre
          (le_of_lt ht) (le_of_lt ht1)
          (by
            change (threshold gaps (r - 1 + 1) : ℚ) ≤ consumedMass gaps pre + t * f i
            rw [hrpred,hx]) (by
            change consumedMass gaps pre + t * f i ≤ (threshold gaps (r - 1) : ℚ)
            rw [hx]
            exact hprev)
        rw [hrpred] at hC
        have hs := terminal_stage_step gaps hg pre r hr j rfl
        rw [hs.1,hs.2] at hC
        have hC' : Rectangle H N (stageF gaps pre (r + 1) + t * f i + f j)
            (stageY gaps pre (r + 1) + t * g i + g j) := by
          simpa only [add_assoc,add_comm,add_left_comm] using hC
        have hrec := ih (pre ++ [i]) r (by omega) hpre'
          (by rw [hpos.1]; exact le_of_lt hd) (by
            intro s hs
            have hspace := threshold_spacing gaps hg r s (by omega) hr
            have hq : N ≤ 3 * ((threshold gaps s : ℚ) - (threshold gaps r : ℚ)) := by
              dsimp only [N]; exact_mod_cast hspace
            rw [hpos.1]
            linarith)
        rw [thresholdBlocks,if_pos hd]
        change 0 < f i ∧ 0 < g i ∧ f j < 0 ∧ g j < 0 ∧ 0 < t ∧ t < 1 ∧
          Rectangle H N _ _ ∧ Rectangle H N _ _ ∧ Rectangle H N _ _ ∧ _
        refine ⟨hf,hgf,hjf0,hjg0,ht,ht1,hrect,hB,hC',?_⟩
        rw [← hretF,← hretY,← hpos.1]
        exact hrec
      · by_cases he : (threshold gaps r : ℚ) = consumedMass gaps pre + f i
        · have hrec := ih (pre ++ [i]) r (by omega) hpre'
            (by rw [hpos.1,← he]) (by
              intro s hs
              have hq : (threshold gaps r : ℚ) < (threshold gaps s : ℚ) := by
                have h := threshold_strict gaps hg s (by omega)
                rw [← hs] at h
                exact_mod_cast h
              rw [hpos.1,← he]
              exact hq)
          have hB := fractional_stage_rectangle hp gaps hg r hr pre ps i 1 hpre
            (by norm_num) (by norm_num)
            (by
              simp only [one_mul]
              change (threshold gaps (r + 1) : ℚ) ≤ consumedMass gaps pre + f i
              rw [← he]
              exact_mod_cast le_of_lt (threshold_strict gaps hg r hr))
            (by
              simp only [one_mul]
              change consumedMass gaps pre + f i ≤ (threshold gaps r : ℚ)
              rw [← he])
          simp only [one_mul] at hB
          rw [thresholdBlocks,if_neg hd,if_pos he]
          refine ⟨hrect,hB,?_⟩
          rw [← hretF,← hretY,← hpos.1]
          exact hrec
        · have hlt : consumedMass gaps pre + f i < (threshold gaps r : ℚ) := by
            exact lt_of_le_of_ne (le_of_not_gt hd) (Ne.symm he)
          have hrec := ih (pre ++ [i]) (r + 1) hm hpre'
            (by rw [hpos.1]; linarith) (by
              intro s hs
              have heq : s = r := by omega
              subst s
              rw [hpos.1]
              exact hlt)
          rw [thresholdBlocks,if_neg hd,if_neg he]
          refine ⟨hrect,?_⟩
          rw [← hpos.2.1,← hpos.2.2,← hpos.1]
          simpa only [hts] using hrec

/-- Uniform physical sparse-necklace rounding, with one possible exceptional
corner for each strict split and at most p-1 splits. -/
theorem uniform_sparse_necklace_rounding (p : ℕ) (hp : 1 ≤ p)
    (gaps : Fin p → ℕ) (hg : ∀ j, 2 ≤ gaps j) : PhysicalRounding gaps := by
  apply physical_rounding_of_fractional_fit hp gaps hg
  have hlo : (threshold gaps p : ℚ) ≤ consumedMass gaps [] := by simp [threshold_last,consumedMass]
  have hhi : ∀ r, p = r + 1 → consumedMass gaps [] < (threshold gaps r : ℚ) := by
    intro r hr
    have h := threshold_strict gaps hg r (by omega)
    rw [← hr,threshold_last] at h
    simpa only [consumedMass,List.map_nil,List.sum_nil] using (show (0 : ℚ) < (threshold gaps r : ℚ) by exact_mod_cast h)
  have hh := threshold_blocks_physical_fit hp gaps hg [] (positiveLabels gaps) p le_rfl
    (by simp) hlo hhi
  have hd : (List.range p).drop p = [] := by simp
  simpa only [stageF,stageY,consumedMass,consumedCharge,List.map_nil,List.sum_nil,
    suffixTerminalCharge,hd,threshold_last,Int.cast_zero,sub_zero,zero_sub,zero_mul,mul_zero,
    add_zero,remainingTerminals,thresholdTerminals,necklaceBlocks] using hh

end D5.S3.Combinatorics.Circle.SparseNecklaceRounding
