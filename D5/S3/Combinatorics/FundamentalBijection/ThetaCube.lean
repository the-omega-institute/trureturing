/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube
   mirror-E: none(waiver:third-iterate-fixed-enumeration)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite, mathlib/module/Mathlib.RingTheory.PowerSeries.Basic, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: none
   digest: The third-iterate fixed 231 and 312 avoiders have the claimed series. -/
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Classify
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Boundary
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Return
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Shape
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231SecondReturn
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231LargePrefix
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231LargeFinish
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumFactors
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube
local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p) (List.range' 1 (List.length p)))
open D5.S3.Combinatorics.ArrowWilfDefs
open ThetaFixedDefs ThetaBasicSumFactors ThetaBasicSumAvoid ThetaBasicSum
open ThetaBasicInverse ThetaBasicInverseBlocks ThetaBasicInverseGeneral ThetaBasicSumIndecomp
open ThetaCube312Classify PowerSeries
open ThetaCube231Boundary ThetaCube231Return ThetaCube231Shape
open ThetaCube231SecondReturn ThetaCube231LargeFinish ThetaCube231LargePrefix
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum (sumIndecomposable)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem result : ThetaFixedDefs.cubeClaim := by
  let Factor (u : List ℕ) : Prop :=
    0 < u.length ∧ u.Perm (List.range' 1 u.length) ∧ sumIndecomposable u
  have indecomp_cut (p : List ℕ) (hp : p.Perm (List.range' 1 p.length))
      (hind : sumIndecomposable p) :
      ∀ k, 0 < k → k < p.length → ∃ x ∈ p.take k, k < x := by
    classical
    intro k hk hkl
    by_contra! hsmall
    have hnodup := hp.nodup_iff.mpr List.nodup_range'
    have hsubset : (p.take k).toFinset ⊆ (List.range' 1 k).toFinset := by
      intro x hx
      have hxt := List.mem_toFinset.mp hx
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp
        (hp.mem_iff.mp (List.mem_of_mem_take hxt))
      exact List.mem_toFinset.mpr
        (List.mem_range'.mpr ⟨x - 1, by have := hsmall x hxt; omega, by omega⟩)
    have hcard : (p.take k).toFinset.card = (List.range' 1 k).toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hnodup.take,
        List.dedup_eq_self.mpr List.nodup_range', Nat.min_eq_left (by omega : k ≤ p.length)]
    have hset := Finset.eq_of_subset_of_card_le hsubset (by omega)
    obtain ⟨i, j, hji⟩ := hind ⟨k, hkl⟩ hk
    have hx := List.get_mem (p.take k) i
    have hy := List.get_mem (p.drop k) j
    have hybound : (p.drop k).get j ≤ k := le_trans hji (hsmall _ hx)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp
      (hp.mem_iff.mp (List.mem_of_mem_drop hy))
    have hyfirst : (p.drop k).get j ∈ p.take k := by
      apply List.mem_toFinset.mp
      rw [hset]
      exact List.mem_toFinset.mpr
        (List.mem_range'.mpr ⟨(p.drop k).get j - 1, by omega, by omega⟩)
    exact List.disjoint_left.mp (List.disjoint_take_drop hnodup (le_refl k)) hyfirst hy
  have hat_sum_left (u v : List ℕ) (hu : u.Perm (List.range' 1 u.length))
      (hv : v.Perm (List.range' 1 v.length))
      (x : ℕ) (hx : x ∈ u) :
      hat (u ++ v.map (fun y => y + u.length)) x = hat u x := by
    let m := u.length; let w := u ++ v.map (fun y => y + m)
    have hidx : w.idxOf x = u.idxOf x := List.idxOf_append_of_mem hx
    have hxi : u.idxOf x < m := List.idxOf_lt_length_of_mem hx
    have hget (i : ℕ) (hi : i < m) : w.getD i 0 = u.getD i 0 := by exact List.getD_append _ _ _ _ hi
    have hrec (i : ℕ) (hi : i < m) : IsLtrMax w i ↔ IsLtrMax u i := by
      constructor
      · intro hr j hj; simpa only [← hget j (by omega), ← hget i hi] using hr j hj
      · intro hr j hj; simpa only [hget j (by omega), hget i hi] using hr j hj
    have hgreatest (i : ℕ) (hi : i < m) :
        Nat.findGreatest (IsLtrMax w) i = Nat.findGreatest (IsLtrMax u) i := by
      induction i with
      | zero => rfl
      | succ i ih =>
          rw [Nat.findGreatest_succ, Nat.findGreatest_succ]
          by_cases hr : IsLtrMax u (i + 1)
          · simp [hr, (hrec _ hi).2 hr]
          · simp [hr, mt (hrec _ hi).1 hr, ih (by omega)]
    have hboundary : m < w.length → IsLtrMax w m := by
      intro hwm j hj; have hvpos : 0 < v.length := (by simp [w] at hwm; omega)
      have hmval : w.getD m 0 = v.getD 0 0 + m := by
        have hvmap : 0 < (v.map (fun y => y + m)).length := (by simp [hvpos])
        rw [List.getD_append_right u _ 0 m (le_refl m)]
        change (v.map (fun y => y + m)).getD (m - m) 0 = v.getD 0 0 + m; simp only [Nat.sub_self]
        rw [List.getD_eq_getElem _ 0 hvmap, List.getElem_map, List.getD_eq_getElem _ 0 hvpos]
      have hvalue : 1 ≤ v.getD 0 0 := by
        have hmem : v.getD 0 0 ∈ v := by
          rw [List.getD_eq_getElem _ 0 hvpos]; exact List.getElem_mem hvpos
        obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hv.mem_iff.mp hmem); omega
      have hjmem : u.getD j 0 ∈ u := by
        rw [List.getD_eq_getElem _ 0 (by omega : j < u.length)]
        exact List.getElem_mem (by omega : j < u.length)
      have hjbound : u.getD j 0 ≤ m := by
        obtain ⟨a, ha, hval⟩ := List.mem_range'.mp (hu.mem_iff.mp hjmem); omega
      rw [hget j (by omega), hmval]; omega
    unfold hat; dsimp only
    rw [hidx]; have hcase : (u.idxOf x + 1 < w.length ∧ ¬ IsLtrMax w (u.idxOf x + 1)) ↔
        (u.idxOf x + 1 < m ∧ ¬ IsLtrMax u (u.idxOf x + 1)) := by
      constructor
      · rintro ⟨hlen, hnrec⟩; have hlt : u.idxOf x + 1 < m := by
          by_contra h; have heq : u.idxOf x + 1 = m := (by omega)
          exact hnrec (heq ▸ hboundary (by omega))
        exact ⟨hlt, fun hr => hnrec ((hrec _ hlt).2 hr)⟩
      · rintro ⟨hlt, hnrec⟩
        refine ⟨by simp [w, m]; omega, ?_⟩; exact fun hr => hnrec ((hrec _ hlt).1 hr)
    by_cases hc : u.idxOf x + 1 < m ∧ ¬ IsLtrMax u (u.idxOf x + 1)
    · rw [if_pos ((hcase).2 hc), if_pos hc, hget _ hc.1]
    · rw [if_neg (fun h => hc ((hcase).1 h)), if_neg hc, hgreatest _ hxi]
      exact hget _ (lt_of_le_of_lt (Nat.findGreatest_le _) hxi)
  have hat_sum_right (u v : List ℕ) (hu : u.Perm (List.range' 1 u.length))
      (hv : v.Perm (List.range' 1 v.length))
      (x : ℕ) (hx : x ∈ v) :
      hat (u ++ v.map (fun y => y + u.length)) (x + u.length) = hat v x + u.length := by
    let m := u.length; let n := v.length
    let w := u ++ v.map (fun y => y + m); have hxpos : 1 ≤ x := by
      obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hv.mem_iff.mp hx); omega
    have hbound (y : ℕ) (hy : y ∈ u) : y ≤ m := by
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hu.mem_iff.mp hy); omega
    have hnotmem : x + m ∉ u := by
      intro h; have := hbound _ h; omega
    have hidxmap (t : List ℕ) (z : ℕ) : (t.map (fun y => y + m)).idxOf (z + m) = t.idxOf z := by
      simp only [List.idxOf, List.findIdx_map, Function.comp_def]
      congr 1; funext value; exact Bool.eq_iff_iff.mpr (by simp)
    have hidx : w.idxOf (x + m) = m + v.idxOf x := by
      rw [List.idxOf_append_of_notMem hnotmem, hidxmap]
    have hxi : v.idxOf x < n := List.idxOf_lt_length_of_mem hx; have hget (i : ℕ) (hi : i < n) :
        w.getD (m + i) 0 = v.getD i 0 + m := by
      rw [List.getD_append_right u _ 0 (m + i) (by omega : u.length ≤ m + i)]
      rw [show m + i - u.length = i by dsimp [m]; omega]
      rw [List.getD_eq_getElem _ 0 (by simpa [n] using hi), List.getElem_map,
        List.getD_eq_getElem _ 0 hi]
    have hget_left (i : ℕ) (hi : i < m) : w.getD i 0 = u.getD i 0 := List.getD_append _ _ _ _ hi
    have hrec (i : ℕ) (hi : i < n) : IsLtrMax w (m + i) ↔ IsLtrMax v i := by
      constructor
      · intro hr j hj
        have h := hr (m + j) (by omega); rw [hget j (by omega), hget i hi] at h; omega
      · intro hr j hj
        by_cases hjm : j < m
        · have huval : u.getD j 0 ∈ u := by
            rw [List.getD_eq_getElem _ 0 (by omega : j < u.length)]
            exact List.getElem_mem (by omega : j < u.length)
          have hvval : 1 ≤ v.getD i 0 := by
            have hmem : v.getD i 0 ∈ v := by
              rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi
            obtain ⟨a, _, ha⟩ := List.mem_range'.mp (hv.mem_iff.mp hmem); omega
          rw [hget_left j hjm, hget i hi]; have := hbound _ huval; omega
        · have jt : j - m < i := (by omega)
          have h := hr (j - m) jt; have hjeq : m + (j - m) = j := (by omega)
          rw [← hjeq, hget _ (by omega), hget i hi]; omega
    have hgreatest (i : ℕ) (hi : i < n) : Nat.findGreatest (IsLtrMax w) (m + i) =
          m + Nat.findGreatest (IsLtrMax v) i := by
      induction i with
      | zero =>
          have hr0 : IsLtrMax v 0 := (by intro j hj; omega)
          have hrm : IsLtrMax w m := (hrec 0 hi).2 hr0; simpa [Nat.findGreatest_eq hrm]
      | succ i ih =>
          have hi' : i < n := (by omega)
          have hr := hrec (i + 1) hi; have hsum : m + (i + 1) = (m + i) + 1 := (by omega)
          rw [hsum, Nat.findGreatest_succ, Nat.findGreatest_succ]
          have hrw : IsLtrMax w (m + i + 1) ↔ IsLtrMax v (i + 1) := by
            simpa [Nat.add_assoc] using hr
          by_cases h : IsLtrMax v (i + 1)
          · rw [if_pos (hrw.2 h), if_pos h]; omega
          · rw [if_neg (mt hrw.1 h), if_neg h, ih hi']
    unfold hat; dsimp only
    rw [hidx]; have hcase : (m + v.idxOf x + 1 < w.length ∧ ¬ IsLtrMax w (m + v.idxOf x + 1)) ↔
        (v.idxOf x + 1 < n ∧ ¬ IsLtrMax v (v.idxOf x + 1)) := by
      constructor
      · rintro ⟨hlen, hnr⟩
        have hlt : v.idxOf x + 1 < n := (by simp [w, m, n] at hlen; omega); refine ⟨hlt, ?_⟩
        exact fun hr => hnr ((hrec _ hlt).2 (by simpa [Nat.add_assoc] using hr))
      · rintro ⟨hlt, hnr⟩; refine ⟨by simp [w, m, n]; omega, ?_⟩
        exact fun hr => hnr ((hrec _ hlt).1 (by simpa [Nat.add_assoc] using hr))
    by_cases hc : v.idxOf x + 1 < n ∧ ¬ IsLtrMax v (v.idxOf x + 1)
    · rw [if_pos (hcase.2 hc), if_pos hc]; simpa [Nat.add_assoc] using hget _ hc.1
    · rw [if_neg (fun h => hc (hcase.1 h)), if_neg hc, hgreatest _ hxi]
      have hlt : Nat.findGreatest (IsLtrMax v) (v.idxOf x) < n :=
        lt_of_le_of_lt (Nat.findGreatest_le _) hxi
      simpa using hget _ hlt
  let GoodWord (k n : ℕ) (R : ℕ → ℕ → ℕ → Prop) (p : List ℕ) : Prop :=
    p.Perm (List.range' 1 n) ∧ ¬ DescendingTriple p R ∧ theta^[k] p = p
  let PrimeWord (k n : ℕ) (R : ℕ → ℕ → ℕ → Prop) (p : List ℕ) : Prop :=
    Factor p ∧ p.length = n ∧ ¬ DescendingTriple p R ∧ theta^[k] p = p
  let FactorSequence (k n : ℕ) (R : ℕ → ℕ → ℕ → Prop) :=
    {fs : List (List ℕ) // (∀ u ∈ fs, Factor u ∧ ¬ DescendingTriple u R ∧
      theta^[k] u = u) ∧ (sumFactors fs).length = n}
  have factorPerm (fs : List (List ℕ)) (hgood : ∀ u ∈ fs, Factor u) :
      (sumFactors fs).Perm (List.range' 1 (sumFactors fs).length) := by
    induction fs with
    | nil => simp [sumFactors]
    | cons u fs ih =>
        have hu : Factor u := hgood u (by simp); have htail : ∀ a ∈ fs, Factor a := by
          intro a ha; exact hgood a (by simp [ha])
        have hv := ih htail; have hshift : ((sumFactors fs).map (fun x => x + u.length)).Perm
            (List.range' (u.length + 1) (sumFactors fs).length) := by
          have h := hv.map (fun x => x + u.length)
          have hr : (List.range' 1 (sumFactors fs).length).map (fun x => x + u.length) =
                List.range' (u.length + 1) (sumFactors fs).length := by
            have hIco := List.Ico.map_add 1 ((sumFactors fs).length + 1) u.length
            convert hIco using 1 <;> simp [List.Ico] <;> omega
          simpa only [hr] using h
        have h := hu.2.1.append hshift; simpa [sumFactors, ← List.range'_append_1,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have factorTriples (fs : List (List ℕ)) (hgood : ∀ u ∈ fs, Factor u)
      (R : ℕ → ℕ → ℕ → Prop)
      (hshift : ∀ a b c m, R (a + m) (b + m) (c + m) ↔ R a b c) :
      DescendingTriple (sumFactors fs) R ↔ ∃ u ∈ fs, DescendingTriple u R := by
    induction fs with
    | nil => simp [sumFactors, DescendingTriple]
    | cons u fs ih =>
        have hu : Factor u := hgood u (by simp); have htail : ∀ a ∈ fs, Factor a := by
          intro a ha; exact hgood a (by simp [ha])
        have hv := factorPerm fs htail
        have hsum := descendingTriple_sum_iff (sumFactors (u :: fs)) u
          (sumFactors fs) rfl hu.2.1 hv R hshift
        have hind := ih htail; rw [hsum, hind]; simp
  have leaderRecords (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      (List.range' 1 p.length).filter (fun x => decide (IsLeader (B p) x)) =
        ((List.Ico 0 p.length).filter (IsLtrMax p)).map (fun i => p.getD i 0) := by
    have record_is_B_leader (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) (s : ℕ)
        (hs : s < p.length) (hrec : IsLtrMax p s) :
        IsLeader (B p) (p.getD s 0) := by
      have hnext : ∃ e, s < e ∧ e ≤ p.length ∧ (∀ j, s < j → j < e → ¬ IsLtrMax p j) ∧
          (e = p.length ∨ IsLtrMax p e) := by
        let Q : ℕ → Prop := fun e => s < e ∧ e ≤ p.length ∧ (e = p.length ∨ IsLtrMax p e)
        have hex : ∃ e, Q e := ⟨p.length, hs, le_refl _, Or.inl rfl⟩; let e := Nat.find hex
        have he : Q e := Nat.find_spec hex; refine ⟨e, he.1, he.2.1, ?_, he.2.2⟩
        intro j hsj hje hr; have hjQ : Q j := ⟨hsj, by omega, Or.inr hr⟩
        have hmin : e ≤ j := Nat.find_min' hex hjQ; omega
      obtain ⟨e, hse, he, hnon, hboundary⟩ := hnext
      have hcycle := cycleFrom_B_record_block p hp s e hse he hrec hnon hboundary
      rw [IsLeader, hcycle]; intro y hy
      obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp hy; have hil : i < e - s := by
        simpa [List.length_take, List.length_drop,
          Nat.min_eq_left (by omega : e - s ≤ p.length - s)]
          using hi
      have hsi : s + i < p.length := (by omega)
      have hget : ((p.drop s).take (e - s))[i] = p.getD (s + i) 0 := by
        rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem _ 0 hsi]
      rw [← hval, hget]; have hg : Nat.findGreatest (IsLtrMax p) (s + i) = s := by
        have hle : s ≤ Nat.findGreatest (IsLtrMax p) (s + i) := Nat.le_findGreatest (by omega) hrec
        have hu := Nat.findGreatest_le (P := IsLtrMax p) (s + i); by_contra hne
        have hgt : s < Nat.findGreatest (IsLtrMax p) (s + i) := (by omega)
        exact hnon _ hgt (by omega) (Nat.findGreatest_spec (by omega : 0 ≤ s + i) (by
            intro j hj; omega))
      simpa only [hg] using last_record_bounds_prefix p (s + i) hsi (s + i) (le_refl _)
    let records := (List.Ico 0 p.length).filter (IsLtrMax p)
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'; have hleader (x : ℕ) (hx : x ∈ p) :
        IsLeader (B p) x ↔ IsLtrMax p (p.idxOf x) := by
      have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
      have hget : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hidx]; exact List.getElem_idxOf hidx
      constructor
      · intro hlead; by_contra hnon; exact (nonrecord_not_B_leader p hp x hx hnon) hlead
      · intro hrec; rw [← hget]; exact record_is_B_leader p hp _ hidx hrec
    have hleft : ((List.range' 1 p.length).filter
        (fun x => decide (IsLeader (B p) x))).Pairwise (· < ·) :=
      (List.pairwise_lt_range' 1 (by omega : 0 < (1 : ℕ))).filter _
    have hright : (records.map (fun i => p.getD i 0)).Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij; have hi' : i < records.length := (by simpa using hi)
      have hj' : j < records.length := (by simpa using hj); simp only [List.getElem_map]
      have hix : records[i] < records[j] :=
        (List.pairwise_iff_getElem.mp ((List.Ico.pairwise_lt 0 p.length).filter _)) i j hi' hj' hij
      have hjmem : records[j] ∈ records := List.getElem_mem hj'
      have hjrec : IsLtrMax p records[j] := decide_eq_true_eq.mp (List.mem_filter.mp hjmem).2
      exact hjrec _ hix
    apply List.Pairwise.eq_of_mem_iff hleft hright; intro x; constructor
    · intro hx
      obtain ⟨hxr, hxlead⟩ := List.mem_filter.mp hx; have hxp : x ∈ p := hp.mem_iff.mpr hxr
      have hrec := (hleader x hxp).mp (decide_eq_true_eq.mp hxlead)
      have hidx : p.idxOf x ∈ records := List.mem_filter.mpr
        ⟨List.Ico.mem.mpr ⟨Nat.zero_le _, List.idxOf_lt_length_of_mem hxp⟩, decide_eq_true hrec⟩
      have hget : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 (List.idxOf_lt_length_of_mem hxp)]
        exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hxp)
      exact List.mem_map.mpr ⟨p.idxOf x, hidx, hget⟩
    · intro hx; obtain ⟨i, hi, hval⟩ := List.mem_map.mp hx; rw [← hval]
      obtain ⟨hiIco, hirec⟩ := List.mem_filter.mp hi
      have hil : i < p.length := (List.Ico.mem.mp hiIco).2; have hxp : p.getD i 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hil]; exact List.getElem_mem hil
      have hidx : p.idxOf (p.getD i 0) = i := by
        rw [List.getD_eq_getElem _ 0 hil]; simpa using (List.get_idxOf hnodup ⟨i, hil⟩)
      apply List.mem_filter.mpr; refine ⟨hp.mem_iff.mp hxp, ?_⟩
      have hrec : IsLtrMax p (p.idxOf (p.getD i 0)) := by
        rw [hidx]; exact decide_eq_true_eq.mp hirec
      exact decide_eq_true ((hleader _ hxp).mpr hrec)
  have B_perm (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      (B p).Perm (List.range' 1 p.length) := by
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hmem (x : ℕ) (hx : x ∈ p) : hat p x ∈ p := by
      have hi : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx; unfold hat; dsimp only
      split_ifs with h
      · rw [List.getD_eq_getElem _ 0 h.1]; exact List.getElem_mem h.1
      · have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf x) < p.length :=
          lt_of_le_of_lt (Nat.findGreatest_le _) hi
        rw [List.getD_eq_getElem _ 0 hg]; exact List.getElem_mem hg
    have hmapNodup : (p.map (hat p)).Nodup := hnodup.map_on (hat_inj_on p hnodup)
    have hsubset : (p.map (hat p)).toFinset ⊆ p.toFinset := by
      intro x hx; obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact List.mem_toFinset.mpr (hmem a ha)
    have hcard : (p.map (hat p)).toFinset.card = p.toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hmapNodup, List.dedup_eq_self.mpr hnodup]
    have heq : (p.map (hat p)).toFinset = p.toFinset :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hperm : (p.map (hat p)).Perm p := List.perm_of_nodup_nodup_toFinset_eq hmapNodup hnodup heq
    exact ((hp.symm.map _).trans hperm).trans hp
  let firstFactorEquiv (k n : ℕ) (R : ℕ → ℕ → ℕ → Prop) : FactorSequence k (n + 1) R ≃
        Σ j : Fin (n + 1), {u : List ℕ // PrimeWord k (j.val + 1) R u} ×
            FactorSequence k (n - j.val) R := by
    let split : FactorSequence k (n + 1) R → Σ j : Fin (n + 1),
          {u : List ℕ // PrimeWord k (j.val + 1) R u} ×
            FactorSequence k (n - j.val) R := fun fs => by
      cases hlist : fs.val with
      | nil =>
          have hlen := fs.property.2; simp [hlist, sumFactors] at hlen
      | cons u us =>
          have hu : Factor u ∧ ¬ DescendingTriple u R ∧
              theta^[k] u = u := by exact fs.property.1 u (by simp [hlist])
          have htail : ∀ a ∈ us, Factor a ∧ ¬ DescendingTriple a R ∧
              theta^[k] a = a := by intro a ha; exact fs.property.1 a (by simp [hlist, ha])
          have hlen : u.length + (sumFactors us).length = n + 1 := by
            simpa [hlist, sumFactors] using fs.property.2
          let j : Fin (n + 1) := ⟨u.length - 1, by have := hu.1.1; omega⟩
          have huLength : u.length = j.val + 1 := (by simp [j]; have := hu.1.1; omega)
          refine ⟨j, ⟨u, ⟨hu.1, huLength, hu.2.1, hu.2.2⟩⟩, ⟨us, htail, ?_⟩⟩; dsimp [j]; omega
    let join : (Σ j : Fin (n + 1), {u : List ℕ // PrimeWord k (j.val + 1) R u} ×
            FactorSequence k (n - j.val) R) → FactorSequence k (n + 1) R :=
        fun t => by
          rcases t with ⟨j, u, rest⟩
          refine ⟨u.val :: rest.val, ?_, ?_⟩
          · intro a ha; rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨u.property.1, u.property.2.2.1, u.property.2.2.2⟩
            · exact rest.property.1 a ha
          · have hlen : u.val.length = j.val + 1 := u.property.2.1
            have htail : (sumFactors rest.val).length = n - j.val := rest.property.2
            simp only [sumFactors, List.length_append, List.length_map]; omega
    apply (Equiv.ofBijective join ?_).symm; constructor
    · rintro ⟨j, u, rest⟩ ⟨j', u', rest'⟩ heq
      have hlist : u.val :: rest.val = u'.val :: rest'.val := (by exact congrArg Subtype.val heq)
      have hu : u.val = u'.val := (List.cons.inj hlist).1
      have hrest : rest.val = rest'.val := (List.cons.inj hlist).2; have hj : j = j' := by
        apply Fin.ext; have hlen := u.property.2.1; have hlen' := u'.property.2.1
        have hul := congrArg List.length hu; omega
      subst j'; have hU : u = u' := Subtype.ext hu
      have hR : rest = rest' := Subtype.ext hrest; simp [hU, hR]
    · intro fs; refine ⟨split fs, ?_⟩
      cases fs with
      | mk fs hfs =>
          cases fs with
          | nil =>
              have hbad := hfs.2; simp [sumFactors] at hbad
          | cons u us =>
              apply Subtype.ext; rfl
  have theta_B (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) : theta (B p) = p := by
    let records := (List.Ico 0 p.length).filter (IsLtrMax p); have hcycles : ∀ s ∈ records,
        cycleFrom (B p) (p.getD s 0) =
          (p.drop s).take (nextBoundary (IsLtrMax p) p.length s - s) := by
      intro s hs; obtain ⟨hsIco, hsrec⟩ := List.mem_filter.mp hs
      have hsn : s < p.length := (List.Ico.mem.mp hsIco).2
      let e := nextBoundary (IsLtrMax p) p.length s
      have hb : s < nextBoundary (IsLtrMax p) p.length s ∧
          nextBoundary (IsLtrMax p) p.length s ≤ p.length ∧
          (nextBoundary (IsLtrMax p) p.length s = p.length ∨
            IsLtrMax p (nextBoundary (IsLtrMax p) p.length s)) ∧
          ∀ j, s < j → j < nextBoundary (IsLtrMax p) p.length s → ¬ IsLtrMax p j := by
        unfold nextBoundary; simp only [dif_pos hsn]
        let Q : ℕ → Prop := fun e => s < e ∧ e ≤ p.length ∧ (e = p.length ∨ IsLtrMax p e)
        have hex : ∃ e, Q e := ⟨p.length, hsn, le_refl _, Or.inl rfl⟩
        have hfind : Q (Nat.find hex) := Nat.find_spec hex
        refine ⟨hfind.1, hfind.2.1, hfind.2.2, ?_⟩
        intro j hsj hjb hjP; have hmin : Nat.find hex ≤ j :=
          Nat.find_min' hex ⟨hsj, by omega, Or.inr hjP⟩
        omega
      exact cycleFrom_B_record_block p hp s e hb.1 hb.2.1
        (decide_eq_true_eq.mp hsrec) hb.2.2.2 hb.2.2.1
    unfold theta; rw [show (B p).length = p.length by simp, leaderRecords p hp]
    change (records.map (fun i => p.getD i 0)).flatMap (cycleFrom (B p)) = p; rw [List.flatMap_map]
    have heq : records.flatMap (fun s => cycleFrom (B p) (p.getD s 0)) =
        records.flatMap (fun s =>
          (p.drop s).take (nextBoundary (IsLtrMax p) p.length s - s)) :=
      List.flatMap_congr hcycles
    rw [heq]; have hzero : 0 < p.length → IsLtrMax p 0 := (by intro _ j hj; omega)
    simpa only [records, List.Ico.zero_bot, Nat.zero_le, List.drop_zero] using
      filter_interval_partition p (IsLtrMax p) 0 (Nat.zero_le _) hzero
  have inverseTheta (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      (theta p).Perm (List.range' 1 p.length) ∧ B (theta p) = p := by
    let n := p.length; let W := {q : List ℕ // q.Perm (List.range' 1 n)}
    have hfinite : Set.Finite {q : List ℕ | q.Perm (List.range' 1 n)} := by
      convert (List.permutations (List.range' 1 n)).finite_toSet using 1
      ext q
      exact List.mem_permutations.symm
    haveI : Finite W := hfinite
    have hvalid (q : W) : q.val.Perm (List.range' 1 q.val.length) := by
      have hlen : q.val.length = n := (by simpa using q.property.length_eq)
      simpa [hlen] using q.property
    let f : W → W := fun q =>
      ⟨B q.val, by
        have hlen : q.val.length = n := (by simpa using q.property.length_eq)
        simpa [hlen] using B_perm q.val (hvalid q)⟩
    have hinj : Function.Injective f := by
      intro x y hxy; have hB : B x.val = B y.val := congrArg Subtype.val hxy; apply Subtype.ext
      calc
        x.val = theta (B x.val) := (theta_B x.val (hvalid x)).symm
        _ = theta (B y.val) := by rw [hB]
        _ = y.val := theta_B y.val (hvalid y)
    have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
    obtain ⟨q, hq⟩ := hsurj (⟨p, hp⟩ : W); have hB : B q.val = p := congrArg Subtype.val hq
    have htheta : theta p = q.val := (by rw [← hB]; exact theta_B q.val (hvalid q)); constructor
    · simpa [htheta, n] using q.property
    · rw [htheta]; exact hB
  have cube_inverse (p : List ℕ) (hp : p.Perm (List.range' 1 p.length))
      (hfixed : theta^[3] p = p) : B (B (B p)) = p := by
    have hp1 : (theta p).Perm (List.range' 1 p.length) := (inverseTheta p hp).1
    have hp1' : (theta p).Perm (List.range' 1 (theta p).length) := by
      have hlen := hp1.length_eq; simpa [hlen] using hp1
    have hp2 : (theta^[2] p).Perm (List.range' 1 p.length) := by
      rw [Function.iterate_succ_apply']
      have h := (inverseTheta (theta p) hp1').1; rw [hp1.length_eq] at h
      simpa [Function.iterate_one] using h
    have hB1 : B (theta p) = p := (inverseTheta p hp).2; have hB2 : B (theta^[2] p) = theta p := by
      have h := (inverseTheta (theta p) hp1').2
      simpa [Function.iterate_succ_apply', Function.iterate_one] using h
    have hB3 : B (theta^[3] p) = theta^[2] p := by
      have hp2' : (theta^[2] p).Perm (List.range' 1 (theta^[2] p).length) := by
        have hlen := hp2.length_eq
        have hlen' : (theta^[2] p).length = p.length := (by simpa using hlen); rw [hlen']; exact hp2
      have h := (inverseTheta (theta^[2] p) hp2').2; simpa [Function.iterate_succ_apply'] using h
    have htheta2 : theta^[2] p = B p := (by simpa [hfixed] using hB3.symm)
    have hBfixed : B (B (B p)) = p := by
      calc
        B (B (B p)) = B (B (theta^[2] p)) := by rw [htheta2]
        _ = B (theta p) := by rw [hB2]
        _ = p := hB1
    exact hBfixed
  have fixed231_size_le_three (p : List ℕ) (hp : p.Perm (List.range' 1 p.length))
      (hindecomp : ∀ k, 0 < k → k < p.length → ∃ x ∈ p.take k, k < x)
      (havoid : ¬ Contains [2, 3, 1] [] 3 p)
      (hfixed : theta^[3] p = p) : p.length ≤ 3 := by
    have fixed231_bounded_absurd (p : List ℕ) (n : ℕ) (hlo : 7 ≤ n) (hhi : n ≤ 10)
        (hp : p.Perm (List.range' 1 n))
        (h0 : p.getD 0 0 = n) (h1 : p.getD 1 0 = 1)
        (h2 : p.getD 2 0 = n - 2) (h3 : p.getD 3 0 = 2)
        (hpen : p.getD (n - 2) 0 = n - 3) (hlast : p.getD (n - 1) 0 = n - 1)
        (hfixed : B (B (B p)) = p) : False := by
      have hlen : p.length = n := (by simpa using hp.length_eq)
      let middle := (p.drop 4).take (n - 6); have hprefix : p.take 4 = [n, 1, n - 2, 2] := by
        apply List.ext_getElem
        · simp [hlen]; omega
        · intro i hi _
          have hi4 : i < 4 := (by simpa [hlen, Nat.min_eq_left (by omega : 4 ≤ n)] using hi)
          rw [List.getElem_take]
          have hv : p[i] = p.getD i 0 := (List.getD_eq_getElem p 0 (by omega)).symm; rw [hv]
          interval_cases i <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
            assumption
      have hsuffix : p.drop (n - 2) = [n - 3, n - 1] := by
        apply List.ext_getElem
        · simp [hlen]; omega
        · intro i hi _; have hi2 : i < 2 := (by simp [hlen] at hi; omega)
          rw [List.getElem_drop]; have hv : p[n - 2 + i] = p.getD (n - 2 + i) 0 :=
            (List.getD_eq_getElem p 0 (by omega)).symm
          rw [hv]
          interval_cases i <;> simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          · simpa using hpen
          · simpa [show n - 2 + 1 = n - 1 by omega] using hlast
      have hword : p = [n, 1, n - 2, 2] ++ middle ++ [n - 3, n - 1] := by
        calc
          p = p.take (n - 2) ++ p.drop (n - 2) := (List.take_append_drop _ _).symm
          _ = [n, 1, n - 2, 2] ++ middle ++ [n - 3, n - 1] := by
            have htake : p.take (n - 2) = p.take 4 ++ middle := by
              conv_lhs => rw [show n - 2 = 4 + (n - 6) by omega, List.take_add]
            rw [htake, hprefix, hsuffix]
      have hrange : (List.range' 1 n).Perm
          ([n, 1, n - 2, 2] ++ List.range' 3 (n - 6) ++ [n - 3, n - 1]) := by
        interval_cases n <;> decide
      have hwhole : ([n, 1, n - 2, 2] ++ middle ++ [n - 3, n - 1]).Perm
          ([n, 1, n - 2, 2] ++ List.range' 3 (n - 6) ++ [n - 3, n - 1]) := by
        rw [← hword]; exact hp.trans hrange
      have hmiddle : middle.Perm (List.range' 3 (n - 6)) :=
        (List.perm_append_left_iff _).mp ((List.perm_append_right_iff _).mp hwhole)
      have hcheck : ∀ middle ∈ (List.range' 3 (n - 6)).permutations',
          let word := [n, 1, n - 2, 2] ++ middle ++ [n - 3, n - 1]
          B (B (B word)) ≠ word := by
        interval_cases n <;> decide
      rw [hword] at hfixed; exact hcheck middle (List.mem_permutations'.mpr hmiddle) hfixed
    -- The large-size theorem and the bounded checks exhaust all lengths.
    by_contra hnot; have hBfixed := cube_inverse p hp hfixed
    by_cases hlarge : 11 ≤ p.length
    · exact large_edge_collision p hp hlarge hindecomp havoid hBfixed
    have hfirst : p.getD 0 0 = p.length :=
      (avoid231_indecomp_iff_first_max p hp (by omega) havoid).mp hindecomp
    have hboundary := terminal_value_next_to_max p hp (by omega) hindecomp havoid hBfixed
    by_cases hfour : p.length = 4
    · have hcheck : ∀ q ∈ (List.range' 1 4).permutations',
          q.getD 0 0 = 4 → q.getD 1 0 = 1 → q.getD 3 0 = 3 →
          B (B (B q)) ≠ q := by decide
      have hmem : p ∈ (List.range' 1 4).permutations' :=
        List.mem_permutations'.mpr (by simpa [hfour] using hp)
      exact (hcheck p hmem (by simpa [hfour] using hfirst)
        hboundary.2 (by simpa [hfour] using hboundary.1)) hBfixed
    have hreturn := penultimate_block_ends_two p hp (by omega)
      hfirst hboundary.2 hboundary.1 hBfixed
    have hshape := return_edge_forces_initial_pair p hp (by omega)
      havoid hfirst hboundary.2 hboundary.1 hreturn
    have hpen := penultimate_value p hp (by omega) hfirst hboundary.2 hboundary.1 hreturn hBfixed
    have hsizes : p.length = 5 ∨ p.length = 6 ∨ 7 ≤ p.length := (by omega)
    rcases hsizes with h | h | h
    · have hcheck : ∀ q ∈ (List.range' 1 5).permutations',
          q.getD 0 0 = 5 → q.getD 1 0 = 1 → q.getD 4 0 = 4 →
          B (B (B q)) ≠ q := by decide
      have hmem : p ∈ (List.range' 1 5).permutations' :=
        List.mem_permutations'.mpr (by simpa [h] using hp)
      exact (hcheck p hmem (by simpa [h] using hfirst)
        hboundary.2 (by simpa [h] using hboundary.1)) hBfixed
    · have hcheck : ∀ q ∈ (List.range' 1 6).permutations',
          q.getD 0 0 = 6 → q.getD 1 0 = 1 → q.getD 5 0 = 5 →
          B (B (B q)) ≠ q := by decide
      have hmem : p ∈ (List.range' 1 6).permutations' :=
        List.mem_permutations'.mpr (by simpa [h] using hp)
      exact (hcheck p hmem (by simpa [h] using hfirst)
        hboundary.2 (by simpa [h] using hboundary.1)) hBfixed
    · exact fixed231_bounded_absurd p p.length h (by omega) hp hfirst hboundary.2
        hshape.1 hshape.2 hpen hboundary.1 hBfixed
  have sumIterate (u v : List ℕ) (hu : u.Perm (List.range' 1 u.length))
      (hv : v.Perm (List.range' 1 v.length)) (k : ℕ) :
      theta^[k] (u ++ v.map (fun y => y + u.length)) = theta^[k] u ++
          (theta^[k] v).map (fun y => y + u.length) := by
    have theta_sum (u v : List ℕ) (hu : u.Perm (List.range' 1 u.length))
        (hv : v.Perm (List.range' 1 v.length)) :
        theta (u ++ v.map (fun y => y + u.length)) = theta u ++
            (theta v).map (fun y => y + u.length) := by
      let m := u.length; let w := u ++ v.map (fun y => y + m); have hsum_perm (a b : List ℕ)
          (ha : a.Perm (List.range' 1 a.length))
          (hb : b.Perm (List.range' 1 b.length)) :
          (a ++ b.map (fun y => y + a.length)).Perm (List.range' 1 (a.length + b.length)) := by
        have hshift : (b.map (fun y => y + a.length)).Perm
            (List.range' (a.length + 1) b.length) := by
          have h := hb.map (fun y => y + a.length)
          have hr : (List.range' 1 b.length).map (fun y => y + a.length) =
              List.range' (a.length + 1) b.length := by
            have hIco := List.Ico.map_add 1 (b.length + 1) a.length
            have hlen : a.length + (b.length + 1) - (a.length + 1) = b.length := (by omega)
            simpa [List.Ico, hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIco
          simpa only [hr] using h
        have h := ha.append hshift; simpa [← List.range'_append_1, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      have hwperm : w.Perm (List.range' 1 w.length) := (by simpa [w, m] using hsum_perm u v hu hv)
      have hθu := inverseTheta u hu; have hθv := inverseTheta v hv
      have hθw := inverseTheta w hwperm
      have hθulen : (theta u).length = u.length := (by simpa using hθu.1.length_eq)
      have hθvlen : (theta v).length = v.length := (by simpa using hθv.1.length_eq)
      let rhs := theta u ++ (theta v).map (fun y => y + m)
      have hrhsperm : rhs.Perm (List.range' 1 rhs.length) := by
        have hθuvalid : (theta u).Perm
            (List.range' 1 (theta u).length) := by simpa [hθulen] using hθu.1
        have hθvvalid : (theta v).Perm
            (List.range' 1 (theta v).length) := by simpa [hθvlen] using hθv.1
        simpa [rhs, m, hθulen, hθvlen] using hsum_perm (theta u) (theta v) hθuvalid hθvvalid
      have hBsum (u v : List ℕ) (hu : u.Perm (List.range' 1 u.length))
          (hv : v.Perm (List.range' 1 v.length)) :
          B (u ++ v.map (fun y => y + u.length)) = B u ++ (B v).map (fun y => y + u.length) := by
        let m := u.length; let w := u ++ v.map (fun y => y + m)
        have hgetB (p : List ℕ) (i : ℕ) (hi : i < (B p).length) :
            (B p)[i] = hat p (i + 1) := by simp [Nat.add_comm]
        apply List.ext_getElem
        · simp [w, m]
        · intro i hiL hiR; have hiw : i < w.length := (by simpa [w, m] using hiL)
          by_cases him : i < m
          · have hx : i + 1 ∈ u := hu.mem_iff.mpr (List.mem_range'.mpr ⟨i, him, by omega⟩)
            rw [List.getElem_append_left (by simpa [m] using him)]
            rw [hgetB w i hiL, hgetB u i (by simpa using him)]
            exact hat_sum_left u v hu hv (i + 1) hx
          · have hj : i - m < v.length := (by simp [w] at hiw; omega)
            have hx : i - m + 1 ∈ v := hv.mem_iff.mpr (List.mem_range'.mpr ⟨i - m, hj, by omega⟩)
            rw [List.getElem_append_right (by simp [m]; omega)]
            have heq : i + 1 = (i - m + 1) + m := (by omega)
            have hpoint := hat_sum_right u v hu hv (i - m + 1) hx; rw [← heq] at hpoint
            simpa [w, m, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpoint
      have hBrhs : B rhs = w := by
        have h := hBsum (theta u) (theta v)
          (by simpa [hθulen] using hθu.1) (by simpa [hθvlen] using hθv.1)
        rw [hθu.2, hθv.2] at h; simpa [rhs, w, m, hθulen] using h
      change theta w = rhs
      calc
        theta w = theta (B (theta w)) := by rw [hθw.2]
        _ = theta (B rhs) := by rw [hθw.2, hBrhs]
        _ = rhs := theta_B rhs hrhsperm
    have hiter_perm (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
        ∀ j, (theta^[j] p).Perm (List.range' 1 p.length) := by
      intro j; induction j with
      | zero => simpa using hp
      | succ j ih =>
          have hlen : (theta^[j] p).length = p.length := (by simpa using ih.length_eq)
          have hvalid : (theta^[j] p).Perm
              (List.range' 1 (theta^[j] p).length) := by simpa [hlen] using ih
          rw [Function.iterate_succ_apply']; simpa [hlen] using (inverseTheta _ hvalid).1
    induction k with
    | zero => simp
    | succ k ih =>
        have huperm := hiter_perm u hu k; have hvperm := hiter_perm v hv k
        have hul : (theta^[k] u).length = u.length := (by simpa using huperm.length_eq)
        have huvalid : (theta^[k] u).Perm
            (List.range' 1 (theta^[k] u).length) := by simpa [hul] using huperm
        have hvl : (theta^[k] v).length = v.length := (by simpa using hvperm.length_eq)
        have hvvalid : (theta^[k] v).Perm
            (List.range' 1 (theta^[k] v).length) := by simpa [hvl] using hvperm
        rw [Function.iterate_succ_apply', ih]; have hsum := theta_sum (theta^[k] u)
          (theta^[k] v) huvalid hvvalid
        simpa [hul, Function.iterate_succ_apply'] using hsum
  let factorizationEquiv (k n : ℕ) (R : ℕ → ℕ → ℕ → Prop)
      (hshift : ∀ a b c m, R (a + m) (b + m) (c + m) ↔ R a b c) :
      {p : List ℕ // GoodWord k n R p} ≃ FactorSequence k n R := by
    classical
    have fixedFactors (fs : List (List ℕ)) (hgood : ∀ u ∈ fs, Factor u) (k : ℕ) :
        theta^[k] (sumFactors fs) = sumFactors fs ↔ ∀ u ∈ fs, theta^[k] u = u := by
      induction fs with
      | nil =>
          have hempty : ∀ j, theta^[j] ([] : List ℕ) = [] := by
            intro j; induction j with
            | zero => rfl
            | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
          simp [sumFactors, hempty]
      | cons u fs ih =>
          have hu : Factor u := hgood u (by simp); have htail : ∀ a ∈ fs, Factor a := by
            intro a ha; exact hgood a (by simp [ha])
          have hv := factorPerm fs htail; have hθuperm : (theta^[k] u).Perm
              (List.range' 1 u.length) := by
            have hiter : ∀ j, (theta^[j] u).Perm (List.range' 1 u.length) := by
              intro j; induction j with
              | zero => simpa using hu.2.1
              | succ j ihj =>
                have hlen : (theta^[j] u).length = u.length := (by simpa using ihj.length_eq)
                have hvalid : (theta^[j] u).Perm
                    (List.range' 1 (theta^[j] u).length) := by simpa [hlen] using ihj
                rw [Function.iterate_succ_apply']; simpa [hlen] using (inverseTheta _ hvalid).1
            exact hiter k
          have hθulen : (theta^[k] u).length = u.length := (by simpa using hθuperm.length_eq)
          have hsum := sumIterate u (sumFactors fs) hu.2.1 hv k; constructor
          · intro hfixed
            have hwhole : theta^[k] u ++ (theta^[k] (sumFactors fs)).map (fun x => x + u.length) =
                u ++ (sumFactors fs).map (fun x => x + u.length) := by
              simpa [sumFactors] using hsum.symm.trans hfixed
            have hfirst : theta^[k] u = u := by
              have htake := congrArg (fun l : List ℕ => l.take u.length) hwhole
              simpa [hθulen] using htake
            have hlast : theta^[k] (sumFactors fs) = sumFactors fs := by
              rw [hfirst] at hwhole; have hmap := List.append_cancel_left hwhole
              exact (List.map_inj_right (fun x y h => by omega)).mp hmap
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hfirst
            · exact (ih htail).mp hlast a ha
          · intro hfixed; have huFixed : theta^[k] u = u := hfixed u (by simp)
            have hvFixed : theta^[k] (sumFactors fs) = sumFactors fs :=
              (ih htail).mpr (by intro a ha; exact hfixed a (by simp [ha]))
            change theta^[k] (u ++ (sumFactors fs).map (fun x => x + u.length)) =
              u ++ (sumFactors fs).map (fun x => x + u.length)
            rw [hsum]; simp [huFixed, hvFixed]
    let facData (p : {p : List ℕ // GoodWord k n R p}) :
        {fs : List (List ℕ) // sumFactors fs = p.val ∧
          ∀ u ∈ fs, Factor u ∧ ¬ DescendingTriple u R ∧ theta^[k] u = u} := by
      have hlen : p.val.length = n := (by simpa using p.property.1.length_eq)
      have hp : p.val.Perm (List.range' 1 p.val.length) := (by simpa [hlen] using p.property.1)
      let fs := Classical.choose (exists_sum_factorization p.val hp)
      have hfs := (Classical.choose_spec (exists_sum_factorization p.val hp)).1
      have hgood := (Classical.choose_spec (exists_sum_factorization p.val hp)).2
      have havoids : ∀ u ∈ fs, ¬ DescendingTriple u R := by
        intro u hu htriple; apply p.property.2.1
        rw [← hfs]; exact (factorTriples fs hgood R hshift).mpr ⟨u, hu, htriple⟩
      have hfixed : ∀ u ∈ fs, theta^[k] u = u := by
        have h := (fixedFactors fs hgood k).mp (hfs.symm ▸ p.property.2.2); exact h
      exact ⟨fs, hfs, fun u hu => ⟨hgood u hu, havoids u hu, hfixed u hu⟩⟩
    let factorize : {p : List ℕ // GoodWord k n R p} → FactorSequence k n R := fun p =>
      ⟨(facData p).val, (facData p).property.2, by
        rw [(facData p).property.1]; simpa using p.property.1.length_eq⟩
    let assemble : FactorSequence k n R → {p : List ℕ // GoodWord k n R p} := fun fs => by
      have hgood : ∀ u ∈ fs.val, Factor u := fun u hu => (fs.property.1 u hu).1
      have hperm := factorPerm fs.val hgood
      have havoids : ¬ DescendingTriple (sumFactors fs.val) R := by
        intro htriple; obtain ⟨u, hu, hbad⟩ :=
          (factorTriples fs.val hgood R hshift).mp htriple
        exact (fs.property.1 u hu).2.1 hbad
      have hfixed : theta^[k] (sumFactors fs.val) = sumFactors fs.val :=
        (fixedFactors fs.val hgood k).mpr (fun u hu => (fs.property.1 u hu).2.2)
      exact ⟨sumFactors fs.val, by
        refine ⟨?_, havoids, hfixed⟩
        simpa [fs.property.2] using hperm⟩
    refine ⟨factorize, assemble, ?_, ?_⟩
    · intro p; apply Subtype.ext; exact (facData p).property.1
    · intro fs; have hchosen : sumFactors (factorize (assemble fs)).val = sumFactors fs.val := by
        exact (facData (assemble fs)).property.1
      have hgoodchosen : ∀ u ∈ (factorize (assemble fs)).val, Factor u :=
        fun u hu => ((factorize (assemble fs)).property.1 u hu).1
      have hgoodfs : ∀ u ∈ fs.val, Factor u := fun u hu => (fs.property.1 u hu).1
      have heq := sum_factorization_unique (sumFactors fs.val)
        (factorize (assemble fs)).val fs.val hchosen rfl hgoodchosen hgoodfs
      exact Subtype.ext heq
  have hcontains231 (p : List ℕ) : Contains [2, 3, 1] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[j.val] > p[i.val] ∧
        p[i.val] > p[k.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩; change List.Sublist [x 2, x 3, x 1] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 2 := (by simpa using (hf ⟨0, by simp⟩).symm)
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := (by simpa using (hf ⟨1, by simp⟩).symm)
      have h2 : p[(f ⟨2, by simp⟩).val] = x 1 := (by simpa using (hf ⟨2, by simp⟩).symm)
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [← h1, ← h0] using hlt 2 (by omega) (by omega)
      · simpa only [← h0, ← h2] using hlt 1 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hji, hik⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[k.val] else if t = 2 then p[i.val] else p[j.val]
      have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
        let f : Fin 3 → Fin p.length := fun t =>
          if t.val = 0 then i else if t.val = 1 then j else k
        have hf : StrictMono f := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [f]; omega
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩; intro t
        fin_cases t <;> simp [f]
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro t ht ht3; have h : t = 1 ∨ t = 2 := (by omega)
        rcases h with rfl | rfl <;> simp [x, hik, hji]
      · intro t ht ht3; have h : t = 1 ∨ t = 2 ∨ t = 3 := (by omega)
        rcases h with rfl | rfl | rfl <;> simp [x]
      · simpa [x] using hsub
  have hcontains312 (p : List ℕ) : Contains [3, 1, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] > p[k.val] ∧
        p[k.val] > p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩; change List.Sublist [x 3, x 1, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 3 := (by simpa using (hf ⟨0, by simp⟩).symm)
      have h1 : p[(f ⟨1, by simp⟩).val] = x 1 := (by simpa using (hf ⟨1, by simp⟩).symm)
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := (by simpa using (hf ⟨2, by simp⟩).symm)
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [← h0, ← h2] using hlt 2 (by omega) (by omega)
      · simpa only [← h2, ← h1] using hlt 1 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[j.val] else if t = 2 then p[k.val] else p[i.val]
      have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
        let f : Fin 3 → Fin p.length := fun t =>
          if t.val = 0 then i else if t.val = 1 then j else k
        have hf : StrictMono f := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [f]; omega
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩; intro t
        fin_cases t <;> simp [f]
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro t ht ht3; have h : t = 1 ∨ t = 2 := (by omega)
        rcases h with rfl | rfl <;> simp [x, hkj, hik]
      · intro t ht ht3; have h : t = 1 ∨ t = 2 ∨ t = 3 := (by omega)
        rcases h with rfl | rfl | rfl <;> simp [x]
      · simpa [x] using hsub
  intro σ hσ; have hcore (w : List ℕ) (R : ℕ → ℕ → ℕ → Prop)
      (hwlen : w.length = 3) (hwne : w ≠ [3, 2, 1])
      (hclass : ∀ p : List ℕ, (Factor p ∧ p ∈ fixedAvoiders p.length 3 σ) ↔
          p ∈ ([[1], [2, 1], w, [3, 2, 1]] : List (List ℕ)))
      (hshift : ∀ a b c m, R (a + m) (b + m) (c + m) ↔ R a b c)
      (hbridge : ∀ p : List ℕ, Contains σ [] σ.length p ↔ DescendingTriple p R) :
      gf 3 σ * (1 - X - X ^ 2 - 2 * X ^ 3) = 1 := by
    let L : List (List ℕ) := [[1], [2, 1], w, [3, 2, 1]]; let P (m : ℕ) : Set (List ℕ) :=
      {u | Factor u ∧ u.length = m ∧ u ∈ fixedAvoiders m 3 σ}
    have hset (m : ℕ) : P m = {u | u ∈ L ∧ u.length = m} := by
      ext u
      constructor
      · rintro ⟨hf, hlen, hfixed⟩
        have hfix' : u ∈ fixedAvoiders u.length 3 σ := (by simpa [hlen] using hfixed)
        exact ⟨(hclass u).mp ⟨hf, hfix'⟩, hlen⟩
      · rintro ⟨hu, hlen⟩
        have hg := (hclass u).mpr hu; exact ⟨hg.1, hlen, by simpa [hlen] using hg.2⟩
    have hcard (m : ℕ) : (P m).ncard =
        if m = 1 then 1 else if m = 2 then 1 else if m = 3 then 2 else 0 := by
      rw [hset]
      by_cases h1 : m = 1
      · subst m; have hs : {u : List ℕ | u ∈ L ∧ u.length = 1} = {([1] : List ℕ)} := by
          ext u; simp [L, or_and_right]; aesop
        rw [hs, Set.ncard_singleton]; simp
      by_cases h2 : m = 2
      · subst m; have hs : {u : List ℕ | u ∈ L ∧ u.length = 2} = {([2, 1] : List ℕ)} := by
          ext u; simp [L, or_and_right]; aesop
        rw [hs, Set.ncard_singleton]; simp
      by_cases h3 : m = 3
      · subst m; have hs : {u : List ℕ | u ∈ L ∧ u.length = 3} = {w, ([3, 2, 1] : List ℕ)} := by
          ext u; simp [L, or_and_right]; aesop
        rw [hs]; have htwo : ({w, ([3, 2, 1] : List ℕ)} : Set (List ℕ)).ncard = 2 :=
          Set.ncard_eq_two.mpr ⟨w, [3, 2, 1], hwne, rfl⟩
        simp [htwo]
      have hs : {u : List ℕ | u ∈ L ∧ u.length = m} = ∅ := by
        ext u; simp +contextual [L, or_and_right, hwlen, Ne.symm h1, Ne.symm h2, Ne.symm h3]
      rw [hs]; simp [h1, h2, h3]
    have hprime (j : ℕ) : ({u : List ℕ | Factor u ∧ u.length = j + 1 ∧
          u ∈ fixedAvoiders (j + 1) 3 σ} : Set (List ℕ)).ncard =
          if j = 0 then 1 else if j = 1 then 1 else if j = 2 then 2 else 0 := by
      change (P (j + 1)).ncard = _; rw [hcard]
      by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;>
        by_cases h2 : j = 2 <;> simp [h0, h1, h2]
    let f (n : ℕ) := (fixedAvoiders n 3 σ).ncard; have hzero : f 0 = 1 := by
      have hs : fixedAvoiders 0 3 σ = {([] : List ℕ)} := by
        ext p
        constructor
        · intro hp; have hlen : p.length = 0 := (by simpa using hp.1.length_eq)
          exact (List.length_eq_zero_iff.mp hlen)
        · intro hp
          have hnil : p = [] := (by simpa using hp); subst p; refine ⟨by simp, ?_, by decide⟩
          intro h; have hh := (hbridge []).mp h; simpa [DescendingTriple] using hh
      dsimp [f]; rw [hs, Set.ncard_singleton]
    have htransport (n : ℕ) : (fixedAvoiders (n + 1) 3 σ).ncard =
          ∑ j : Fin (n + 1), ({u : List ℕ | Factor u ∧ u.length = j.val + 1 ∧
              u ∈ fixedAvoiders (j.val + 1) 3 σ} : Set (List ℕ)).ncard *
              (fixedAvoiders (n - j.val) 3 σ).ncard := by
      classical
      have hGood (m : ℕ) :
          {p : List ℕ | GoodWord 3 m R p} = fixedAvoiders m 3 σ := by
        ext p
        constructor
        · rintro ⟨hperm, havoid, hfixed⟩; exact ⟨hperm, fun h => havoid ((hbridge p).mp h), hfixed⟩
        · rintro ⟨hperm, havoid, hfixed⟩; exact ⟨hperm, fun h => havoid ((hbridge p).mpr h), hfixed⟩
      have hPrime (m : ℕ) : {u : List ℕ | PrimeWord 3 m R u} =
            {u : List ℕ | Factor u ∧ u.length = m ∧ u ∈ fixedAvoiders m 3 σ} := by
        ext u
        constructor
        · rintro ⟨hfac, hlen, havoid, hfixed⟩
          refine ⟨hfac, hlen, ?_, fun h => havoid ((hbridge u).mp h), hfixed⟩
          simpa [hlen] using hfac.2.1
        · rintro ⟨hfac, hlen, hperm, havoid, hfixed⟩
          exact ⟨hfac, hlen, fun h => havoid ((hbridge u).mpr h), hfixed⟩
      have goodFinite (m : ℕ) : Finite {p : List ℕ // GoodWord 3 m R p} := by
        apply Set.finite_coe_iff.mpr
        apply (List.finite_toSet ((List.range' 1 m).permutations)).subset
        intro p hp; exact List.mem_permutations.mpr hp.1
      have primeFinite (m : ℕ) : Finite {p : List ℕ // PrimeWord 3 m R p} := by
        apply Set.finite_coe_iff.mpr
        apply (List.finite_toSet ((List.range' 1 m).permutations)).subset
        intro p hp; have hlen : p.length = m := hp.2.1
        exact List.mem_permutations.mpr (by simpa [hlen] using hp.1.2.1)
      letI (m : ℕ) : Finite {p : List ℕ // GoodWord 3 m R p} := goodFinite m
      letI (m : ℕ) : Finite {p : List ℕ // PrimeWord 3 m R p} := primeFinite m
      letI (m : ℕ) : Finite (FactorSequence 3 m R) :=
        Finite.of_injective (factorizationEquiv 3 m R hshift).symm
          (factorizationEquiv 3 m R hshift).symm.injective
      letI (j : Fin (n + 1)) : Finite ({u : List ℕ // PrimeWord 3 (j.val + 1) R u} ×
            FactorSequence 3 (n - j.val) R) := inferInstance
      calc
        (fixedAvoiders (n + 1) 3 σ).ncard =
            Nat.card {p : List ℕ // GoodWord 3 (n + 1) R p} := by
          change (fixedAvoiders (n + 1) 3 σ).ncard =
            Nat.card (↑({p : List ℕ | GoodWord 3 (n + 1) R p} : Set (List ℕ)))
          rw [Nat.card_coe_set_eq, hGood]
        _ = Nat.card (FactorSequence 3 (n + 1) R) :=
          Nat.card_congr (factorizationEquiv 3 (n + 1) R hshift)
        _ = Nat.card (Σ j : Fin (n + 1), {u : List ℕ // PrimeWord 3 (j.val + 1) R u} ×
                FactorSequence 3 (n - j.val) R) :=
          Nat.card_congr (firstFactorEquiv 3 n R)
        _ = ∑ j : Fin (n + 1), Nat.card {u : List ℕ // PrimeWord 3 (j.val + 1) R u} *
                Nat.card (FactorSequence 3 (n - j.val) R) := by
          rw [Nat.card_sigma]; simp only [Nat.card_prod]
        _ = ∑ j : Fin (n + 1), ({u : List ℕ | Factor u ∧ u.length = j.val + 1 ∧
                u ∈ fixedAvoiders (j.val + 1) 3 σ} : Set (List ℕ)).ncard *
                (fixedAvoiders (n - j.val) 3 σ).ncard := by
          apply Finset.sum_congr rfl
          intro j _; have hfirst : Nat.card {u : List ℕ // PrimeWord 3 (j.val + 1) R u} =
              ({u : List ℕ | Factor u ∧ u.length = j.val + 1 ∧
                u ∈ fixedAvoiders (j.val + 1) 3 σ} : Set (List ℕ)).ncard := by
            change Nat.card (↑({u : List ℕ | PrimeWord 3 (j.val + 1) R u} : Set (List ℕ))) = _
            rw [Nat.card_coe_set_eq, hPrime]
          have hlast : Nat.card (FactorSequence 3 (n - j.val) R) =
              (fixedAvoiders (n - j.val) 3 σ).ncard := by
            calc
              _ = Nat.card {p : List ℕ // GoodWord 3 (n - j.val) R p} :=
                (Nat.card_congr (factorizationEquiv 3 (n - j.val) R hshift)).symm
              _ = _ := by
                change Nat.card (↑({p : List ℕ | GoodWord 3 (n - j.val) R p} :
                  Set (List ℕ))) = _
                rw [Nat.card_coe_set_eq, hGood]
          rw [hfirst, hlast]
    have hcoeff (n : ℕ) : f (n + 1) = ∑ j : Fin (n + 1),
          (if j.val = 0 then 1 else if j.val = 1 then 1 else
            if j.val = 2 then 2 else 0) * f (n - j.val) := by
      have hr := htransport n; simpa only [f, hprime] using hr
    have hone : f 1 = 1 := by
      have hr := hcoeff 0; simpa [Fin.sum_univ_succ, hzero] using hr
    have htwo : f 2 = 2 := by
      have hr := hcoeff 1; simpa [Fin.sum_univ_succ, hzero, hone] using hr
    have hrec (n : ℕ) : f (n + 3) = f (n + 2) + f (n + 1) + 2 * f n := by
      have hr := hcoeff (n + 2); simpa [Fin.sum_univ_succ, Nat.add_sub_cancel_left,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
    let g : ℕ → ℤ := fun n => (f n : ℤ); have h0 : g 0 = 1 := (by simp [g]; exact_mod_cast hzero)
    have h1 : g 1 = 1 := (by simp [g]; exact_mod_cast hone)
    have h2 : g 2 = 2 := (by simp [g]; exact_mod_cast htwo)
    have hrec' (n : ℕ) : g (n + 3) = g (n + 2) + g (n + 1) + 2 * g n := by
      dsimp [g]
      exact_mod_cast hrec n
    have hseries : mk g * (1 - X - X ^ 2 - 2 * X ^ 3) = 1 := by
        let F : PowerSeries ℤ := mk g; have hpoly : F * (1 - X - X ^ 2 - 2 * X ^ 3) =
            F - X ^ 1 * F - X ^ 2 * F - X ^ 3 * F - X ^ 3 * F := by ring
        change F * (1 - X - X ^ 2 - 2 * X ^ 3) = 1; rw [hpoly]; apply PowerSeries.ext
        intro n; simp only [map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
        by_cases hz : n = 0
        · subst n; simp [F, h0]
        by_cases ho : n = 1
        · subst n; simp [F, h0, h1]
        by_cases ht : n = 2
        · subst n; simp [F, h0, h1, h2]
        have hn : n = (n - 3) + 3 := (by omega)
        have hr := hrec' (n - 3); rw [← hn] at hr; have h2n : n - 3 + 2 = n - 1 := (by omega)
        have h1n : n - 3 + 1 = n - 2 := (by omega); rw [h2n, h1n] at hr
        simp only [if_pos (by omega : 1 ≤ n), if_pos (by omega : 2 ≤ n),
          if_pos (by omega : 3 ≤ n), if_neg hz]
        simp only [F, PowerSeries.coeff_mk]
        change g n - g (n - 1) - g (n - 2) - g (n - 3) - g (n - 3) = 0; omega
    simpa [ThetaFixedDefs.gf, f, g] using hseries
  rcases hσ with h231 | h312
  · subst σ; apply hcore [3, 1, 2] (fun a b c => b > a)
    · decide
    · decide
    · intro p
      constructor
      · rintro ⟨hfactor, hfixed⟩
        have hsmall := fixed231_size_le_three p hfactor.2.1
          (indecomp_cut p hfactor.2.1 hfactor.2.2) hfixed.2.1 hfixed.2.2
        have hfirst := (avoid231_indecomp_iff_first_max p hfactor.2.1
          hfactor.1 hfixed.2.1).mp (indecomp_cut p hfactor.2.1 hfactor.2.2)
        have hcheck : ∀ n : Fin 4, ∀ q ∈ (List.range' 1 n.val).permutations',
            0 < n.val → q.getD 0 0 = n.val →
            q ∈ ([[1], [2, 1], [3, 1, 2], [3, 2, 1]] : List (List ℕ)) := by decide
        exact hcheck ⟨p.length, by omega⟩ p (List.mem_permutations'.mpr hfactor.2.1)
          hfactor.1 hfirst
      · intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h <;> subst p
        all_goals
          refine ⟨⟨by decide, by decide, by unfold sumIndecomposable; decide⟩,
            ⟨by decide, ?_, by decide⟩⟩
          · change ¬ Contains [2, 3, 1] [] 3 _; rw [hcontains231]; decide
    · intro a b c m; omega
    · intro p; change Contains [2, 3, 1] [] 3 p ↔ DescendingTriple p (fun a b c => b > a)
      rw [hcontains231]; constructor
      · rintro ⟨i, j, k, hij, hjk, hji, hik⟩; refine ⟨i.val, j.val, k.val, hij, hjk, k.isLt, ?_, ?_⟩
        · rw [List.getD_eq_getElem p 0 i.isLt, List.getD_eq_getElem p 0 k.isLt]; exact hik
        · rw [List.getD_eq_getElem p 0 j.isLt, List.getD_eq_getElem p 0 i.isLt]; exact hji
      · rintro ⟨i, j, k, hij, hjk, hk, hik, hji⟩
        refine ⟨⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, hk⟩, hij, hjk, ?_, ?_⟩
        · rw [List.getD_eq_getElem p 0 (by omega : j < p.length),
            List.getD_eq_getElem p 0 (by omega : i < p.length)] at hji
          exact hji
        · rw [List.getD_eq_getElem p 0 (by omega : i < p.length),
            List.getD_eq_getElem p 0 hk] at hik
          exact hik
  · subst σ; apply hcore [2, 3, 1] (fun a b c => c > b)
    · decide
    · decide
    · intro p
      constructor
      · rintro ⟨hfactor, hfixedset⟩; have hp := hfactor.2.1; have hpos := hfactor.1
        have hindecomp := indecomp_cut p hfactor.2.1 hfactor.2.2; have havoid := hfixedset.2.1
        have hfixed := hfixedset.2.2; have hsmall : p.length ≤ 3 := by
          by_contra hnot; have hBfixed := cube_inverse p hp hfixed
          exact fixed312_large_absurd p hp (by omega) hindecomp havoid hBfixed
        have hlast := (avoid312_indecomp_iff_last_one p hp hpos havoid).mp hindecomp
        have hcheck : ∀ n : Fin 4, ∀ q ∈ (List.range' 1 n.val).permutations',
            0 < n.val → q.getD (n.val - 1) 0 = 1 →
            q ∈ ([[1], [2, 1], [2, 3, 1], [3, 2, 1]] : List (List ℕ)) := by decide
        exact hcheck ⟨p.length, by omega⟩ p (List.mem_permutations'.mpr hp) hpos hlast
      · intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h <;> subst p
        all_goals
          refine ⟨⟨by decide, by decide, by unfold sumIndecomposable; decide⟩,
            ⟨by decide, ?_, by decide⟩⟩
          · change ¬ Contains [3, 1, 2] [] 3 _; rw [hcontains312]; decide
    · intro a b c m; omega
    · intro p; change Contains [3, 1, 2] [] 3 p ↔ DescendingTriple p (fun a b c => c > b)
      rw [hcontains312]; constructor
      · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩; refine ⟨i.val, j.val, k.val, hij, hjk, k.isLt, ?_, ?_⟩
        · rw [List.getD_eq_getElem p 0 i.isLt, List.getD_eq_getElem p 0 k.isLt]; exact hik
        · rw [List.getD_eq_getElem p 0 k.isLt, List.getD_eq_getElem p 0 j.isLt]; exact hkj
      · rintro ⟨i, j, k, hij, hjk, hk, hik, hkj⟩
        refine ⟨⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, hk⟩, hij, hjk, ?_, ?_⟩
        · rw [List.getD_eq_getElem p 0 (by omega : i < p.length),
            List.getD_eq_getElem p 0 hk] at hik
          exact hik
        · rw [List.getD_eq_getElem p 0 hk,
            List.getD_eq_getElem p 0 (by omega : j < p.length)] at hkj
          exact hkj

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube
