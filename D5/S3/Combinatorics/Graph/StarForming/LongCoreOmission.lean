/- GID: D5/S3/Combinatorics/Graph/StarForming/LongCoreOmission
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/LongCoreOmission
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual open-core score extraction and symbolic cyclic exceptional-state exclusion. -/

import D5.S3.Combinatorics.Graph.StarForming.ClosedModule
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The structural all-length upper proof in LONG_CORE_SHARP_OMISSION,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69.
Unlike ClosedCore, this graph has no H5--H0 edge. Its possible score
thirteen is retained and paid by the actual neighboring H seam. -/
namespace D5.S3.Combinatorics.Graph.StarForming.LongCoreOmission
open StarFormingDissociationRefutation LongCoreUpper
open scoped BigOperators

def graph : SimpleGraph (Fin 20) where
  Adj := LongCoreWord.insideAdj
  symm := ⟨fun _ _ h => (LongCoreWord.inside_simple.2 _ _).mp h⟩
  loopless := ⟨LongCoreWord.inside_simple.1⟩
instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (LongCoreWord.insideAdj a b))

private def reflection : Fin 20 → Fin 20 :=
  ![5,4,3,2,1,0,11,10,9,8,7,6,17,16,15,14,13,12,19,18]
private def iota (f : Bool) (v : Fin 20) : Fin 20 := if f then reflection v else v

private theorem reflected : ∀ f : Bool, ∀ a b : Fin 20,
    graph.Adj (iota f a) (iota f b) ↔ graph.Adj a b := by decide +kernel
private theorem injective : ∀ f : Bool, Function.Injective (iota f) := by decide +kernel

def bit (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) : ℕ :=
  if iota f v∈S then 1 else 0

private theorem bit_bound (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) :
    bit S f v≤1 := by unfold bit; split_ifs <;> omega

def full (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) : ℕ :=
  if iota f a∈S ∧ iota f b∈S then 1 else 0

private theorem full_bounds (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) :
    full S f a b≤1 ∧ full S f a b≤bit S f a ∧ full S f a b≤bit S f b := by
  by_cases ha : iota f a∈S <;> by_cases hb : iota f b∈S <;> simp [full,bit,ha,hb]

private theorem triple (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S)
    (f : Bool) (a b c : Fin 20) (hab : graph.Adj a b) (hbc : graph.Adj b c) (hne : a≠c) :
    bit S f a+bit S f b+bit S f c≤2 := by
  have hnot : ¬ (iota f a∈S ∧ iota f b∈S ∧ iota f c∈S) := by
    rintro ⟨ha,hb,hc⟩
    have he := (SubQuorum.DoubleStarGrafting.independent_iff graph S).mp hS
      (iota f b) hb (iota f a) ha (iota f c) hc
      (graph.adj_symm ((reflected f a b).mpr hab)) ((reflected f b c).mpr hbc)
    exact hne (injective f he)
  by_cases ha : iota f a∈S <;> by_cases hb : iota f b∈S <;>
    by_cases hc : iota f c∈S <;> simp_all [bit]

def cell (S : Finset (Fin 20)) (f : Bool) : Fin 3 → Cell :=
  ![{highLeft := bit S f 0, highRight := bit S f 1, leafLeft := bit S f 6, leafRight := bit S f 7, cut := full S f 12 13},
    {highLeft := bit S f 2, highRight := bit S f 3, leafLeft := bit S f 8, leafRight := bit S f 9, cut := full S f 14 15},
    {highLeft := bit S f 4, highRight := bit S f 5, leafLeft := bit S f 10, leafRight := bit S f 11, cut := full S f 16 17}]

def omitted (S : Finset (Fin 20)) (f : Bool) : ℕ :=
  (if iota f 12∉S ∧ iota f 13∉S then 1 else 0)+
  (if iota f 14∉S ∧ iota f 15∉S then 1 else 0)+
  (if iota f 16∉S ∧ iota f 17∉S then 1 else 0)

private theorem pair_score (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) :
    bit S f a+bit S f b+(if iota f a∉S ∧ iota f b∉S then 1 else 0)=1+full S f a b := by
  by_cases ha : iota f a∈S <;> by_cases hb : iota f b∈S <;> simp [bit,full,ha,hb]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
private theorem score (S : Finset (Fin 20)) (f : Bool) :
    S.card+omitted S f=3+(cell S f 0).weight+(cell S f 1).weight+
      (cell S f 2).weight+bit S f 18+bit S f 19 := by
  have hcard : S.card=∑ v : Fin 20, bit S false v := by simp [bit,iota]
  norm_num only [Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.add_zero] at hcard
  change S.card=bit S false 0+(bit S false 1+(bit S false 2+(bit S false 3+(bit S false 4+(bit S false 5+(bit S false 6+(bit S false 7+(bit S false 8+(bit S false 9+(bit S false 10+(bit S false 11+(bit S false 12+(bit S false 13+(bit S false 14+(bit S false 15+(bit S false 16+(bit S false 17+(bit S false 18+(bit S false 19))))))))))))))))))) at hcard
  have h0 := pair_score S f 12 13
  have h1 := pair_score S f 14 15
  have h2 := pair_score S f 16 17
  have href (v : Fin 20) : bit S true v=bit S false (reflection v) := rfl
  cases f <;>
    simp [cell,Cell.weight,omitted,iota,reflection,href] at h0 h1 h2 ⊢ <;>
    omega

private theorem omitted_reflection (S : Finset (Fin 20)) : omitted S true=omitted S false := by
  simp [omitted,iota,reflection,and_comm] <;> omega

private theorem valid (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) (f : Bool)
    (j : Fin 3) : Valid (cell S f j) (bit S f 18) (bit S f 19) := by
  fin_cases j
  · have hf := full_bounds S f 12 13
    have h0 := triple S hS f 1 0 6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 0 1 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 0 6 12 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 1 7 13 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h4 := triple S hS f 0 6 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 := triple S hS f 1 7 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h6 := triple S hS f 12 6 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h7 := triple S hS f 13 7 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Valid]
    refine ⟨bit_bound S f 0,bit_bound S f 1,bit_bound S f 6,bit_bound S f 7,hf.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals omega
  · have hf := full_bounds S f 14 15
    have h0 := triple S hS f 3 2 8 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 2 3 9 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 2 8 14 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 3 9 15 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h4 := triple S hS f 2 8 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 := triple S hS f 3 9 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h6 := triple S hS f 14 8 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h7 := triple S hS f 15 9 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Valid]
    refine ⟨bit_bound S f 2,bit_bound S f 3,bit_bound S f 8,bit_bound S f 9,hf.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals omega
  · have hf := full_bounds S f 16 17
    have h0 := triple S hS f 5 4 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 4 5 11 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 4 10 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 5 11 17 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h4 := triple S hS f 4 10 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 := triple S hS f 5 11 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h6 := triple S hS f 16 10 18 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h7 := triple S hS f 17 11 19 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Valid]
    refine ⟨bit_bound S f 4,bit_bound S f 5,bit_bound S f 10,bit_bound S f 11,hf.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals omega

private theorem across (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) (f : Bool)
    (j : Fin 2) : Across (cell S f ⟨j.val,by omega⟩) (cell S f ⟨j.val+1,by omega⟩) := by
  fin_cases j
  · have hf := full_bounds S f 12 13
    have hg := full_bounds S f 14 15
    have h0 := triple S hS f 0 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 7 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 1 2 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 7 13 14 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Across]
    omega
  · have hf := full_bounds S f 14 15
    have hg := full_bounds S f 16 17
    have h0 := triple S hS f 2 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h1 := triple S hS f 9 3 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h2 := triple S hS f 3 4 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h3 := triple S hS f 9 15 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    dsimp [cell,Across]
    omega

private theorem oriented_cap (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S)
    (f : Bool) (horder : bit S f 19≤bit S f 18) :
    S.card+omitted S f≤13 ∧
      (S.card+omitted S f=13 →
        bit S f 0=1 ∧ bit S f 1=1 ∧ bit S f 4=1 ∧ bit S f 5=1) := by
  have h0 := valid S hS f 0
  have h1 := valid S hS f 1
  have h2 := valid S hS f 2
  have ha := across S hS f 0
  have hb := across S hS f 1
  have hu0 := bit_bound S f 18
  have hu1 := bit_bound S f 19
  have hcases : (bit S f 18=0 ∧ bit S f 19=0) ∨
      (bit S f 18=1 ∧ bit S f 19=0) ∨ (bit S f 18=1 ∧ bit S f 19=1) := by omega
  rcases hcases with ⟨he,ho⟩ | ⟨he,ho⟩ | ⟨he,ho⟩
  · rw [he,ho] at h0 h1 h2
    have h := ClosedHighCycle.zero_hub_score _ _ _ h0 h1 h2
    have hs := score S f
    rw [he,ho] at hs
    exact ⟨by omega,by omega⟩
  · rw [he,ho] at h0 h1 h2
    have hh := triple S hS f 8 18 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have hhub : (cell S f 1).leafLeft+(cell S f 2).leafLeft+1≤2 := by
      dsimp [cell]
      omega
    have h := one_hub_block _ _ _ h0 h1 h2 ha hb hhub
    have hs := score S f
    rw [he,ho] at hs
    exact ⟨by omega,by omega⟩
  · rw [he,ho] at h0 h1 h2
    have h := two_hub_block _ _ _ h0 h1 h2 ha hb
    have hs := score S f
    rw [he,ho] at hs
    refine ⟨by omega,?_⟩
    intro ht
    have hh := h.2 (by omega)
    have hl := two_hub_tight _ h0 hh.1
    have hr := two_hub_tight _ h2 hh.2.2
    exact ⟨hl.2.2.2.1,hl.2.2.2.2,hr.2.2.2.1,hr.2.2.2.2⟩

/-- An actual open core has score at most thirteen. Only a selection
containing both internally matched boundary H pairs can reach thirteen. -/
theorem local_bound (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) :
    S.card+omitted S false≤13 ∧
      (S.card+omitted S false=13 → 0∈S ∧ 1∈S ∧ 4∈S ∧ 5∈S) := by
  by_cases h : bit S false 19≤bit S false 18
  · have hh := oriented_cap S hS false h
    exact ⟨hh.1,by
      intro ht
      have hp := hh.2 ht
      simpa [bit,iota] using hp⟩
  · have he : bit S true 19≤bit S true 18 := by
      simpa [bit,iota,reflection] using (Nat.le_of_lt (Nat.lt_of_not_ge h))
    have hh := oriented_cap S hS true he
    rw [omitted_reflection] at hh
    refine ⟨hh.1,?_⟩
    intro ht
    have hp := hh.2 ht
    simpa [bit,iota,reflection,and_comm,and_left_comm,and_assoc] using hp

variable {I : Type} [Fintype I] [DecidableEq I]

def slice (S : Finset (I × Fin 20)) (i : I) : Finset (Fin 20) :=
  Finset.univ.filter (fun v => (i,v)∈S)

def omissions (S : Finset (I × Fin 20)) : ℕ := ∑ i : I, omitted (slice S i) false

private theorem slice_independent (e : Equiv.Perm I) (S : Finset (I × Fin 20))
    (hS : IsKIndependent (LongCoreWord.graph e) 2 S) (i : I) :
    IsKIndependent graph 2 (slice S i) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro c hc a ha b hb hca hcb
  exact congrArg Prod.snd ((SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hS
    (i,c) (Finset.mem_filter.mp hc).2 (i,a) (Finset.mem_filter.mp ha).2
    (i,b) (Finset.mem_filter.mp hb).2 (Or.inl ⟨rfl,hca⟩) (Or.inl ⟨rfl,hcb⟩))

/-- Exceptional score-thirteen cells cannot be adjacent across the actual
H5--H0 seam. This includes a fixed index, so singleton restoration is kept. -/
theorem exceptional_exclusion (e : Equiv.Perm I) (S : Finset (I × Fin 20))
    (hS : IsKIndependent (LongCoreWord.graph e) 2 S) (i : I) :
    ¬ ( (slice S i).card+omitted (slice S i) false=13 ∧
        (slice S (e i)).card+omitted (slice S (e i)) false=13) := by
  rintro ⟨hi,hj⟩
  have hx := (local_bound _ (slice_independent e S hS i)).2 hi
  have hy := (local_bound _ (slice_independent e S hS (e i))).2 hj
  have he := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hS
    (i,5) (Finset.mem_filter.mp hx.2.2.2).2
    (i,4) (Finset.mem_filter.mp hx.2.2.1).2
    (e i,0) (Finset.mem_filter.mp hy.1).2
    (Or.inl ⟨rfl,by change LongCoreWord.insideAdj 5 4; decide +kernel⟩)
    (Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩))
  have hv := congrArg (fun x : I × Fin 20 => x.2) he
  exact (by decide : (4 : Fin 20)≠0) hv

/-- The all-size score upper bound is obtained by summing actual local
scores and the permutation exclusion, rather than enumerating lengths. -/
theorem score_bound (e : Equiv.Perm I) (S : Finset (I × Fin 20))
    (hS : IsKIndependent (LongCoreWord.graph e) 2 S) :
    S.card+omissions S≤12*Fintype.card I+Fintype.card I/2 := by
  classical
  let a : I → ℕ := fun i => if (slice S i).card+omitted (slice S i) false=13 then 1 else 0
  have hc : ∀ i, (slice S i).card+omitted (slice S i) false≤12+a i := by
    intro i
    have hh := (local_bound _ (slice_independent e S hS i)).1
    dsimp [a]
    split_ifs <;> omega
  have hx : ∀ i, a i+a (e i)≤1 := by
    intro i
    have hh := exceptional_exclusion e S hS i
    dsimp [a]
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
  have ha := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hx i)
  have he := Equiv.sum_comp e a
  rw [Finset.sum_add_distrib] at ha
  rw [he] at ha
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at ha
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
  have hcard := ClosedModule.card_fibers S
  change S.card=∑ i : I, (slice S i).card at hcard
  rw [← hcard] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  dsimp [omissions]
  omega

/-- The separated word (AB)^floor(k/2), with a final B at odd length. -/
def cyclicWord {k : ℕ} (i : Fin k) : Bool := decide (i.val%2=0 ∧ i.val<2*(k/2))

theorem cyclicWord_separated (k : ℕ) :
    ∀ i : Fin k, ¬ (cyclicWord i=true ∧ cyclicWord (finRotate k i)=true) := by
  intro i
  have hk : k≠0 := by have := i.isLt; omega
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simp only [cyclicWord,decide_eq_true_eq]
  rw [coe_finRotate]
  split_ifs with h
  · subst i
    simp only [Fin.val_last]
    omega
  · omega

/-- There are exactly floor(k/2) actual A cells. -/
theorem cyclicWord_count (k : ℕ) :
    (Finset.univ.filter (fun i : Fin k => cyclicWord i=true)).card=k/2 := by
  classical
  let A := Finset.univ.filter (fun i : Fin k => cyclicWord i=true)
  have hf : ∀ j : Fin (k/2), 2*j.val<k := by
    intro j
    have := j.isLt
    omega
  have hc : (Finset.univ : Finset (Fin (k/2))).card=A.card := by
    apply Finset.card_bij (fun j _ => (⟨2*j.val,hf j⟩ : Fin k))
    · intro j hj
      simp [A,cyclicWord]
    · intro i hi j hj he
      apply Fin.ext
      have hval := congrArg Fin.val he
      change 2*i.val=2*j.val at hval
      omega
    · intro i hi
      have hm := (Finset.mem_filter.mp hi).2
      simp only [cyclicWord,decide_eq_true_eq] at hm
      refine ⟨⟨i.val/2,by omega⟩,by simp,?_⟩
      apply Fin.ext
      dsimp
      omega
  simpa [A] using hc.symm

private theorem word_omitted (kind : Bool) :
    omitted (Finset.univ.filter (LongCoreWord.selected kind)) false=
      if kind then 1 else 2 := by
  cases kind <;> decide +kernel

private theorem word_score (word : I → Bool) :
    (LongCoreWord.selectedSet word).card+omissions (LongCoreWord.selectedSet word)=
      12*Fintype.card I+(Finset.univ.filter (fun i => word i=true)).card := by
  classical
  have hslice (i : I) : slice (LongCoreWord.selectedSet word) i=
      Finset.univ.filter (LongCoreWord.selected (word i)) := by
    ext v
    simp [slice,LongCoreWord.selectedSet]
  have hc := LongCoreWord.selectedSet_card word
  dsimp [omissions]
  simp_rw [hslice,word_omitted]
  rw [hc,← Finset.sum_add_distrib]
  have he (i : I) : (if word i then 12 else 10)+(if word i then 1 else 2)=
      12+(if word i=true then 1 else 0) := by cases word i <;> decide
  simp_rw [he]
  simp [Finset.sum_add_distrib,Finset.sum_const,Nat.mul_comm]

/-- The exact all-length omission score is attained by the source A/B word;
all lengths, including zero and singleton, are handled symbolically. -/
theorem cyclic_score (k : ℕ) :
    (∀ S : Finset (Fin k × Fin 20), IsKIndependent (LongCoreWord.graph (finRotate k)) 2 S →
      S.card+omissions S≤12*k+k/2) ∧
    ∃ S : Finset (Fin k × Fin 20), IsKIndependent (LongCoreWord.graph (finRotate k)) 2 S ∧
      S.card+omissions S=12*k+k/2 := by
  classical
  constructor
  · intro S hS
    simpa using score_bound (finRotate k) S hS
  · refine ⟨LongCoreWord.selectedSet cyclicWord,?_,?_⟩
    · apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
      intro c hc a ha b hb hca hcb
      exact LongCoreWord.word_dissociates (finRotate k) cyclicWord (cyclicWord_separated k)
        c a b (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp ha).2
        (Finset.mem_filter.mp hb).2 hca hcb
    · rw [word_score,cyclicWord_count,Fintype.card_fin]

end D5.S3.Combinatorics.Graph.StarForming.LongCoreOmission
