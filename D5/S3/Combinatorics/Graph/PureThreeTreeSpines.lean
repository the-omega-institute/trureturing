/- GID: D5/S3/Combinatorics/Graph/PureThreeTreeSpines
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure 3-tree histories: the root is K₃, every other birth is one vertex, with precisely three older neighbours. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.RollingCliqueHistories
import D5.S3.Topology.GraphChainAveraging

compile_only_with_mathlib

/-! Pure 3-tree histories: the root is K₃, every other birth is one vertex,
with precisely three older neighbours. All three forward faces and all copy
indices are retained. A graph retraction projects every history onto its spine. -/
namespace Omega.PureThreeTree
open SimpleGraph Omega.GraphChains Omega.RollingCliques
open scoped BigOperators
noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n k : ℕ}

def previous (i : Fin (n+1)) : Fin (n+1) := ⟨i.val-1, (Nat.sub_le _ _).trans_lt i.isLt⟩

def Legal (i : Fin (n+1)) (f : Fin (n+1) → Finset (Fin 3)) : Prop :=
  (∑ j, if j < i then (f j).card else 0) = 3 ∧
  (∀ j, i ≤ j → f j = Finset.univ) ∧
  (∀ j, 0 < j.val → j < i → f j ⊆ {0}) ∧
  0 ∈ f (previous i)

structure History (n k : ℕ) where
  stage : Fin (n+1)
  step : Fin (n+1) → Step n 3 k
  root_step : step 0 = rootStep n 3 k
  beyond (i : Fin (n+1)) : stage < i → step i = rootStep n 3 k
  legal (i : Fin (n+1)) : i ≤ stage → 0 < i.val → Legal i (step i).1
  nested (j i l : Fin (n+1)) : i ≤ l → l ≤ stage → (step l).1 j ⊆ (step i).1 j

@[ext] theorem History.ext' {b c : History n k} (hs : b.stage = c.stage)
    (hf : b.step = c.step) : b = c := by
  cases b; cases c; cases hs; cases hf; rfl
instance : DecidableEq (History n k) := Classical.decEq _
instance : Fintype (History n k) := by
  have : Finite (History n k) := Finite.of_injective
    (fun b : History n k => (b.stage,b.step))
    (fun _ _ h => History.ext' (congrArg Prod.fst h) (congrArg Prod.snd h))
  exact Fintype.ofFinite _

def History.initial : History n k where
  stage := 0
  step := fun _ => rootStep n 3 k
  root_step := rfl
  beyond _ _ := rfl
  legal i hi hp := False.elim (by have : i.val ≤ 0 := hi; omega)
  nested _ _ _ _ _ := Finset.Subset.rfl

def History.IsPrefix (b c : History n k) : Prop :=
  b.stage ≤ c.stage ∧ ∀ i, i ≤ b.stage → b.step i = c.step i

theorem History.IsPrefix.eq_of_stage_eq {b c : History n k}
    (h : b.IsPrefix c) (he : b.stage = c.stage) : b = c := by
  apply History.ext' he
  funext i
  by_cases hi : i ≤ b.stage
  · exact h.2 i hi
  · exact (b.beyond i (lt_of_not_ge hi)).trans (c.beyond i (he ▸ lt_of_not_ge hi)).symm

def History.prefix (b : History n k) (t : Fin (n+1)) (ht : t ≤ b.stage) : History n k where
  stage := t
  step i := if i ≤ t then b.step i else rootStep n 3 k
  root_step := by simp [b.root_step]
  beyond _ hi := ite_eq_right (not_le_of_gt hi)
  legal i hi hp := by simpa [hi] using b.legal i (hi.trans ht) hp
  nested j i l hil hl := by simpa [hl, hil.trans hl] using b.nested j i l hil (hl.trans ht)

theorem History.prefix_spec (b : History n k) (t : Fin (n+1)) (ht : t ≤ b.stage) :
    (b.prefix t ht).IsPrefix b := ⟨ht, fun _ hi => ite_eq_left hi⟩

def data : RollingData (History n k) (Fin 3) where
  depth b := b.stage.val
  ancestor := History.IsPrefix
  refl b := ⟨le_rfl, fun _ _ => rfl⟩
  trans h₁ h₂ := ⟨h₁.1.trans h₂.1, fun i hi => (h₁.2 i hi).trans (h₂.2 i (hi.trans h₁.1))⟩
  depth_lt h hne := lt_of_le_of_ne h.1 (fun he => hne (h.eq_of_stage_eq (Fin.ext he)))
  comparable := by
    intro a b c h₁ h₂
    rcases le_total a.stage b.stage with h | h
    · exact Or.inl ⟨h, fun i hi => (h₁.2 i hi).trans (h₂.2 i (hi.trans h)).symm⟩
    · exact Or.inr ⟨h, fun i hi => (h₂.2 i hi).trans (h₁.2 i (hi.trans h)).symm⟩
  retain a b := ((b.step b.stage).1 a.stage : Set (Fin 3))
  nested := by
    intro a b c h x hx
    change x ∈ (b.step b.stage).1 a.stage
    rw [h.2 b.stage le_rfl]
    exact c.nested _ _ _ h.1 le_rfl hx
  root := History.initial
  earlier b := by
    by_cases hb : b.stage = 0
    · exact Or.inl (History.IsPrefix.eq_of_stage_eq (b := History.initial) (c := b)
        ⟨Fin.zero_le _, fun i hi => by have he : i = 0 := le_antisymm hi (Fin.zero_le _); simp [he, History.initial, b.root_step]⟩ hb.symm).symm
    · have hp : 0 < b.stage.val := Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))
      have ha : previous b.stage < b.stage := by change b.stage.val-1 < b.stage.val; omega
      exact Or.inr ⟨b.prefix _ ha.le,b.prefix_spec _ ha.le,
        fun he => ha.ne (congrArg History.stage he),0,(b.legal _ le_rfl hp).2.2.2⟩

/-- Only root histories carry three vertices; each later history carries one. -/
def Vertex (n k : ℕ) := {v : History n k × Fin 3 // v.1.stage = 0 ∨ v.2 = 0}
instance : Fintype (Vertex n k) := by
  classical
  unfold Vertex
  infer_instance
instance : DecidableEq (Vertex n k) := Classical.decEq _

def graph (n k : ℕ) : SimpleGraph (Vertex n k) := (rolling (data : RollingData (History n k) (Fin 3))).comap Subtype.val

def depth (v : Vertex n k) : ℕ := v.val.1.stage.val
def pre (u v : Vertex n k) : Prop := u.val.1.IsPrefix v.val.1

def root (a : Fin 3) : Vertex n k := ⟨(History.initial,a),Or.inl rfl⟩
def birth (b : History n k) : Vertex n k := ⟨(b,0),Or.inr rfl⟩

theorem History.initial_prefix (b : History n k) : (History.initial).IsPrefix b := by
  refine ⟨Fin.zero_le _,fun i hi => ?_⟩
  have he : i = 0 := le_antisymm hi (Fin.zero_le _)
  simp [he, History.initial,b.root_step]

theorem History.stage_zero {b : History n k} (h : b.stage = 0) : b = History.initial :=
  (History.initial_prefix b).eq_of_stage_eq h.symm |>.symm

/-- The actual older neighbours correspond bijectively to the three retained parents. -/
def parents (b : History n k) : Finset (Fin (n+1) × Fin 3) :=
  Finset.univ.filter (fun p => p.1 < b.stage ∧ p.2 ∈ (b.step b.stage).1 p.1)

theorem parents_card (b : History n k) (hb : 0 < b.stage.val) : (parents b).card = 3 := by
  classical
  rw [parents, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  have he (j : Fin (n+1)) :
      (∑ x : Fin 3, if j < b.stage ∧ x ∈ (b.step b.stage).1 j then 1 else 0) =
        if j < b.stage then ((b.step b.stage).1 j).card else 0 := by
    by_cases h : j < b.stage <;> simp [h]
  simpa only [he] using (b.legal _ le_rfl hb).1

def History.reclone (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) (b : History n k) : History n k where
  stage := b.stage
  step t := if t = i ∧ i ≤ b.stage then ((b.step t).1, σ (b.step t).2) else b.step t
  root_step := by simpa [hi.symm] using b.root_step
  beyond t ht := by
    simp [show ¬(t = i ∧ i ≤ b.stage) from fun h => ht.not_ge (h.1.symm ▸ h.2), b.beyond t ht]
  legal t ht hp := by
    split <;> exact b.legal t ht hp
  nested j t l htl hl := by
    split <;> split <;> exact b.nested j t l htl hl

private theorem History.reclone_symm (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) (b : History n k) : (b.reclone i hi σ).reclone i hi σ.symm = b := by
  refine History.ext' (b := (b.reclone i hi σ).reclone i hi σ.symm) (c := b) rfl ?_
  funext t
  change (if t = i ∧ i ≤ b.stage then (((b.reclone i hi σ).step t).1,
    σ.symm ((b.reclone i hi σ).step t).2) else (b.reclone i hi σ).step t) = _
  split
  · rename_i ht
    simp [History.reclone, ht]
  · rename_i ht
    simp [History.reclone, ht]

theorem History.reclone_prefix (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) {b c : History n k} :
    (b.reclone i hi σ).IsPrefix (c.reclone i hi σ) ↔ b.IsPrefix c := by
  have forward (τ : Equiv.Perm (Fin (k + 1))) {b c : History n k} (h : b.IsPrefix c) :
      (b.reclone i hi τ).IsPrefix (c.reclone i hi τ) := by
    refine ⟨h.1, fun t ht => ?_⟩
    change t ≤ b.stage at ht
    have he := h.2 t ht
    by_cases hit : t = i
    · subst t
      simp [History.reclone, ht, ht.trans h.1, he]
    · simp [History.reclone, hit, he]
  exact ⟨fun h => by simpa only [History.reclone_symm] using forward σ.symm h, forward σ⟩

def clonePerm (i : Fin (n + 1)) (hi : i ≠ 0) (σ : Equiv.Perm (Fin (k + 1))) :
    Equiv.Perm (History n k × Fin 3) where
  toFun v := (v.1.reclone i hi σ, v.2)
  invFun v := (v.1.reclone i hi σ.symm, v.2)
  left_inv v := Prod.ext (History.reclone_symm i hi σ _) rfl
  right_inv v := Prod.ext (History.reclone_symm i hi σ.symm _) rfl

theorem clonePerm_adj (i : Fin (n + 1)) (hi : i ≠ 0) (σ : Equiv.Perm (Fin (k + 1)))
    (u v : History n k × Fin 3) :
    (rolling data).Adj (clonePerm i hi σ u) (clonePerm i hi σ v) ↔
      (rolling data).Adj u v := by
  have e (b c : History n k) : b.reclone i hi σ = c.reclone i hi σ ↔ b = c := by
    constructor
    · intro hb
      simpa only [History.reclone_symm] using congrArg (History.reclone i hi σ.symm) hb
    · exact congrArg _
  have h (b : History n k) (t : Fin (n + 1)) :
      ((b.reclone i hi σ).step t).1 = (b.step t).1 := by
    simp only [History.reclone]
    split <;> rfl
  change (clonePerm i hi σ u ≠ clonePerm i hi σ v ∧ _) ↔ _
  rw [(clonePerm i hi σ).injective.ne_iff]
  change (_ ∧ ((u.1.reclone i hi σ = v.1.reclone i hi σ) ∨
    ((u.1.reclone i hi σ).IsPrefix (v.1.reclone i hi σ) ∧
      u.2 ∈ ((v.1.reclone i hi σ).step v.1.stage).1 u.1.stage) ∨
    ((v.1.reclone i hi σ).IsPrefix (u.1.reclone i hi σ) ∧
      v.2 ∈ ((u.1.reclone i hi σ).step u.1.stage).1 v.1.stage))) ↔ _
  simp only [e, History.reclone_prefix, h]
  rfl


def History.Break (b c : History n k) (i : Fin (n + 1)) : Prop :=
  i ≤ b.stage ∧ (c.stage < i ∨ b.step i ≠ c.step i)

theorem History.exists_break {b c : History n k} (h : ¬b.IsPrefix c) :
    ∃ i, b.Break c i := by
  classical
  by_contra! hn
  apply h
  refine ⟨?_, ?_⟩
  · exact le_of_not_gt fun ht => hn b.stage ⟨le_rfl, Or.inl ht⟩
  · exact fun i hi => not_ne_iff.mp fun he => hn i ⟨hi, Or.inr he⟩

noncomputable def History.firstBreak {b c : History n k} (h : ¬b.IsPrefix c) : Fin (n + 1) :=
  letI := Classical.propDecidable
  ((Finset.univ : Finset (Fin (n + 1))).filter (b.Break c)).min'
    (by obtain ⟨i, hi⟩ := exists_break h; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)

theorem History.firstBreak_mem {b c : History n k} (h : ¬b.IsPrefix c) :
    b.Break c (firstBreak h) := by
  classical
  unfold firstBreak
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

theorem History.firstBreak_min {b c : History n k} (h : ¬b.IsPrefix c)
    {i : Fin (n + 1)} (hi : b.Break c i) : firstBreak h ≤ i := by
  classical
  unfold firstBreak
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

theorem History.firstBreak_pos {b c : History n k} (h : ¬b.IsPrefix c) :
    0 < (firstBreak h).val := by
  have hh := (firstBreak_mem h).2
  by_contra! hl
  have he : firstBreak h = 0 := Fin.ext (Nat.eq_zero_of_le_zero hl)
  simp [he, b.root_step, c.root_step] at hh

theorem History.firstBreak_eq {b d c : History n k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) :
    firstBreak hb = firstBreak hd := by
  have hm := firstBreak_mem hb
  have ha : d.Break c (firstBreak hb) := by
    exact ⟨hm.1.trans h.1, by rw [← h.2 _ hm.1]; exact hm.2⟩
  have hle := firstBreak_min hd ha
  have hh := firstBreak_mem hd
  have hh' : firstBreak hd ≤ b.stage := hle.trans hm.1
  have hz : b.Break c (firstBreak hd) := by
    exact ⟨hh', by rw [h.2 _ hh']; exact hh.2⟩
  exact le_antisymm (firstBreak_min hb hz) hle

def Fin.previous (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩

theorem History.beforeBreak {b c : History n k} (h : ¬b.IsPrefix c)
    {i : Fin (n + 1)} (hi : i < firstBreak h) : i ≤ c.stage ∧ b.step i = c.step i := by
  have hb := hi.le.trans (firstBreak_mem h).1
  constructor
  · exact le_of_not_gt fun hh => hi.not_ge (firstBreak_min h ⟨hb, Or.inl hh⟩)
  · exact not_ne_iff.mp fun hh => hi.not_ge (firstBreak_min h ⟨hb, Or.inr hh⟩)

theorem History.previous_lt_break {b c : History n k} (h : ¬b.IsPrefix c) :
    Fin.previous (firstBreak h) < firstBreak h := by
  have hh := firstBreak_pos h
  change (firstBreak h).val - 1 < (firstBreak h).val
  omega

def History.breakBlock {b c : History n k} (h : ¬b.IsPrefix c) : History n k :=
  b.prefix (firstBreak h) (firstBreak_mem h).1

theorem History.breakBlock_eq {b d c : History n k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) :
    breakBlock hb = breakBlock hd := by
  have he := firstBreak_eq h hb hd
  apply History.ext' he
  funext i
  simp only [breakBlock, History.prefix, ← he]
  split
  · rename_i hi
    exact h.2 _ (hi.trans (firstBreak_mem hb).1)
  · rfl

def History.collapseVertex (a : History n k) (_h : 0 < a.stage.val) :
    History n k × Fin 3 :=
  (a.prefix (Fin.previous a.stage) (Nat.sub_le _ _),0)

noncomputable def spineMap (c : History n k) (v : History n k × Fin 3) :
    History n k × Fin 3 := by
  classical
  exact if h : v.1.IsPrefix c then v else
    History.collapseVertex (History.breakBlock h) (History.firstBreak_pos h)

theorem spineMap_fixed {c : History n k} {v : History n k × Fin 3}
    (h : v.1.IsPrefix c) : spineMap c v = v := by
  simp [spineMap, h]

theorem spineMap_on_spine (c : History n k) (v : History n k × Fin 3) :
    (spineMap c v).1.IsPrefix c := by
  classical
  by_cases h : v.1.IsPrefix c
  · rwa [spineMap_fixed h]
  rw [spineMap, dite_eq_right h]
  have hm := History.previous_lt_break h
  have hc := (History.beforeBreak h hm).1
  refine ⟨hc, fun i hi => ?_⟩
  have hb : i < History.firstBreak h := hi.trans_lt hm
  have hi' : i ≤ Fin.previous (History.firstBreak h) := hi
  simpa [History.collapseVertex, History.breakBlock, History.prefix, hi', hb.le] using
    (History.beforeBreak h hb).2

theorem spineMap_eq_of_outside {b d c : History n k} (h : b.IsPrefix d)
    (hb : ¬b.IsPrefix c) (hd : ¬d.IsPrefix c) (x y : Fin 3) :
    spineMap c (b,x) = spineMap c (d,y) := by
  simp only [spineMap, dite_eq_right hb, dite_eq_right hd]
  have e : (⟨History.breakBlock hb, History.firstBreak_pos hb⟩ :
      {a : History n k // 0 < a.stage.val}) =
      ⟨History.breakBlock hd, History.firstBreak_pos hd⟩ :=
    Subtype.ext (History.breakBlock_eq h hb hd)
  exact congrArg (fun a => History.collapseVertex a.val a.property) e

theorem spineMap_edge (c : History n k) {u v : History n k × Fin 3}
    (h : (rolling data).Adj u v) :
    spineMap c u = spineMap c v ∨ (rolling data).Adj (spineMap c u) (spineMap c v) := by
  classical
  let D : RollingData (History n k) (Fin 3) := data
  have earlier (x y : History n k × Fin 3) (hxy : (rolling D).Adj x y)
      (hpre : x.1.IsPrefix y.1) :
      spineMap c x = spineMap c y ∨ (rolling D).Adj (spineMap c x) (spineMap c y) := by
    by_cases hx : x.1.IsPrefix c
    · rw [spineMap_fixed hx]
      by_cases hy : y.1.IsPrefix c
      · rw [spineMap_fixed hy]
        exact Or.inr hxy
      · have hp : x.1.stage < History.firstBreak hy := by
          by_contra! hn
          have hm := (History.firstBreak_mem hy).2
          rw [← hpre.2 _ hn, hx.2 _ hn] at hm
          exact hm.elim (fun hh => hh.not_ge (hn.trans hx.1)) (fun hh => hh rfl)
        rw [spineMap, dite_eq_right hy]
        let a := History.breakBlock hy
        let d := History.collapseVertex a (History.firstBreak_pos hy)
        change x = d ∨ (rolling D).Adj x d
        by_cases he : x = d
        · exact Or.inl he
        · apply Or.inr
          refine ⟨he, ?_⟩
          by_cases hb : x.1 = d.1
          · exact Or.inl hb
          · refine Or.inr (Or.inl ⟨?_, ?_⟩)
            · have hc : x.1.stage ≤ d.1.stage := by
                change x.1.stage.val ≤ (History.firstBreak hy).val - 1
                have hp' : x.1.stage.val < (History.firstBreak hy).val := hp
                omega
              refine ⟨hc, fun i hi => ?_⟩
              have hi' := hi.trans hp.le
              have hdi := hi.trans hc
              change x.1.step i =
                if i ≤ d.1.stage then (if i ≤ History.firstBreak hy then y.1.step i else _) else _
              rw [ite_eq_left hdi, ite_eq_left hi']
              exact hpre.2 _ hi
            · have hretain := (rolling_earlier D hxy hpre.1).2.resolve_left (fun hz => by
                have hp' := (History.firstBreak_mem hy).1
                exact hp.not_ge (hp'.trans (congrArg History.stage hz).ge))
              have hprefix (b c : History n k) (hbc : b.IsPrefix c) :
                  D.ancestor b c := hbc
              have hdy : d.1.IsPrefix y.1 :=
                D.trans (History.prefix_spec a (Fin.previous a.stage) (Nat.sub_le _ _))
                  (History.prefix_spec y.1 (History.firstBreak hy) (History.firstBreak_mem hy).1)
              exact D.nested (hprefix _ _ hdy) hretain
    · have hy : ¬y.1.IsPrefix c := fun hy => hx (D.trans hpre hy)
      exact Or.inl (spineMap_eq_of_outside hpre hx hy x.2 y.2)
  rcases h.2 with hh | hh | hh
  · exact earlier u v h (hh ▸ D.refl u.1)
  · exact earlier u v h hh.1
  · exact (earlier v u h.symm hh.1).elim (fun he => Or.inl he.symm) (fun he => Or.inr he.symm)

theorem spineMap_stable {b c : History n k} (h : b.IsPrefix c)
    (t : Fin (n + 1)) (ht : t.val = b.stage.val + 1) (htc : t ≤ c.stage)
    (v : History n k × Fin 3) (hv : ¬(c.prefix t htc).IsPrefix v.1) :
    spineMap b v = spineMap c v := by
  classical
  let D : RollingData (History n k) (Fin 3) := data
  by_cases h₁ : v.1.IsPrefix b
  · rw [spineMap_fixed h₁, spineMap_fixed (D.trans h₁ h)]
  have hmin := (History.firstBreak_mem h₁).1
  let i := History.firstBreak h₁
  have hit : i ≤ t := by
    rcases le_total v.1.stage t with hv' | hv'
    · exact hmin.trans hv'
    · exact History.firstBreak_min h₁ ⟨hv', Or.inl (show b.stage < t from Nat.lt_of_succ_le ht.ge)⟩
  have hbefore (s : Fin (n + 1)) (hs : s < i) : s ≤ c.stage ∧ v.1.step s = c.step s := by
    obtain ⟨hh, he⟩ := History.beforeBreak h₁ hs
    exact ⟨hh.trans h.1, he.trans (h.2 s hh)⟩
  have hincompat : v.1.Break c i := by
    refine ⟨hmin, ?_⟩
    by_cases hlt : i < t
    · have hi : i ≤ b.stage := by
        change i.val < t.val at hlt
        exact show i.val ≤ b.stage.val by omega
      have hh := (History.firstBreak_mem h₁).2.resolve_left (not_lt_of_ge hi)
      exact Or.inr fun he => hh (he.trans (h.2 i hi).symm)
    · have he : i = t := le_antisymm hit (le_of_not_gt hlt)
      apply Or.inr
      intro har
      refine hv ⟨he ▸ hmin, fun s hs => ?_⟩
      change s ≤ t at hs
      change (if s ≤ t then c.step s else _) = v.1.step s
      rw [ite_eq_left hs]
      rcases lt_or_eq_of_le hs with hlt' | rfl
      · exact (hbefore s (he ▸ hlt')).2.symm
      · exact (he ▸ har).symm
  have h₂ : ¬v.1.IsPrefix c := fun g =>
    hincompat.2.elim (fun hh => hh.not_ge (hmin.trans g.1)) (fun hh => hh (g.2 i hmin))
  have eq : History.firstBreak h₁ = History.firstBreak h₂ := by
    refine le_antisymm (le_of_not_gt fun hj => ?_) (History.firstBreak_min h₂ hincompat)
    have g := hbefore _ hj
    exact (History.firstBreak_mem h₂).2.elim (fun hh => hh.not_ge g.1) (fun hh => hh g.2)
  simp only [spineMap, dite_eq_right h₁, dite_eq_right h₂]
  have equalBlock : History.breakBlock h₁ = History.breakBlock h₂ :=
    History.ext' eq (by funext s; simp [History.breakBlock, History.prefix, eq])
  have e : (⟨History.breakBlock h₁, History.firstBreak_pos h₁⟩ :
      {a : History n k // 0 < a.stage.val}) =
      ⟨History.breakBlock h₂, History.firstBreak_pos h₂⟩ :=
    Subtype.ext equalBlock
  exact congrArg (fun a => History.collapseVertex a.val a.property) e

def retract (c : History n k) (v : Vertex n k) : Vertex n k := by
  classical
  refine ⟨spineMap c v.val, ?_⟩
  by_cases h : v.val.1.IsPrefix c
  · rw [spineMap_fixed h]
    exact v.property
  · rw [spineMap, dite_eq_right h]
    exact Or.inr rfl

theorem retract_fixed {c : History n k} {v : Vertex n k} (h : v.val.1.IsPrefix c) :
    retract c v = v := Subtype.ext (spineMap_fixed h)

theorem retract_spine (c : History n k) (v : Vertex n k) :
    (retract c v).val.1.IsPrefix c := spineMap_on_spine c v.val

theorem retract_edge (c : History n k) {u v : Vertex n k} (h : (graph n k).Adj u v) :
    retract c u = retract c v ∨ (graph n k).Adj (retract c u) (retract c v) :=
  (spineMap_edge c h).imp Subtype.ext id

def clone (i : Fin (n+1)) (hi : i ≠ 0) (σ : Equiv.Perm (Fin (k+1))) :
    Equiv.Perm (Vertex n k) where
  toFun v := ⟨clonePerm i hi σ v.val,v.property⟩
  invFun v := ⟨clonePerm i hi σ.symm v.val,v.property⟩
  left_inv v := Subtype.ext ((clonePerm i hi σ).left_inv v.val)
  right_inv v := Subtype.ext ((clonePerm i hi σ).right_inv v.val)

theorem clone_adj (i : Fin (n+1)) (hi : i ≠ 0) (σ : Equiv.Perm (Fin (k+1)))
    (u v : Vertex n k) :
    (graph n k).Adj (clone i hi σ u) (clone i hi σ v) ↔ (graph n k).Adj u v :=
  clonePerm_adj i hi σ u.val v.val

theorem short_walk (a : Fin 3) (v : Vertex n k) :
    ∃ p : (graph n k).Walk (root a) v, p.length ≤ depth v + 1 := by
  generalize hd : depth v = m
  induction m using Nat.strong_induction_on generalizing v with
  | h m ih =>
    by_cases hz : v.val.1.stage = 0
    · by_cases he : root a = v
      · subst v
        exact ⟨Walk.nil,by simp⟩
      · have ed : (graph n k).Adj (root a) v :=
          ⟨fun h => he (Subtype.ext h),Or.inl (History.stage_zero hz).symm⟩
        exact ⟨Walk.cons ed Walk.nil,by simp⟩
    · have hp : 0 < v.val.1.stage.val := Nat.pos_of_ne_zero (fun h => hz (Fin.ext h))
      let b := v.val.1
      have hlt : previous b.stage < b.stage := Nat.sub_lt hp (by decide)
      let u := birth (b.prefix _ hlt.le)
      have hdep : depth u < m := by
        change (previous b.stage).val < m
        rw [← hd]
        exact hlt
      obtain ⟨p,hp'⟩ := ih _ hdep u rfl
      have ed : (graph n k).Adj u v :=
        ⟨fun h => hlt.ne (congrArg (fun z => z.1.stage) h),
          Or.inr (Or.inl ⟨b.prefix_spec _ hlt.le,(b.legal _ le_rfl hp).2.2.2⟩)⟩
      refine ⟨p.concat ed, ?_⟩
      simp only [Walk.length_concat]
      rw [← hd]
      change p.length + 1 ≤ b.stage.val+1
      change p.length ≤ b.stage.val-1+1 at hp'
      omega

theorem retract_support (v a b : Vertex n k) (c : Chains (Vertex n k))
    (hs : Supported (graph n k) c)
    (hn : ¬(pre a v ∧ pre b v ∧ (a=b ∨ (graph n k).Adj a b))) :
    pushChain (retract v.val.1) c (a,b)=0 := by
  classical
  unfold pushChain
  simp only [Finset.sum_apply,Pi.single_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : (a,b) = (retract v.val.1 e.1,retract v.val.1 e.2)
  · rw [ite_eq_left he]
    apply hs e
    intro ed
    apply hn
    have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    change a = _ at ha
    change b = _ at hb
    rw [ha,hb]
    exact ⟨retract_spine _ _,retract_spine _ _,retract_edge _ ed⟩
  · simp [he]

/-- Complete finite-depth localization on the pure duplication graph. The number
of copies is k+1. No bound on R from above, filling data, or symmetry assumption
is required of the input potential. -/
def History.copyMap {l : ℕ} (f : Fin (k+1) → Fin (l+1)) (hf : f 0=0)
    (b : History n k) : History n l where
  stage := b.stage
  step i := ((b.step i).1,f (b.step i).2)
  root_step := by simp [b.root_step,rootStep,hf]
  beyond i hi := by simp [b.beyond i hi,rootStep,hf]
  legal i hi hp := b.legal i hi hp
  nested j i t hit ht := b.nested j i t hit ht

theorem History.copyMap_prefix {l : ℕ} (f : Fin (k+1) → Fin (l+1)) (hf : f 0=0)
    {b c : History n k} (h : b.IsPrefix c) :
    (b.copyMap f hf).IsPrefix (c.copyMap f hf) :=
  ⟨h.1,fun i hi => by
    change ((b.step i).1,f (b.step i).2) = ((c.step i).1,f (c.step i).2)
    rw [h.2 i hi]⟩

def copyMap {l : ℕ} (f : Fin (k+1) → Fin (l+1)) (hf : f 0=0)
    (v : Vertex n k) : Vertex n l := ⟨(v.val.1.copyMap f hf,v.val.2),v.property⟩

theorem copyMap_edge {l : ℕ} (f : Fin (k+1) → Fin (l+1)) (hf : f 0=0)
    {u v : Vertex n k} (h : (graph n k).Adj u v) :
    (graph n l).Adj (copyMap f hf u) (copyMap f hf v) := by
  have hne : (copyMap f hf u).val ≠ (copyMap f hf v).val := by
    intro he
    have hs : u.val.1.stage=v.val.1.stage := congrArg (fun z => z.1.stage) he
    have hl := congrArg (fun z : History n l × Fin 3 => z.2) he
    change u.val.2=v.val.2 at hl
    have hp := (rolling_earlier data h hs.le).1
    exact h.1 (Prod.ext (hp.eq_of_stage_eq hs) hl)
  refine ⟨hne,?_⟩
  rcases h.2 with he | he | he
  · exact Or.inl (congrArg (History.copyMap f hf) he)
  · exact Or.inr (Or.inl ⟨History.copyMap_prefix f hf he.1,he.2⟩)
  · exact Or.inr (Or.inr ⟨History.copyMap_prefix f hf he.1,he.2⟩)

def forget (v : Vertex n k) : Vertex n 0 := copyMap (fun _ => 0) rfl v
def selectCopy (v : Vertex n 0) : Vertex n k := copyMap (fun _ => 0) rfl v

theorem forget_selectCopy (v : Vertex n 0) : forget (selectCopy (k := k) v)=v := by
  apply Subtype.ext
  apply Prod.ext
  · apply History.ext' (b := (forget (selectCopy (k := k) v)).val.1) (c := v.val.1) rfl
    funext i
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have h := (v.val.1.step i).2.isLt
      change 0 = (v.val.1.step i).2.val
      omega
  · rfl

theorem copyMap_root {l : ℕ} (f : Fin (k+1) → Fin (l+1)) (hf : f 0=0) (a : Fin 3) :
    copyMap (n := n) f hf (root a)=root a := by
  apply Subtype.ext
  apply Prod.ext
  · apply History.ext' (b := History.copyMap f hf History.initial) (c := History.initial) rfl
    funext i
    simp [History.copyMap,History.initial,rootStep,hf]
  · rfl

theorem graph_connected : (graph n k).Connected := by
  let : Nonempty (Vertex n k) := ⟨root 0⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨p,_⟩ := short_walk 0 u
  obtain ⟨q,_⟩ := short_walk 0 v
  exact p.reachable.symm.trans q.reachable

/-- The chain obstruction is realized by actual finite-dimensional Banach gains
using the repository's public canonical-gain theorem. -/
theorem equal_depth_edge_root {u v : Vertex n k} (h : (graph n k).Adj u v)
    (hd : depth u=depth v) : depth u=0 := by
  have hp := (rolling_earlier data h hd.le).1
  have he : u.val.1=v.val.1 := hp.eq_of_stage_eq (Fin.ext hd)
  by_contra hn
  have hu : u.val.2=0 := u.property.resolve_left (fun hz => hn (congrArg Fin.val hz))
  have hv : v.val.2=0 := v.property.resolve_left (fun hz => hn (hd.trans (congrArg Fin.val hz)))
  exact h.1 (Prod.ext he (hu.trans hv.symm))

theorem root_adj {a b : Fin 3} (h : a≠b) : (graph n k).Adj (root a) (root b) :=
  ⟨fun he => h (congrArg Prod.snd he),Or.inl rfl⟩

end
end Omega.PureThreeTree
