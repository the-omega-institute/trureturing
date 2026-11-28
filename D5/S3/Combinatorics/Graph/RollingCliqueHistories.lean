/- GID: D5/S3/Combinatorics/Graph/RollingCliqueHistories
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-sharp-four-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite trees of nested clique retention histories and their label and copy symmetries. -/

import OmegaBuild.Commands
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

compile_only_with_mathlib

/-! Omega original.

Finite trees of nested clique retention histories and their label and copy symmetries. -/

namespace Omega.RollingCliques

open SimpleGraph

open scoped BigOperators

noncomputable section

section RollingGraph

variable {B X : Type*} [Fintype B] [Fintype X]

/-- The ancestors of each block are linearly ordered, and each surviving
label at a descendant survives at every intermediate block. -/
structure RollingData (B X : Type*) where
  depth : B → ℕ
  ancestor : B → B → Prop
  refl (b : B) : ancestor b b
  trans {a b c : B} : ancestor a b → ancestor b c → ancestor a c
  depth_lt {a b : B} : ancestor a b → a ≠ b → depth a < depth b
  comparable {a b c : B} : ancestor a c → ancestor b c → ancestor a b ∨ ancestor b a
  retain : B → B → Set X
  nested {a b c : B} : ancestor b c → retain a c ⊆ retain a b
  root : B
  earlier (b : B) : b = root ∨ ∃ a, ancestor a b ∧ a ≠ b ∧ (retain a b).Nonempty

def rolling (D : RollingData B X) : SimpleGraph (B × X) where
  Adj u v := u ≠ v ∧ (u.1 = v.1 ∨
    (D.ancestor u.1 v.1 ∧ u.2 ∈ D.retain u.1 v.1) ∨
    (D.ancestor v.1 u.1 ∧ v.2 ∈ D.retain v.1 u.1))
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.elim (fun he => Or.inl he.symm)
      (fun hr => Or.inr (Or.symm hr))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem rolling_earlier (D : RollingData B X) {u v : B × X}
    (huv : (rolling D).Adj u v) (hd : D.depth u.1 ≤ D.depth v.1) :
    D.ancestor u.1 v.1 ∧ (u.1 = v.1 ∨ u.2 ∈ D.retain u.1 v.1) := by
  by_cases he : u.1 = v.1
  · exact ⟨he ▸ D.refl u.1, Or.inl he⟩
  rcases huv.2 with h | h | h
  · exact (he h).elim
  · exact ⟨h.1, Or.inr h.2⟩
  · exact ((D.depth_lt h.1 (fun h' => he h'.symm)).not_ge hd).elim

theorem rolling_clique (D : RollingData B X) (v : B × X) :
    (rolling D).IsClique {u | D.depth u.1 ≤ D.depth v.1 ∧ (rolling D).Adj u v} := by
  intro u hu z hz hne
  have hu' := rolling_earlier D hu.2 hu.1
  have hz' := rolling_earlier D hz.2 hz.1
  refine ⟨hne, ?_⟩
  by_cases he : u.1 = z.1
  · exact Or.inl he
  rcases D.comparable hu'.1 hz'.1 with h | h
  · have hv : u.1 ≠ v.1 := by
      intro hh
      exact (D.depth_lt h he).not_ge (hh ▸ hz.1)
    exact Or.inr (Or.inl ⟨h, D.nested hz'.1 (hu'.2.resolve_left hv)⟩)
  · have hv : z.1 ≠ v.1 := by
      intro hh
      exact (D.depth_lt h (fun h' => he h'.symm)).not_ge (hh ▸ hu.1)
    exact Or.inr (Or.inr ⟨h, D.nested hu'.1 (hz'.2.resolve_left hv)⟩)

theorem rolling_connected (D : RollingData B X) (x₀ : X) :
    (rolling D).Connected := by
  let o : B × X := (D.root, x₀)
  have go (v : B × X) : (rolling D).Reachable o v := by
    generalize hd : D.depth v.1 = m
    induction m using Nat.strong_induction_on generalizing v with
    | h m ih =>
      rcases D.earlier v.1 with hb | ⟨a, ha, hne, x, hx⟩
      · by_cases h : o = v
        · exact h ▸ SimpleGraph.Reachable.refl o
        · have hed : (rolling D).Adj o v := ⟨h, Or.inl hb.symm⟩
          exact hed.reachable
      · have ha' : D.depth (a, x).1 < m := by rw [← hd]; exact D.depth_lt ha hne
        have hed : (rolling D).Adj (a, x) v := ⟨fun h => hne (congrArg Prod.fst h),
          Or.inr (Or.inl ⟨ha, hx⟩)⟩
        exact (ih _ ha' (a, x) rfl).trans hed.reachable
  letI : Nonempty (B × X) := ⟨o⟩
  exact ⟨fun u v => (go u).symm.trans (go v)⟩

theorem rolling_short_walk {B X : Type*} (D : RollingData B X) (a : X) (v : B × X) :
    ∃ p : (rolling D).Walk (D.root, a) v, p.length ≤ D.depth v.1 + 1 := by
  let o : B × X := (D.root, a)
  generalize hd : D.depth v.1 = m
  induction m using Nat.strong_induction_on generalizing v with
  | h m ih =>
    rcases D.earlier v.1 with hb | ⟨b, hb, hne, x, hx⟩
    · by_cases h : o = v
      · subst v
        exact ⟨Walk.nil, by simp⟩
      · have ed : (rolling D).Adj o v := ⟨h, Or.inl hb.symm⟩
        exact ⟨Walk.cons ed Walk.nil, by simp⟩
    · have hd' : D.depth (b, x).1 < m := by rw [← hd]; exact D.depth_lt hb hne
      obtain ⟨p, hp⟩ := ih _ hd' (b,x) rfl
      have ed : (rolling D).Adj (b,x) v :=
        ⟨fun h => hne (congrArg Prod.fst h), Or.inr (Or.inl ⟨hb,hx⟩)⟩
      exact ⟨p.concat ed, by simp only [Walk.length_concat]; omega⟩

end RollingGraph

section Histories

/-- The cardinalities of the nested retention sets, indexed by birth and stage. -/
structure Retention (n q : ℕ) where
  count : Fin (n + 1) → Fin (n + 1) → ℕ
  root (j : Fin (n + 1)) : count j 0 = q
  positivePrevious (i : Fin (n + 1)) (hi : 0 < i.val) :
    0 < count ⟨i.val - 1, by omega⟩ i

abbrev Step (n q k : ℕ) := (Fin (n + 1) → Finset (Fin q)) × Fin (k + 1)

def rootStep (n q k : ℕ) : Step n q k := (fun _ => Finset.univ, 0)

structure History {n q : ℕ} (P : Retention n q) (k : ℕ) where
  stage : Fin (n + 1)
  step : Fin (n + 1) → Step n q k
  root_step : step 0 = rootStep n q k
  beyond (i : Fin (n + 1)) : stage < i → step i = rootStep n q k
  cardinal (j i : Fin (n + 1)) : i ≤ stage → ((step i).1 j).card = P.count j i
  nested (j i l : Fin (n + 1)) :
    i ≤ l → l ≤ stage → (step l).1 j ⊆ (step i).1 j

theorem History.ext' {n q k : ℕ} {P : Retention n q} {b c : History P k}
    (hs : b.stage = c.stage) (hf : b.step = c.step) : b = c := by
  cases b
  cases c
  cases hs
  cases hf
  rfl

noncomputable instance {n q k : ℕ} {P : Retention n q} : DecidableEq (History P k) :=
  Classical.decEq _

noncomputable instance {n q k : ℕ} {P : Retention n q} : Fintype (History P k) := by
  classical
  have : Finite (History P k) :=
    Finite.of_injective (fun b : History P k => (b.stage, b.step))
      (fun _ _ h => History.ext' (congrArg Prod.fst h) (congrArg Prod.snd h))
  exact Fintype.ofFinite _

def History.initial {n q k : ℕ} (P : Retention n q) : History P k where
  stage := 0
  step := fun _ => rootStep n q k
  root_step := rfl
  beyond _ _ := rfl
  cardinal j i hi := by
    have he : i = 0 := le_antisymm hi (Fin.zero_le i)
    simpa [he, rootStep] using (P.root j).symm
  nested _ _ _ _ _ := Finset.Subset.rfl

def History.IsPrefix {n q k : ℕ} {P : Retention n q} (b c : History P k) : Prop :=
  b.stage ≤ c.stage ∧ ∀ i, i ≤ b.stage → b.step i = c.step i

theorem History.IsPrefix.eq_of_stage_eq {n q k : ℕ} {P : Retention n q}
    {b c : History P k} (h : b.IsPrefix c) (he : b.stage = c.stage) : b = c := by
  apply History.ext' he
  funext i
  by_cases hi : i ≤ b.stage
  · exact h.2 i hi
  · exact (b.beyond i (lt_of_not_ge hi)).trans (c.beyond i (he ▸ lt_of_not_ge hi)).symm

def History.prefix {n q k : ℕ} {P : Retention n q} (b : History P k)
    (t : Fin (n + 1)) (ht : t ≤ b.stage) : History P k where
  stage := t
  step i := if i ≤ t then b.step i else rootStep n q k
  root_step := by simp [b.root_step]
  beyond i hi := if_neg (not_le_of_gt hi)
  cardinal j i hi := by simpa [hi] using b.cardinal j i (hi.trans ht)
  nested j i l hil hl := by
    simpa [hl, hil.trans hl] using b.nested j i l hil (hl.trans ht)

theorem History.prefix_spec {n q k : ℕ} {P : Retention n q}
    (b : History P k) (t : Fin (n + 1)) (ht : t ≤ b.stage) :
    (b.prefix t ht).IsPrefix b :=
  ⟨ht, fun i hi => if_pos hi⟩

def historyData {n q k : ℕ} (P : Retention n q) :
    RollingData (History P k) (Fin q) where
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
  retain a b := ((b.step b.stage).1 a.stage : Set (Fin q))
  nested := by
    intro a b c h x hx
    change x ∈ (b.step b.stage).1 a.stage
    rw [h.2 b.stage le_rfl]
    exact c.nested a.stage b.stage c.stage h.1 le_rfl hx
  root := History.initial P
  earlier b := by
    by_cases hb : b.stage = 0
    · exact Or.inl (History.IsPrefix.eq_of_stage_eq
        (b := History.initial P) (c := b)
        ⟨Fin.zero_le _, fun i hi => by
          have he : i = 0 := le_antisymm hi (Fin.zero_le i)
          simp [he, History.initial, b.root_step]⟩ hb.symm).symm
    · have hpos : 0 < b.stage.val := Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))
      let a : Fin (n + 1) := ⟨b.stage.val - 1, by omega⟩
      have ha : a < b.stage := by change b.stage.val - 1 < b.stage.val; omega
      refine Or.inr ⟨b.prefix a ha.le, b.prefix_spec a ha.le, ?_, ?_⟩
      · exact fun he => ha.ne (congrArg History.stage he)
      · change ((b.step b.stage).1 a : Set (Fin q)).Nonempty
        rw [Finset.coe_nonempty, ← Finset.card_pos, b.cardinal _ _ le_rfl]
        exact P.positivePrevious b.stage hpos

end Histories

section LabelPermutations

variable {n q k : ℕ} {P : Retention n q}

/-- Relabel each birth layer independently, transporting all retention choices. -/
def relabelStep (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (s : Step n q k) :
    Step n q k :=
  (fun j => (s.1 j).map (σ j).toEmbedding, s.2)

private theorem relabel_root (σ : Fin (n + 1) → Equiv.Perm (Fin q)) :
    relabelStep σ (rootStep n q k) = rootStep n q k := by
  ext j x
  · simp [relabelStep, rootStep, Finset.mem_map_equiv]
  · rfl

def History.relabel (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (b : History P k) :
    History P k where
  stage := b.stage
  step i := relabelStep σ (b.step i)
  root_step := (congrArg _ b.root_step).trans (relabel_root σ)
  beyond i hi := (congrArg _ (b.beyond i hi)).trans (relabel_root σ)
  cardinal j i hi := by simp [relabelStep, b.cardinal j i hi]
  nested j i l hil ht := by
    intro a ha
    simp only [relabelStep, Finset.mem_map_equiv] at *
    exact b.nested j i l hil ht ha

private theorem relabelStep_symm (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (s : Step n q k) :
    relabelStep (fun j => (σ j).symm) (relabelStep σ s) = s := by
  ext j x
  · simp [relabelStep, Finset.mem_map_equiv]
  · rfl

private theorem History.relabel_symm (σ : Fin (n + 1) → Equiv.Perm (Fin q)) (b : History P k) :
    (b.relabel σ).relabel (fun j => (σ j).symm) = b :=
  History.ext' rfl (funext fun _ => relabelStep_symm σ _)

theorem History.relabel_prefix (σ : Fin (n + 1) → Equiv.Perm (Fin q))
    {b c : History P k} : (b.relabel σ).IsPrefix (c.relabel σ) ↔ b.IsPrefix c := by
  constructor
  · intro h
    refine ⟨h.1, fun i hi => ?_⟩
    exact (relabelStep_symm σ _).symm.trans
      ((congrArg (relabelStep (fun j => (σ j).symm)) (h.2 i hi)).trans (relabelStep_symm σ _))
  · exact fun h => ⟨h.1, fun i hi => congrArg (relabelStep σ) (h.2 i hi)⟩

def labelPerm (σ : Fin (n + 1) → Equiv.Perm (Fin q)) :
    Equiv.Perm (History P k × Fin q) where
  toFun v := (v.1.relabel σ, σ v.1.stage v.2)
  invFun v := (v.1.relabel (fun j => (σ j).symm), (σ v.1.stage).symm v.2)
  left_inv v := Prod.ext (History.relabel_symm σ _) ((σ _).symm_apply_apply _)
  right_inv v := Prod.ext (History.relabel_symm (fun j => (σ j).symm) _) ((σ _).apply_symm_apply _)

theorem labelPerm_adj (σ : Fin (n + 1) → Equiv.Perm (Fin q))
    (u v : History P k × Fin q) :
    (rolling (historyData P)).Adj (labelPerm σ u) (labelPerm σ v) ↔
      (rolling (historyData P)).Adj u v := by
  have h (a b : History P k) : a.relabel σ = b.relabel σ ↔ a = b := by
    constructor
    · intro he
      simpa only [History.relabel_symm] using congrArg (History.relabel (fun j => (σ j).symm)) he
    · exact congrArg _
  change (labelPerm σ u ≠ labelPerm σ v ∧ _) ↔ _
  rw [(labelPerm σ).injective.ne_iff]
  change (_ ∧ (u.1.relabel σ = v.1.relabel σ ∨
    ((u.1.relabel σ).IsPrefix (v.1.relabel σ) ∧
      σ u.1.stage u.2 ∈ (relabelStep σ (v.1.step v.1.stage)).1 u.1.stage) ∨
    ((v.1.relabel σ).IsPrefix (u.1.relabel σ) ∧
      σ v.1.stage v.2 ∈ (relabelStep σ (u.1.step u.1.stage)).1 v.1.stage))) ↔ _
  simp only [h, History.relabel_prefix, relabelStep, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  rfl

end LabelPermutations

section ClonePermutations

variable {n q k : ℕ} {P : Retention n q}

def History.reclone (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) (b : History P k) : History P k where
  stage := b.stage
  step t := if t = i ∧ i ≤ b.stage then ((b.step t).1, σ (b.step t).2) else b.step t
  root_step := by simpa [hi.symm] using b.root_step
  beyond t ht := by
    simp [show ¬(t = i ∧ i ≤ b.stage) from fun h => ht.not_ge (h.1.symm ▸ h.2), b.beyond t ht]
  cardinal j t ht := by
    split <;> exact b.cardinal j t ht
  nested j t l htl hl := by
    split <;> split <;> exact b.nested j t l htl hl

private theorem History.reclone_symm (i : Fin (n + 1)) (hi : i ≠ 0)
    (σ : Equiv.Perm (Fin (k + 1))) (b : History P k) : (b.reclone i hi σ).reclone i hi σ.symm = b := by
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
    (σ : Equiv.Perm (Fin (k + 1))) {b c : History P k} :
    (b.reclone i hi σ).IsPrefix (c.reclone i hi σ) ↔ b.IsPrefix c := by
  have forward (τ : Equiv.Perm (Fin (k + 1))) {b c : History P k} (h : b.IsPrefix c) :
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
    Equiv.Perm (History P k × Fin q) where
  toFun v := (v.1.reclone i hi σ, v.2)
  invFun v := (v.1.reclone i hi σ.symm, v.2)
  left_inv v := Prod.ext (History.reclone_symm i hi σ _) rfl
  right_inv v := Prod.ext (History.reclone_symm i hi σ.symm _) rfl

theorem clonePerm_adj (i : Fin (n + 1)) (hi : i ≠ 0) (σ : Equiv.Perm (Fin (k + 1)))
    (u v : History P k × Fin q) :
    (rolling (historyData P)).Adj (clonePerm i hi σ u) (clonePerm i hi σ v) ↔
      (rolling (historyData P)).Adj u v := by
  have e (b c : History P k) : b.reclone i hi σ = c.reclone i hi σ ↔ b = c := by
    constructor
    · intro hb
      simpa only [History.reclone_symm] using congrArg (History.reclone i hi σ.symm) hb
    · exact congrArg _
  have h (b : History P k) (t : Fin (n + 1)) :
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

end ClonePermutations

section ConcreteRetention

def quota (w M j i : ℕ) : ℕ :=
  if i ≤ j + w then M ^ (w + 2 - (i - j)) else 0

private theorem quota_antitone (w M j : ℕ) (hM : 1 ≤ M) :
    Antitone (quota w M j) := by
  intro i l hil
  by_cases h : l ≤ j + w
  · simp only [quota, h, hil.trans h, ite_true]
    exact pow_le_pow_right' hM (by omega)
  · simp [quota, h]

private theorem quota_le (w M j i : ℕ) (hM : 1 ≤ M) :
    quota w M j i ≤ M ^ (w + 2) := by
  have h := quota_antitone w M j hM (Nat.zero_le i)
  simpa [quota] using h

def concreteRetention (w n M : ℕ) (hw : 1 ≤ w) (hM : 1 ≤ M) :
    Retention n (M ^ (w + 2)) where
  count j i := quota w M j.val i.val
  root j := by simp [quota]
  positivePrevious i hi := by
    have hwi : i.val ≤ i.val - 1 + w := by omega
    simp [quota, hwi, pow_pos (show 0 < M by omega)]

private def segment {m q : ℕ} (h : m ≤ q) : Finset (Fin q) :=
  Finset.univ.map (Fin.castLEEmb h)

private theorem mem_segment {m q : ℕ} (h : m ≤ q) (x : Fin q) :
    x ∈ segment h ↔ x.val < m := by
  simp only [segment, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isLt
  · intro hx
    exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩

private theorem card_segment {m q : ℕ} (h : m ≤ q) : (segment h).card = m := by
  simp [segment]

def fullSpine (w n M k : ℕ) (hw : 1 ≤ w) (hM : 1 ≤ M) :
    History (concreteRetention w n M hw hM) k where
  stage := ⟨n, Nat.lt_succ_self n⟩
  step i := (fun j => segment (quota_le w M j.val i.val hM), 0)
  root_step := by
    ext j x
    · simp [mem_segment, quota, x.isLt, rootStep]
    · rfl
  beyond i hi := (Nat.not_lt_of_ge (Nat.le_of_lt_succ i.isLt) hi).elim
  cardinal j i _ := card_segment (quota_le w M j.val i.val hM)
  nested j i l hil _ := by
    intro x hx
    simp only [mem_segment] at *
    exact hx.trans_le (quota_antitone w M j.val hM hil)

theorem quota_step (w M j i : ℕ) (hj : j ≤ i) (hi : i + 1 ≤ j + w) :
    quota w M j i = M * quota w M j (i + 1) := by
  rw [quota, if_pos (by omega : i ≤ j + w), quota, if_pos hi]
  have he : w + 2 - (i - j) = w + 2 - (i + 1 - j) + 1 := by omega
  rw [he, pow_succ, Nat.mul_comm]

end ConcreteRetention

end

end Omega.RollingCliques
