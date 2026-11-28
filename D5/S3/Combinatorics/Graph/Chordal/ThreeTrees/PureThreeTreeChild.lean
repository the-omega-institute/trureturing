/- GID: D5/S3/Combinatorics/Graph/Chordal/ThreeTrees/PureThreeTreeChild
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct a child history retaining a specified triangle of the parent spine. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ThreeTrees.PureThreeTreeSpines

compile_only_with_mathlib

/-! Construct a child history retaining a specified triangle of the parent spine. -/
namespace Omega.PureThreeTree

open SimpleGraph Omega.RollingCliques
open scoped BigOperators
noncomputable section

variable {n k : ℕ}
local notation "V" => Vertex n k
local notation "D" => Fin (n + 1)
local notation "K" => Fin (k + 1)

def address (v : V) : D × Fin 3 := (v.val.1.stage, v.val.2)

theorem address_injective_on_spine (b : History n k) :
    Set.InjOn (@address n k) {v | v.val.1.IsPrefix b} := by
  intro a ha d hd h
  apply Subtype.ext
  apply Prod.ext
  · have he := congrArg Prod.fst h
    change a.val.1.stage = d.val.1.stage at he
    apply History.IsPrefix.eq_of_stage_eq ?_ he
    exact ⟨he.le, fun i hi => (ha.2 i hi).trans (hd.2 i (he ▸ hi)).symm⟩
  · have he := congrArg Prod.snd h
    change a.val.2 = d.val.2 at he
    exact he

private def labels (T : Finset (D × Fin 3)) (i : D) : Finset (Fin 3) :=
  (T.filter fun x => x.1 = i).image Prod.snd

private theorem mem_labels (T : Finset (D × Fin 3)) (i : D) (a : Fin 3) :
    a ∈ labels T i ↔ (i,a) ∈ T := by
  classical
  constructor
  · rintro h
    obtain ⟨⟨j,b⟩,hj,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hj,h⟩ := Finset.mem_filter.mp hj
    change j = i at h
    subst j
    exact hj
  · intro h
    exact Finset.mem_image.mpr ⟨(i,a), Finset.mem_filter.mpr ⟨h,rfl⟩, rfl⟩

private theorem sum_labels (T : Finset (D × Fin 3)) : ∑ i, (labels T i).card = T.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := T) (t := (Finset.univ : Finset D))
    (f := Prod.fst) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_image_of_injOn
  intro p hp q hq he
  have h₁ := (Finset.mem_filter.mp hp).2
  have h₂ := (Finset.mem_filter.mp hq).2
  exact Prod.ext (h₁.trans h₂.symm) he

private theorem contains_at_or_after (b : History n k) {i j : D} (hi : i ≤ b.stage)
    (hij : i ≤ j) : (b.step i).1 j = Finset.univ := by
  by_cases h0 : i = 0
  · subst i
    rw [b.root_step]
    rfl
  · exact (b.legal _ hi (Nat.pos_of_ne_zero fun h => h0 (Fin.ext h))).2.1 j hij

private theorem retain_at_earlier_step (b : History n k) (i : D) (hi : i ≤ b.stage)
    (v : V) (hv : v.val.1.IsPrefix b) (hnbr : v.val.1 = b ∨ (graph n k).Adj v (birth b)) :
    v.val.2 ∈ (b.step i).1 v.val.1.stage := by
  rcases hnbr with he | hnbr
  · have hij : i ≤ v.val.1.stage := he.symm ▸ hi
    rw [contains_at_or_after b hi hij]
    exact Finset.mem_univ _
  · rcases (rolling_earlier data hnbr hv.1).2 with he | he
    · have hij : i ≤ v.val.1.stage := he.symm ▸ hi
      rw [contains_at_or_after b hi hij]
      exact Finset.mem_univ _
    · exact b.nested _ _ _ hi le_rfl he

private def extended (b : History n k) (t : D) (ht : t.val = b.stage.val + 1)
    (mask : D → Finset (Fin 3)) (copy : K)
    (hl : Legal t mask) (hmask : ∀ i ≤ b.stage, ∀ j, mask j ⊆ (b.step i).1 j) :
    History n k where
  stage := t
  step i := if i ≤ b.stage then b.step i else if i = t then (mask,copy) else rootStep n 3 k
  root_step := by simp [b.root_step]
  beyond i hi := by
    have h₁ : ¬ i ≤ b.stage := by change i.val ≤ b.stage.val → False; omega
    simp [h₁, hi.ne.symm]
  legal i hi hpos := by
    by_cases hb : i ≤ b.stage
    · simpa [hb] using b.legal i hb hpos
    · have he : i = t := by
        apply Fin.ext
        have hle : i.val ≤ t.val := hi
        have hgt : b.stage.val < i.val := lt_of_not_ge hb
        omega
      subst i
      simpa [hb] using hl
  nested j i l hil hlt := by
    by_cases hb : l ≤ b.stage
    · simpa [hb, hil.trans hb] using b.nested j i l hil hb
    · have he : l = t := by
        apply Fin.ext
        have hle : l.val ≤ t.val := hlt
        have hgt : b.stage.val < l.val := lt_of_not_ge hb
        omega
      subst l
      by_cases hx : i ≤ b.stage
      · simpa [hb, hx] using hmask i hx j
      · have he' : i = t := by
          apply Fin.ext
          have hle : i.val ≤ t.val := hil
          have hgt : b.stage.val < i.val := lt_of_not_ge hx
          omega
        subst i
        exact Finset.Subset.rfl

/-- For a triangle on one spine containing the top vertex, preserve exactly
its addresses in the next history step and leave the old steps intact. -/
theorem exists_child_with_triangle (b : History n k) (t : D) (ht : t.val = b.stage.val + 1)
    (P : Finset V) (hcard : P.card = 3)
    (hP : ∀ v ∈ P, v.val.1.IsPrefix b ∧ (v.val.1 = b ∨ (graph n k).Adj v (birth b)))
    (hbirth : birth b ∈ P) (copy : K) :
    ∃ c : History n k, c.stage = t ∧ b.IsPrefix c ∧
      (c.step t).2 = copy ∧
      ∀ v : V, v.val.1.IsPrefix b →
        (v.val.2 ∈ (c.step t).1 v.val.1.stage ↔ v ∈ P) := by
  classical
  let T := P.image address
  let mask (i : D) := if t ≤ i then Finset.univ else labels T i
  have hc (i : D) (hi : t ≤ i) : labels T i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp ((mem_labels _ _ _).mp ha)
    have hp := (hP v hv).1.1
    have hs : v.val.1.stage = i := congrArg Prod.fst he
    have hh : t.val ≤ i.val := hi
    change v.val.1.stage.val ≤ b.stage.val at hp
    omega
  have hcardT : T.card = 3 := by
    rw [Finset.card_image_of_injOn, hcard]
    exact fun a ha d hd he => address_injective_on_spine b (hP a ha).1 (hP d hd).1 he
  have hlegal : Legal t mask := by
    refine ⟨?_, fun i hi => ite_eq_left hi, ?_, ?_⟩
    · calc
        _ = ∑ i, (labels T i).card := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i < t
          · simp [hi, mask, not_le_of_gt hi]
          · simp [hi, hc _ (le_of_not_gt hi)]
        _ = T.card := sum_labels T
        _ = 3 := hcardT
    · intro i hi hit
      rw [show mask i = labels T i by simp [mask, not_le_of_gt hit]]
      intro a ha
      obtain ⟨v,hv,e⟩ := Finset.mem_image.mp ((mem_labels _ _ _).mp ha)
      have he : v.val.1.stage = i := congrArg Prod.fst e
      have hx : v.val.2 = a := congrArg Prod.snd e
      have hv0 := v.property.resolve_left (fun e => (Nat.ne_of_gt hi) (congrArg Fin.val (he.symm.trans e)))
      simpa [hx] using hv0
    · have he : previous t = b.stage := by
        apply Fin.ext
        change t.val - 1 = b.stage.val
        omega
      have hlt : ¬ t ≤ b.stage := by change ¬ t.val ≤ b.stage.val; omega
      rw [he, show mask b.stage = labels T b.stage by simp [mask, hlt], mem_labels]
      exact Finset.mem_image.mpr ⟨birth b, hbirth, rfl⟩
  have hm (i : D) (hi : i ≤ b.stage) (j : D) : mask j ⊆ (b.step i).1 j := by
    by_cases hj : t ≤ j
    · have hij : i ≤ j := by
        change i.val ≤ j.val
        have h₁ : i.val ≤ b.stage.val := hi
        have h₂ : t.val ≤ j.val := hj
        omega
      rw [contains_at_or_after b hi hij]
      exact Finset.subset_univ _
    · intro a ha
      have ha' : a ∈ labels T j := by simpa [mask,hj] using ha
      obtain ⟨v,hv,he⟩ := Finset.mem_image.mp ((mem_labels _ _ _).mp ha')
      have hs : v.val.1.stage = j := congrArg Prod.fst he
      have hl : v.val.2 = a := congrArg Prod.snd he
      have h := retain_at_earlier_step b i hi v (hP v hv).1 (hP v hv).2
      rwa [hs,hl] at h
  let c := extended b t ht mask copy hlegal hm
  have hlt : b.stage < t := Nat.lt_of_succ_le ht.ge
  have hbase : b.IsPrefix c := ⟨hlt.le, fun i hi => by simp [c, extended, hi]⟩
  have hlast : c.step t = (mask,copy) := by simp [c, extended, not_le_of_gt hlt]
  refine ⟨c,rfl,hbase,congrArg Prod.snd hlast,fun v hv => ?_⟩
  rw [hlast]
  change v.val.2 ∈ mask v.val.1.stage ↔ v ∈ P
  rw [show mask v.val.1.stage = labels T v.val.1.stage by
    simp [mask, not_le_of_gt (hv.1.trans_lt hlt)], mem_labels]
  constructor
  · rintro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    have e : w = v := address_injective_on_spine b (hP w hw).1 hv he
    exact e ▸ hw
  · intro h
    exact Finset.mem_image.mpr ⟨v,h,rfl⟩

end
end Omega.PureThreeTree
