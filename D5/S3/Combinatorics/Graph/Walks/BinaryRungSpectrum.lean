/- GID: D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Circulant]
   utility: none
   digest: Maximal independent vertex sets in cyclic two-label matching ladders. -/
import D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace BinaryRungSpectrum

open SimpleGraph Finset
open WellCoveredPowerCliqueProduct (IsMaximalIndep WellCovered)
open MatchingCliqueCycle (spectrum)

noncomputable section

abbrev Vertex (m : ℕ) := Fin (m + 2) × ZMod 2

variable {m : ℕ}

/-- Additive label transport permits both parallel and crossed closing matchings. -/
def forward (t : Fin (m + 2) → ZMod 2) : Equiv.Perm (Vertex m) where
  toFun x := (x.1 + 1, x.2 + t x.1)
  invFun x := (x.1 - 1, x.2 - t (x.1 - 1))
  left_inv x := by simp
  right_inv x := by simp

/-- Rung edges and both orientations of the actual matching edges. -/
def graph (t : Fin (m + 2) → ZMod 2) : SimpleGraph (Vertex m) where
  Adj x y := (x.1 = y.1 ∧ x ≠ y) ∨ forward t x = y ∨ forward t y = x
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro x h
    have hstep : x.1 + 1 ≠ x.1 := by intro h; simp at h
    rcases h with h | h | h
    · exact h.2 rfl
    · exact hstep (congrArg Prod.fst h)
    · exact hstep (congrArg Prod.fst h)⟩

private lemma binary_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  have hb := ZMod.val_lt b
  have hv : b.val = 0 ∨ b.val = 1 := by omega
  rcases hv with h | h
  · left; apply ZMod.val_injective; simpa using h
  · right; apply ZMod.val_injective; simpa only [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < 2)] using h

private lemma binary_double_one : (1 : ZMod 2) + 1 = 0 := by
  change ((2 : ℕ) : ZMod 2) = 0
  exact ZMod.natCast_self 2

private lemma binary_ne {a b : ZMod 2} (h : a ≠ b) : b = a + 1 := by
  rcases binary_cases a with rfl | rfl <;> rcases binary_cases b with rfl | rfl
  · exact (h rfl).elim
  · simp
  · exact binary_double_one.symm
  · exact (h rfl).elim

private lemma rung_unique {t : Fin (m + 2) → ZMod 2} {I : Finset (Vertex m)}
    (hI : IsMaximalIndep (graph t) I) {i : Fin (m + 2)} {a b : ZMod 2}
    (ha : (i,a) ∈ I) (hb : (i,b) ∈ I) : a = b := by
  by_contra h
  have hne : (i,a) ≠ (i,b) := fun he => h (congrArg Prod.snd he)
  exact hI.1 _ ha _ hb hne (Or.inl ⟨rfl, hne⟩)

private def occupied (I : Finset (Vertex m)) : Finset (Fin (m + 2)) := I.image Prod.fst

private lemma mem_occupied (I : Finset (Vertex m)) (i : Fin (m + 2)) :
    i ∈ occupied I ↔ ∃ b : ZMod 2, (i,b) ∈ I := by
  constructor
  · intro h
    obtain ⟨x, hx, hxi⟩ := mem_image.mp h
    exact ⟨x.2, by simpa only [← hxi] using hx⟩
  · rintro ⟨b, hb⟩
    exact mem_image.mpr ⟨(i,b), hb, rfl⟩

private def label (I : Finset (Vertex m)) (i : Fin (m + 2)) : ZMod 2 :=
  if (i,0) ∈ I then 0 else 1

private lemma label_mem (I : Finset (Vertex m)) {i : Fin (m + 2)}
    (hi : i ∈ occupied I) : (i, label I i) ∈ I := by
  by_cases h0 : (i,0) ∈ I
  · simpa [label, h0] using h0
  · obtain ⟨b, hb⟩ := (mem_occupied I i).mp hi
    rcases binary_cases b with rfl | rfl
    · exact (h0 hb).elim
    · simpa [label, h0] using hb

private lemma selected_label {t : Fin (m + 2) → ZMod 2} {I : Finset (Vertex m)}
    (hI : IsMaximalIndep (graph t) I) {i : Fin (m + 2)} {b : ZMod 2}
    (hb : (i,b) ∈ I) : label I i = b :=
  rung_unique hI (label_mem I ((mem_occupied I i).mpr ⟨b,hb⟩)) hb

private lemma next_occupied {t : Fin (m + 2) → ZMod 2} {I : Finset (Vertex m)}
    (hI : IsMaximalIndep (graph t) I) {i : Fin (m + 2)}
    (hi : i ∉ occupied I) : i + 1 ∈ occupied I := by
  by_contra hn
  have hprev (b : ZMod 2) : ∃ c : ZMod 2, (i - 1,c) ∈ I ∧ c + t (i - 1) = b := by
    have hv : (i,b) ∉ I := fun h => hi ((mem_occupied I i).mpr ⟨b,h⟩)
    obtain ⟨u, hu, ha⟩ := hI.2 (i,b) hv
    rcases ha with ⟨he,_⟩ | he | he
    · exact (hi (mem_image.mpr ⟨u,hu,he.symm⟩)).elim
    · have hf : i + 1 = u.1 := congrArg Prod.fst he
      exact (hn (mem_image.mpr ⟨u,hu,hf.symm⟩)).elim
    · have hf : u.1 + 1 = i := congrArg Prod.fst he
      have hf' : u.1 = i - 1 := eq_sub_of_add_eq hf
      have hs : u.2 + t u.1 = b := congrArg Prod.snd he
      exact ⟨u.2, by simpa only [← hf'] using hu, by simpa only [← hf'] using hs⟩
  obtain ⟨a, ha, ha0⟩ := hprev 0
  obtain ⟨b, hb, hb1⟩ := hprev 1
  have hab := rung_unique hI ha hb
  have : (0 : ZMod 2) = 1 := ha0.symm.trans (by simpa only [hab] using hb1)
  exact zero_ne_one this

private def phase (t : Fin (m + 2) → ZMod 2) (I : Finset (Vertex m))
    (i : Fin (m + 2)) : ZMod 2 :=
  if i ∈ occupied I then label I i else label I (i + 1) - t i

private lemma phase_step {t : Fin (m + 2) → ZMod 2} {I : Finset (Vertex m)}
    (hI : IsMaximalIndep (graph t) I) (i : Fin (m + 2)) :
    phase t I (i + 1) = phase t I i + (if i ∈ occupied I then 1 else 0) + t i := by
  by_cases hi : i ∈ occupied I
  · by_cases hn : i + 1 ∈ occupied I
    · have hne : label I i + t i ≠ label I (i + 1) := by
        intro he
        have hv : (i,label I i) ≠ (i + 1,label I (i + 1)) := by
          intro h
          have := congrArg Prod.fst h
          simp at this
        apply hI.1 _ (label_mem I hi) _ (label_mem I hn) hv
        exact Or.inr (Or.inl (Prod.ext rfl he))
      have he := binary_ne hne
      simp only [phase, hi, hn, ite_true]
      simpa only [add_assoc, add_comm, add_left_comm] using he
    · let b : ZMod 2 := label I i + t i + 1
      have hv : (i + 1,b) ∉ I := fun h => hn ((mem_occupied I _).mpr ⟨b,h⟩)
      obtain ⟨u, hu, ha⟩ := hI.2 (i + 1,b) hv
      have hout : label I (i + 1 + 1) = b + t (i + 1) := by
        rcases ha with ⟨he,_⟩ | he | he
        · exact (hn (mem_image.mpr ⟨u,hu,he.symm⟩)).elim
        · have hf : i + 1 + 1 = u.1 := congrArg Prod.fst he
          have hs : b + t (i + 1) = u.2 := congrArg Prod.snd he
          have hm : (i + 1 + 1, b + t (i + 1)) ∈ I := by
            simpa only [hf, hs] using hu
          exact selected_label hI hm
        · have hf : u.1 + 1 = i + 1 := congrArg Prod.fst he
          have hf' : u.1 = i := add_right_cancel hf
          have hs : u.2 + t u.1 = b := congrArg Prod.snd he
          have hm : (i,u.2) ∈ I := by simpa only [← hf'] using hu
          have hl := selected_label hI hm
          rw [hf', ← hl] at hs
          have hz : (1 : ZMod 2) = 0 := add_left_cancel
            (show (label I i + t i) + 1 = (label I i + t i) + 0 from by
              simpa [b,add_assoc] using hs.symm)
          exact (one_ne_zero hz).elim
      simp only [phase, hi, hn, ite_true, ite_false]
      rw [hout]
      dsimp [b]
      ring
  · have hn := next_occupied hI hi
    simp only [phase, hi, hn, ite_false, ite_true, add_zero]
    ring

private lemma occupied_card {t : Fin (m + 2) → ZMod 2} {I : Finset (Vertex m)}
    (hI : IsMaximalIndep (graph t) I) : (occupied I).card = I.card := by
  apply card_image_of_injOn
  intro u hu v hv huv
  have hu' : (v.1,u.2) ∈ I := by
    change (u.1,u.2) ∈ I at hu
    simpa only [huv] using hu
  exact Prod.ext huv (rung_unique hI hu' hv)

/-- Independence and domination force the sharp density bounds on the actual vertex set. -/
theorem cardinality_bounds {t : Fin (m + 2) → ZMod 2} {I : Finset (Vertex m)}
    (hI : IsMaximalIndep (graph t) I) : m + 2 ≤ 2 * I.card ∧ I.card ≤ m + 2 := by
  have hupper : I.card ≤ m + 2 := by
    rw [← occupied_card hI]
    simpa only [Fintype.card_fin] using card_le_univ (occupied I)
  have hinj : Set.InjOn (fun i : Fin (m + 2) => i + 1)
      ((univ \ occupied I : Finset (Fin (m + 2))) : Set (Fin (m + 2))) := by
    intro i _ j _ hij
    exact add_right_cancel hij
  have himage : ((univ \ occupied I).image (fun i => i + 1)) ⊆ occupied I := by
    rintro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact next_occupied hI (mem_sdiff.mp hi).2
  have hcard := card_le_card himage
  rw [card_image_of_injOn hinj, card_sdiff,inter_univ, card_univ,
    Fintype.card_fin, occupied_card hI] at hcard
  omega

/-- The holonomy of the matching cycle is the parity of every maximal independent set. -/
theorem cardinality_parity {t : Fin (m + 2) → ZMod 2} {I : Finset (Vertex m)}
    (hI : IsMaximalIndep (graph t) I) : (I.card : ZMod 2) = ∑ i, t i := by
  have hshift : ∑ i : Fin (m + 2), phase t I (i + 1) = ∑ i, phase t I i := by
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i _
      exact mem_univ _
    · intro i _ j _ he
      exact add_right_cancel he
    · intro j _
      exact ⟨j - 1, mem_univ _, by simp⟩
    · intro i _
      rfl
  have hsum : ∑ i : Fin (m + 2), phase t I (i + 1) =
      ∑ i, (phase t I i + (if i ∈ occupied I then 1 else 0) + t i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact phase_step hI i
  have hcount : (∑ i : Fin (m + 2), if i ∈ occupied I then (1 : ZMod 2) else 0) =
      (I.card : ZMod 2) := by
    rw [← occupied_card hI]
    simp
  rw [hshift, Finset.sum_add_distrib, Finset.sum_add_distrib, hcount] at hsum
  have hz : (I.card : ZMod 2) + ∑ i, t i = 0 := by
    apply add_left_cancel (a := ∑ i : Fin (m+2), phase t I i)
    simpa only [add_assoc,add_zero] using hsum.symm
  have hneg : -(∑ i, t i) = ∑ i, t i := by
    rcases binary_cases (∑ i, t i) with h | h <;> rw [h] <;> decide
  exact (eq_neg_of_add_eq_zero_left hz).trans hneg

private def realize (O : Finset (Fin (m + 2))) (f : Fin (m + 2) → ZMod 2) :
    Finset (Vertex m) := O.image (fun i => (i,f i))

private lemma mem_realize (O : Finset (Fin (m + 2))) (f : Fin (m + 2) → ZMod 2)
    (i : Fin (m + 2)) (b : ZMod 2) : (i,b) ∈ realize O f ↔ i ∈ O ∧ b = f i := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := mem_image.mp h
    have hji : j = i := congrArg Prod.fst he
    subst j
    exact ⟨hj,(congrArg Prod.snd he).symm⟩
  · rintro ⟨hi,rfl⟩
    exact mem_image.mpr ⟨i,hi,rfl⟩

/-- A phase solution assembles a native independent dominating set of the prescribed rungs. -/
theorem maximal_of_phase (t : Fin (m + 2) → ZMod 2) (O : Finset (Fin (m + 2)))
    (f : Fin (m + 2) → ZMod 2)
    (hgap : ∀ i, i ∉ O → i + 1 ∈ O)
    (hphase : ∀ i, f (i + 1) = f i + (if i ∈ O then 1 else 0) + t i) :
    ∃ I : Finset (Vertex m), IsMaximalIndep (graph t) I ∧ I.card = O.card := by
  have hsep (i : Fin (m + 2)) (hi : i ∈ O) : f i + t i ≠ f (i + 1) := by
    rw [hphase i, if_pos hi]
    simp [add_assoc, add_comm, add_left_comm]
  refine ⟨realize O f, ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy hne ha
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    rcases ha with ⟨he,_⟩ | he | he
    · have he' : i=j := he
      subst j
      exact hne rfl
    · have hf : i + 1 = j := congrArg Prod.fst he
      have hs : f i + t i = f j := congrArg Prod.snd he
      exact hsep i hi (by simpa only [hf] using hs)
    · have hf : j + 1 = i := congrArg Prod.fst he
      have hs : f j + t j = f i := congrArg Prod.snd he
      exact hsep j hj (by simpa only [hf] using hs)
  · rintro ⟨i,b⟩ hv
    by_cases hi : i ∈ O
    · have hb : b ≠ f i := fun he => hv ((mem_realize O f i b).mpr ⟨hi,he⟩)
      refine ⟨(i,f i), (mem_realize O f _ _).mpr ⟨hi,rfl⟩, Or.inl ⟨rfl,?_⟩⟩
      exact fun he => hb (congrArg Prod.snd he)
    · have hn := hgap i hi
      by_cases hb : b = f i
      · refine ⟨(i + 1,f (i + 1)), (mem_realize O f _ _).mpr ⟨hn,rfl⟩, ?_⟩
        apply Or.inr ∘ Or.inl
        change (i+1,b+t i)=(i+1,f (i+1))
        refine Prod.ext rfl ?_
        simpa only [hb, hphase i, if_neg hi, add_zero]
      · have hp : i - 1 ∈ O := by
          by_contra hp
          have hh := hgap (i - 1) hp
          exact hi (by simpa using hh)
        have hs := hphase (i - 1)
        simp only [sub_add_cancel, if_pos hp] at hs
        have hf : f (i - 1) + t (i - 1) + 1 = b + 1 := by
          calc
            f (i - 1) + t (i - 1) + 1 = f i := by
              simpa only [add_assoc, add_comm, add_left_comm] using hs.symm
            _ = b + 1 := binary_ne hb
        have hb' : f (i - 1) + t (i - 1) = b := add_right_cancel hf
        refine ⟨(i - 1,f (i - 1)), (mem_realize O f _ _).mpr ⟨hp,rfl⟩, ?_⟩
        apply Or.inr ∘ Or.inr
        change (i-1+1,f (i-1)+t (i-1))=(i,b)
        exact Prod.ext (by simp) hb'
  · apply card_image_of_injective
    intro i j he
    exact congrArg Prod.fst he

/-- Only the closing matching carries the total twist. -/
def closing (m : ℕ) (q : ZMod 2) (i : Fin (m + 2)) : ZMod 2 :=
  if i.val + 1 = m + 2 then q else 0

private def spacedRungs (m e : ℕ) : Finset (Fin (m + 2)) :=
  univ.filter (fun i => i.val % 2 = 0 ∨ 2 * e ≤ i.val)

private def prefixCount (e x : ℕ) : ℕ := x - min e (x / 2)

private lemma prefix_step (e x : ℕ) :
    prefixCount e (x + 1) = prefixCount e x + (if x % 2 = 0 ∨ 2 * e ≤ x then 1 else 0) := by
  dsimp [prefixCount]
  split_ifs <;> omega

private lemma spaced_card (e : ℕ) (he : 2 * e ≤ m + 2) :
    (spacedRungs m e).card = m + 2 - e := by
  have hc : (univ \ spacedRungs m e).card = e := by
    calc
      (univ \ spacedRungs m e).card = (range e).card := by
        apply card_bij (fun i _ => i.val / 2)
        · intro i hi
          simp only [mem_sdiff, mem_univ, spacedRungs, mem_filter, true_and,
            not_or] at hi
          simp only [mem_range]
          omega
        · intro i hi j hj hij
          simp only [mem_sdiff, mem_univ, spacedRungs, mem_filter, true_and,
            not_or] at hi hj
          apply Fin.ext
          omega
        · intro j hj
          simp only [mem_range] at hj
          refine ⟨⟨2 * j + 1, by omega⟩, ?_, ?_⟩
          · simp only [mem_sdiff, mem_univ, spacedRungs, mem_filter, true_and]
            omega
          · dsimp
            omega
      _ = e := card_range e
  rw [card_sdiff,inter_univ, card_univ, Fintype.card_fin] at hc
  have hle : (spacedRungs m e).card ≤ m + 2 := by
    simpa using card_le_univ (spacedRungs m e)
  omega

private lemma spaced_gap (e : ℕ) (he : 2 * e ≤ m + 2) (i : Fin (m + 2)) :
    i ∉ spacedRungs m e → i + 1 ∈ spacedRungs m e := by
  simp only [spacedRungs, mem_filter, mem_univ, true_and]
  intro hi
  have hiBound := i.isLt
  have hval : (i + 1).val = (i.val + 1) % (m + 2) := by simp [Fin.val_add]
  rw [hval]
  by_cases hl : i.val + 1 = m + 2
  · simp [hl]
  · rw [Nat.mod_eq_of_lt (show i.val + 1 < m + 2 by omega)]
    omega

private lemma spaced_phase (e : ℕ) (he : 2 * e ≤ m + 2) (i : Fin (m + 2)) :
    (prefixCount e (i + 1).val : ZMod 2) = (prefixCount e i.val : ZMod 2) +
      (if i ∈ spacedRungs m e then 1 else 0) + closing m ((m + 2 - e : ℕ) : ZMod 2) i := by
  have hiBound := i.isLt
  have hval : (i + 1).val = (i.val + 1) % (m + 2) := by simp [Fin.val_add]
  have hstep := prefix_step e i.val
  by_cases hl : i.val + 1 = m + 2
  · have hend : prefixCount e (m + 2) = m + 2 - e := by dsimp [prefixCount]; omega
    have hz : (i + 1).val = 0 := by rw [hval, hl]; simp
    rw [hz]
    have hstep' : (prefixCount e i.val : ZMod 2) +
        (if i ∈ spacedRungs m e then 1 else 0) = (m + 2 - e : ℕ) := by
      rw [hl, hend] at hstep
      simpa [spacedRungs] using congrArg (fun x : ℕ => (x : ZMod 2)) hstep.symm
    rw [hstep']
    simp only [closing, hl, if_pos]
    rcases binary_cases ((m + 2 - e : ℕ) : ZMod 2) with h | h <;>
      simp [prefixCount, h, binary_double_one]
  · rw [hval, Nat.mod_eq_of_lt (show i.val + 1 < m + 2 by omega)]
    simp only [closing, hl, if_neg, add_zero]
    simpa [spacedRungs] using congrArg (fun x : ℕ => (x : ZMod 2)) hstep

/-- Every cardinality meeting the density bound and closing parity is attained by vertices. -/
theorem closing_attainability (k : ℕ) (hlo : m + 2 ≤ 2 * k) (hhi : k ≤ m + 2) :
    k ∈ spectrum (graph (closing m (k : ZMod 2))) := by
  let e := m + 2 - k
  have he : 2 * e ≤ m + 2 := by dsimp [e]; omega
  have hk : m + 2 - e = k := by dsimp [e]; omega
  obtain ⟨I,hI,hcard⟩ := maximal_of_phase (closing m ((m + 2 - e : ℕ) : ZMod 2)) (spacedRungs m e)
    (fun i => (prefixCount e i.val : ZMod 2)) (spaced_gap e he) (spaced_phase e he)
  rw [hk] at hI
  exact ⟨I,hI,by rw [hcard,spaced_card e he,hk]⟩

private lemma closing_total (q : ZMod 2) : ∑ i : Fin (m + 2), closing m q i = q := by
  have he : closing m q = fun i => if i = Fin.last (m + 1) then q else 0 := by
    funext i
    have hi : i.val + 1 = m + 2 ↔ i = Fin.last (m + 1) := by
      rw [Fin.ext_iff]
      simp only [Fin.val_last]
      omega
    simp only [closing, hi]
  rw [he]
  simp

/-- The complete spectrum includes necessity and a vertex-set construction for every size. -/
theorem closing_spectrum (q : ZMod 2) (k : ℕ) :
    k ∈ spectrum (graph (closing m q)) ↔
      m + 2 ≤ 2 * k ∧ k ≤ m + 2 ∧ (k : ZMod 2) = q := by
  constructor
  · rintro ⟨I,hI,rfl⟩
    exact ⟨(cardinality_bounds hI).1, (cardinality_bounds hI).2,
      (cardinality_parity hI).trans (closing_total q)⟩
  · rintro ⟨hlo,hhi,hq⟩
    rw [← hq]
    exact closing_attainability k hlo hhi

/-- The untwisted ladder is the native Cartesian prism, on precisely the same vertices. -/
theorem closing_zero_eq_prism (r : ℕ) :
    graph (closing (r + 1) 0) =
      (cycleGraph (r + 3)) □ (⊤ : SimpleGraph (ZMod 2)) := by
  ext x y
  rcases x with ⟨i,a⟩
  rcases y with ⟨j,b⟩
  have hc : (cycleGraph (r + 3)).Adj i j ↔ j=i+1 ∨ i=j+1 := by
    rw [cycleGraph_adj]
    constructor
    · rintro (h | h)
      · exact Or.inr ((sub_eq_iff_eq_add').mp h)
      · exact Or.inl ((sub_eq_iff_eq_add').mp h)
    · rintro (h | h)
      · exact Or.inr ((sub_eq_iff_eq_add').mpr h)
      · exact Or.inl ((sub_eq_iff_eq_add').mpr h)
  have hz (i : Fin (r + 3)) : closing (r + 1) 0 i = 0 := by simp [closing]
  change ((i=j ∧ (i,a) ≠ (j,b)) ∨
      (i+1,a+closing (r+1) 0 i)=(j,b) ∨
      (j+1,b+closing (r+1) 0 j)=(i,a)) ↔
    ((cycleGraph (r+3)).Adj i j ∧ a=b) ∨
      ((⊤ : SimpleGraph (ZMod 2)).Adj a b ∧ i=j)
  simp only [hz,add_zero,Prod.mk.injEq,hc,top_adj]
  constructor
  · rintro (⟨hi,hne⟩ | ⟨hi,hb⟩ | ⟨hi,hb⟩)
    · exact Or.inr ⟨fun hb => hne (Prod.ext hi hb),hi⟩
    · exact Or.inl ⟨Or.inl hi.symm,hb⟩
    · exact Or.inl ⟨Or.inr hi.symm,hb.symm⟩
  · rintro (⟨hi,hb⟩ | ⟨hb,hi⟩)
    · rcases hi with hi | hi
      · exact Or.inr (Or.inl ⟨hi.symm,hb⟩)
      · exact Or.inr (Or.inr ⟨hi.symm,hb.symm⟩)
    · exact Or.inl ⟨hi,fun h => hb (congrArg Prod.snd h)⟩

/-- Complete necessity and attainability for every Cartesian prism with at least three rungs. -/
theorem prism_spectrum (r k : ℕ) :
    k ∈ spectrum ((cycleGraph (r + 3)) □ (⊤ : SimpleGraph (ZMod 2))) ↔
      r + 3 ≤ 2 * k ∧ k ≤ r + 3 ∧ Even k := by
  rw [← closing_zero_eq_prism]
  exact (closing_spectrum 0 k).trans (by rw [ZMod.natCast_eq_zero_iff_even])

private theorem wellCovered_closing_iff (q : ZMod 2) :
    WellCovered (graph (closing m q)) ↔
      ∀ k l : ℕ, (m + 2 ≤ 2*k ∧ k ≤ m + 2 ∧ (k : ZMod 2) = q) →
        (m + 2 ≤ 2*l ∧ l ≤ m + 2 ∧ (l : ZMod 2) = q) → k = l := by
  constructor
  · intro h k l hk hl
    obtain ⟨I,hI,hk'⟩ := (closing_spectrum q k).mpr hk
    obtain ⟨J,hJ,hl'⟩ := (closing_spectrum q l).mpr hl
    simpa only [hk',hl'] using h I J hI hJ
  · intro h I J hI hJ
    exact h I.card J.card
      ((closing_spectrum q I.card).mp ⟨I,hI,rfl⟩)
      ((closing_spectrum q J.card).mp ⟨J,hJ,rfl⟩)

/-- The complete untwisted classification follows from the attained spectrum at every size. -/
theorem prism_wellCovered_iff (r : ℕ) :
    WellCovered ((cycleGraph (r + 3)) □ (⊤ : SimpleGraph (ZMod 2))) ↔
      r = 0 ∨ r = 2 := by
  rw [← closing_zero_eq_prism,wellCovered_closing_iff]
  simp only [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  constructor
  · intro h
    by_contra hn
    let k := 2 * ((r + 3) / 2)
    have hk : r + 3 ≤ 2*k ∧ k ≤ r + 3 ∧ k % 2 = 0 := by dsimp [k]; omega
    have hl : r + 3 ≤ 2*(k-2) ∧ k-2 ≤ r + 3 ∧ (k-2) % 2 = 0 := by
      dsimp [k]; omega
    have he := h k (k-2) hk hl
    dsimp [k] at he
    omega
  · intro hr k l hk hl
    omega

/-- The complete twisted classification includes the repeated two-rung boundary. -/
theorem twisted_wellCovered_iff :
    WellCovered (graph (closing m 1)) ↔ m ≤ 2 := by
  rw [wellCovered_closing_iff]
  simp only [ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]
  constructor
  · intro h
    by_contra hn
    let k := 2 * ((m + 1) / 2) + 1
    have hk : m + 2 ≤ 2*k ∧ k ≤ m + 2 ∧ k % 2 = 1 := by dsimp [k]; omega
    have hl : m + 2 ≤ 2*(k-2) ∧ k-2 ≤ m + 2 ∧ (k-2) % 2 = 1 := by
      dsimp [k]; omega
    have he := h k (k-2) hk hl
    dsimp [k] at he
    omega
  · intro hm k l hk hl
    omega

end

end BinaryRungSpectrum
