/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuOrder
   mirror-E: none(waiver:universal-order-and-clique-fiber-proofs)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Fin]
   utility: none
   digest: Ordered clique-fiber expansion preserves the cokernel closure rules. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure
import Mathlib.Data.Fintype.Fin

/-! Clique-fiber expansion and its converse along an increasing section. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- Replace each fiber of a monotone map by a clique of adjacent twins. -/
def cliqueLift (E : α → α → Prop) (f : β → α) (a b : β) : Prop :=
  a < b ∧ (f a = f b ∨ E (f a) (f b))

/-- Arbitrary ordered clique blowups preserve both P and J, including collapsed premises. -/
theorem rules_cliqueLift {E : α → α → Prop} (h : Rules E)
    {f : β → α} (hf : Monotone f) : Rules (cliqueLift E f) := by
  refine ⟨fun h => h.1, ?_, ?_⟩
  · intro a b c d hab hcd hac hcb hbd
    refine ⟨hbd, ?_⟩
    by_cases hbd' : f b = f d
    · exact Or.inl hbd'
    right
    have hbd'' : f b < f d := lt_of_le_of_ne (hf hbd.le) hbd'
    by_cases hcb' : f c = f b
    · rcases hcd.2 with hcd' | hcd'
      · exact False.elim (hbd' (hcb'.symm.trans hcd'))
      · simpa only [hcb'] using hcd'
    · have hcb'' : f c < f b := lt_of_le_of_ne (hf hcb.le) hcb'
      have hab' : E (f a) (f b) := hab.2.resolve_left (by
        intro hab'; have := hf hac; rw [hab'] at this; exact (not_lt_of_ge this) hcb'')
      have hcd' : E (f c) (f d) := hcd.2.resolve_left (by
        intro hcd'; rw [hcd'] at hcb''; exact (not_lt_of_ge hbd''.le) hcb'')
      exact h.propagate hab' hcd' (hf hac) hcb'' hbd''
  · intro a b c d e g hab hcd heg hac hcb hae heb hbd hbg
    have hout : max c e < max d g := by
      exact lt_of_lt_of_le (max_lt hcb heb) (hbd.trans (le_max_left d g))
    refine ⟨hout, ?_⟩
    have hmap₁ : f (max c e) = max (f c) (f e) := hf.map_max
    have hmap₂ : f (max d g) = max (f d) (f g) := hf.map_max
    have hlow : f (max c e) ≤ f b := hf (max_le hcb.le heb.le)
    have hupp : f b ≤ f (max d g) := hf (hbd.trans (le_max_left d g))
    by_cases heq : f (max c e) = f (max d g)
    · exact Or.inl heq
    right
    have hlt : f (max c e) < f (max d g) := lt_of_le_of_ne (hlow.trans hupp) heq
    by_cases hmiddle : f (max c e) < f b
    · have hc : f c < f b := (hf (le_max_left c e)).trans_lt hmiddle
      have he : f e < f b := (hf (le_max_right c e)).trans_lt hmiddle
      have hab' : E (f a) (f b) := hab.2.resolve_left (by
        intro heq; have := hf hac; rw [heq] at this; exact (not_lt_of_ge this) hc)
      have hcd' : E (f c) (f d) := hcd.2.resolve_left (by
        intro heq; have := hf hbd; rw [← heq] at this; exact (not_lt_of_ge this) hc)
      have heg' : E (f e) (f g) := heg.2.resolve_left (by
        intro heq; have := hf hbg; rw [← heq] at this; exact (not_lt_of_ge this) he)
      rw [hmap₁, hmap₂]
      exact h.join hab' hcd' heg' (hf hac) hc (hf hae) he (hf hbd) (hf hbg)
    · have hmiddle' : f (max c e) = f b := le_antisymm hlow (le_of_not_gt hmiddle)
      have hy : f b < f (max d g) := by simpa only [hmiddle'] using hlt
      have step {r s : β} (hrs : cliqueLift E f r s)
          (har : a ≤ r) (hrx : r ≤ max c e) (hsy : s = max d g) :
          E (f (max c e)) (f (max d g)) := by
        subst s
        have hr : f r ≤ f (max c e) := hf hrx
        have hrs' : E (f r) (f (max d g)) := hrs.2.resolve_left (by
          intro heq; rw [heq] at hr; exact (not_lt_of_ge hr) hlt)
        by_cases hr' : f r = f (max c e)
        · simpa only [hr'] using hrs'
        · have hr'' : f r < f b := by
            rw [← hmiddle']; exact lt_of_le_of_ne hr hr'
          have hab' : E (f a) (f b) := hab.2.resolve_left (by
            intro heq; have := hf har; rw [heq] at this; exact (not_lt_of_ge this) hr'')
          rw [hmiddle']
          exact h.propagate hab' hrs' (hf har) hr'' hy
      rcases le_total d g with hdg | hgd
      · exact step heg hae (le_max_right c e) (max_eq_right hdg).symm
      · exact step hcd hac (le_max_left c e) (max_eq_left hgd).symm

/-- Compression by a monotone map with an increasing section is an equivalence. -/
theorem rules_cliqueLift_iff {E : α → α → Prop}
    (hordered : ∀ {a b}, E a b → a < b)
    {f : β → α} (hf : Monotone f) {s : α → β}
    (hs : StrictMono s) (hfs : ∀ a, f (s a) = a) :
    Rules (cliqueLift E f) ↔ Rules E := by
  refine ⟨?_, fun h => rules_cliqueLift h hf⟩
  intro h
  have lift {a b : α} (hab : E a b) : cliqueLift E f (s a) (s b) := by
    exact ⟨hs (hordered hab), Or.inr (by simpa only [hfs] using hab)⟩
  have unlift {a b : α} (hab : cliqueLift E f (s a) (s b)) : E a b := by
    rcases hab.2 with heq | he
    · have : a = b := by simpa only [hfs] using heq
      exact False.elim ((ne_of_lt (hs.lt_iff_lt.mp hab.1)) this)
    · simpa only [hfs] using he
  refine ⟨hordered, ?_, ?_⟩
  · intro a b c d hab hcd hac hcb hbd
    exact unlift (h.propagate (lift hab) (lift hcd) (hs.monotone hac) (hs hcb) (hs hbd))
  · intro a b c d e g hab hcd heg hac hcb hae heb hbd hbg
    have hj := h.join (lift hab) (lift hcd) (lift heg)
      (hs.monotone hac) (hs hcb) (hs.monotone hae) (hs heb)
      (hs.monotone hbd) (hs.monotone hbg)
    rw [← hs.monotone.map_max, ← hs.monotone.map_max] at hj
    exact unlift hj

/-- An edge between two vertices without choosing their order. -/
def Incident (E : α → α → Prop) (a b : α) : Prop := E a b ∨ E b a

private theorem ordinary_clique {E : ℕ → ℕ → Prop} (h : Rules E)
    {g k : ℕ} (hg : E 0 g) (hk : E 0 k) (hgk : g < k) : E g k :=
  h.propagate hg hk le_rfl (h.ordered hg) hgk

/-- Exceptional incidence is an upper set in the ordered list of ordinary vertices. -/
theorem incident_ordinary_mono {E : ℕ → ℕ → Prop} (h : Rules E)
    {s g k : ℕ} (hs : ¬ E 0 s) (hg : E 0 g) (hk : E 0 k)
    (hgk : g < k) (hsg : Incident E s g) : Incident E s k := by
  rcases hsg with hsg | hgs
  · left
    have hj := h.join hg hsg hk (Nat.zero_le s) (h.ordered hsg)
      le_rfl (h.ordered hg) le_rfl hgk.le
    simpa only [max_eq_left (Nat.zero_le s), max_eq_right hgk.le] using hj
  · have hsk : s ≠ k := by intro heq; subst s; exact hs hk
    rcases lt_or_gt_of_ne hsk with hsk | hks
    · left
      exact h.propagate hgs (ordinary_clique h hg hk hgk) le_rfl (h.ordered hgs) hsk
    · right
      exact h.propagate hk hgs (Nat.zero_le g) hgk hks

/-- Every exceptional vertex has one unique cutoff, including empty ordinary lists. -/
theorem exists_unique_ordinary_cutoff {E : ℕ → ℕ → Prop} (h : Rules E)
    {s M : ℕ} (hs : ¬ E 0 s) (g : Fin M → ℕ) (hg : StrictMono g)
    (ho : ∀ r, E 0 (g r)) :
    ∃! c : ℕ, c ≤ M ∧ ∀ r : Fin M, Incident E s (g r) ↔ c ≤ r.val := by
  classical
  let c := (Finset.univ.filter (fun r : Fin M => ¬ Incident E s (g r))).card
  have hcM : c ≤ M := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin M))
        (fun r => ¬ Incident E s (g r)))
  have hdown : ∀ i j : Fin M, j ≤ i → ¬ Incident E s (g i) → ¬ Incident E s (g j) := by
    intro i j hji hi hj
    by_cases hij : j = i
    · exact hi (hij ▸ hj)
    · have hji' : j < i := lt_of_le_of_ne hji hij
      exact hi (incident_ordinary_mono h hs (ho j) (ho i) (hg hji') hj)
  have hcut : ∀ r : Fin M, Incident E s (g r) ↔ c ≤ r.val := by
    intro r
    have hi : r.val < c ↔ ¬ Incident E s (g r) :=
      Fin.lt_card_filter_univ_iff_apply_of_imp (fun j => ¬ Incident E s (g j)) hdown
    exact (not_iff_not.mp (by simpa only [not_le] using hi)).symm
  refine ⟨c, ⟨hcM, hcut⟩, ?_⟩
  intro d hd
  obtain ⟨hdM, hdcut⟩ := hd
  suffices c = d from this.symm
  apply le_antisymm
  · by_contra hdc
    have hdM : d < M := by omega
    have hi := (hdcut ⟨d, hdM⟩).mpr le_rfl
    have := (hcut ⟨d, hdM⟩).mp hi
    change c ≤ d at this
    omega
  · by_contra hcd
    have hcM' : c < M := by omega
    have hi := (hcut ⟨c, hcM'⟩).mpr le_rfl
    have := (hdcut ⟨c, hcM'⟩).mp hi
    change d ≤ c at this
    omega

/-- Symmetric threshold edges on an ordered set. -/
def thresholdEdges (x y : α → ℚ) (a b : α) : Prop :=
  a < b ∧ y a < x b ∧ y b < x a

/-- Monotone horizontal coordinates and arbitrary vertical thresholds satisfy P and J. -/
theorem rules_thresholdEdges (x y : α → ℚ) (hx : Monotone x) :
    Rules (thresholdEdges x y) := by
  refine ⟨fun h => h.1, ?_, ?_⟩
  · intro a b c d hab hcd hac hcb hbd
    exact ⟨hbd, hab.2.2.trans_le (hx (hac.trans (hcb.le.trans hbd.le))),
      hcd.2.2.trans_le (hx hcb.le)⟩
  · intro a b c d e g hab hcd heg hac hcb hae heb hbd hbg
    refine ⟨lt_of_lt_of_le (max_lt hcb heb) (hbd.trans (le_max_left d g)), ?_, ?_⟩
    · rcases le_total c e with hce | hec
      · rw [max_eq_right hce]
        exact heg.2.1.trans_le (hx (le_max_right d g))
      · rw [max_eq_left hec]
        exact hcd.2.1.trans_le (hx (le_max_left d g))
    · rcases le_total d g with hdg | hgd
      · rw [max_eq_right hdg]
        exact heg.2.2.trans_le (hx (le_max_right c e))
      · rw [max_eq_left hgd]
        exact hcd.2.2.trans_le (hx (le_max_left c e))

/-- Truncate at t and make t adjacent to every smaller vertex. -/
def adjoinGreatest (E : α → α → Prop) (t a b : α) : Prop :=
  a < b ∧ b ≤ t ∧ (b = t ∨ E a b)

/-- Adjoining or deleting a greatest universal vertex preserves exactly the old rules. -/
theorem rules_adjoinGreatest_iff {E : α → α → Prop} (t : α)
    (hbound : ∀ {a b}, E a b → a < b ∧ b < t) :
    Rules (adjoinGreatest E t) ↔ Rules E := by
  constructor
  · intro h
    have lift {a b : α} (hab : E a b) : adjoinGreatest E t a b :=
      ⟨(hbound hab).1, (hbound hab).2.le, Or.inr hab⟩
    have unlift {a b : α} (hab : adjoinGreatest E t a b) (hb : b < t) : E a b :=
      hab.2.2.resolve_left (ne_of_lt hb)
    refine ⟨fun hab => (hbound hab).1, ?_, ?_⟩
    · intro a b c d hab hcd hac hcb hbd
      exact unlift (h.propagate (lift hab) (lift hcd) hac hcb hbd) (hbound hcd).2
    · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
      exact unlift (h.join (lift hab) (lift hcd) (lift hef) hac hcb hae heb hbd hbf)
        (max_lt (hbound hcd).2 (hbound hef).2)
  · intro h
    refine ⟨fun hab => hab.1, ?_, ?_⟩
    · intro a b c d hab hcd hac hcb hbd
      refine ⟨hbd, hcd.2.1, ?_⟩
      by_cases hd : d = t
      · exact Or.inl hd
      · right
        have hb : b ≠ t := ne_of_lt (hbd.trans_le hcd.2.1)
        exact h.propagate (hab.2.2.resolve_left hb) (hcd.2.2.resolve_left hd) hac hcb hbd
    · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
      have hout : max c e < max d f :=
        lt_of_lt_of_le (max_lt hcb heb) (hbd.trans (le_max_left d f))
      refine ⟨hout, max_le hcd.2.1 hef.2.1, ?_⟩
      by_cases hf' : max d f = t
      · exact Or.inl hf'
      · right
        have hlt : max d f < t :=
          lt_of_le_of_ne (max_le hcd.2.1 hef.2.1) hf'
        have hd : d ≠ t := ne_of_lt ((le_max_left d f).trans_lt hlt)
        have hf : f ≠ t := ne_of_lt ((le_max_right d f).trans_lt hlt)
        have hb : b ≠ t := ne_of_lt (hbd.trans_lt ((le_max_left d f).trans_lt hlt))
        exact h.join (hab.2.2.resolve_left hb) (hcd.2.2.resolve_left hd)
          (hef.2.2.resolve_left hf) hac hcb hae heb hbd hbf

end D5.S3.Combinatorics.MazorchukXu
