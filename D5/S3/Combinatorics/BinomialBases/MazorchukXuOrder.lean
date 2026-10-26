/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuOrder
   mirror-E: none(waiver:universal-order-and-clique-fiber-proofs)
   anchors: [mathlib/module/Mathlib.Order.Hom.Basic]
   utility: none
   digest: Ordered clique-fiber expansion preserves the cokernel closure rules. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure

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

end D5.S3.Combinatorics.MazorchukXu
