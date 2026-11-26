/- GID: D5/S1/Words/Powers/CommonWitnessCompactness
   generality: G
   mirror-B: D5/B/S1/Words/Powers/CommonWitnessCompactness
   mirror-E: none(waiver:universal-word-family-compactness)
   anchors: []
   utility: none
   digest: Finite-character compactness for globally oriented common word witnesses. -/

module

public import D5.S1.Words.Powers.CyclicCentralizer
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Card
public import OmegaBuild.Commands

compile_only_with_mathlib

/-!
For a relation of word pairs, an inner witness solves `a ++ z = z ++ b` and an
outer witness solves the swapped equation.  The family theorem below keeps one
orientation for the whole relation.  Periodic overlaps make the witnesses of a
nonempty row prefix-comparable, enabling transport along its cyclic centralizer.
The empty row is neutral and is handled directly by cancellation.

The literature source for the finite-family argument is C. Aiswarya, Amaldev
Manuel and Saina Sunny, *Deciding Conjugacy of a Rational Relation*,
arXiv:2307.06777v4 (2026), Definition 5, p. 14, and Lemma 6, p. 25.  Their printed
lemma assumes a finite alphabet; this file proves the finite-word statement for
an arbitrary alphabet and retains empty words and empty families.
-/

public section

namespace D5.S1.Words.Powers.CommonWitnessCompactness

universe u

variable {α : Type u}


private def Inner (p : List α × List α) (z : List α) : Prop :=
  p.1 ++ z = z ++ p.2

private def Outer (p : List α × List α) (z : List α) : Prop :=
  z ++ p.1 = p.2 ++ z

def CommonWitness (G : Set (List α × List α)) : Prop :=
  ∃ z : List α, (∀ p ∈ G, Inner p z) ∨ (∀ p ∈ G, Outer p z)

private theorem inner_solution_prefix_or_prefix
    {a b z₁ z₂ : List α} (ha : a ≠ [])
    (h₁ : a ++ z₁ = z₁ ++ b) (h₂ : a ++ z₂ = z₂ ++ b) :
    z₁ <+: z₂ ∨ z₂ <+: z₁ := by
  have hapos : 0 < a.length := List.length_pos_of_ne_nil ha
  have periodic : ∀ z : List α, a ++ z = z ++ b →
      List.HasPeriod (a ++ z) a.length := by
    intro z hz
    change a ++ z <+: (a ++ z).take a.length ++ (a ++ z)
    have htake : (a ++ z).take a.length = a := by simp
    rw [htake]
    refine ⟨b, ?_⟩
    calc
      (a ++ z) ++ b = a ++ (z ++ b) := List.append_assoc ..
      _ = a ++ (a ++ z) := by rw [hz]
  have prefix_of_length : ∀ (z z' : List α),
      a ++ z = z ++ b → a ++ z' = z' ++ b → z.length ≤ z'.length →
      z <+: z' := by
    intro z z' hz hz' hlen
    apply (List.prefix_append_right_inj a).mp
    apply List.prefix_iff_getElem?.mpr
    intro j hj
    have hj' : j < (a ++ z').length := by
      simp only [List.length_append] at hj ⊢
      omega
    have hmod : j % a.length < a.length := Nat.mod_lt _ hapos
    calc
      (a ++ z')[j]? = (a ++ z')[j % a.length]? :=
        ((periodic z' hz').getElem?_mod a.length j (a ++ z') hj').symm
      _ = a[j % a.length]? := List.getElem?_append_left hmod
      _ = (a ++ z)[j % a.length]? := (List.getElem?_append_left hmod).symm
      _ = (a ++ z)[j]? := (periodic z hz).getElem?_mod a.length j (a ++ z) hj
      _ = some (a ++ z)[j] := List.getElem?_eq_getElem hj
  rcases Nat.le_total z₁.length z₂.length with hlen | hlen
  · exact Or.inl (prefix_of_length z₁ z₂ h₁ h₂ hlen)
  · exact Or.inr (prefix_of_length z₂ z₁ h₂ h₁ hlen)

private theorem residual_commutes_right
    {a b z t : List α} (h : a ++ z = z ++ b)
    (h' : a ++ (z ++ t) = (z ++ t) ++ b) :
    b ++ t = t ++ b := by
  have h₁ : z ++ (b ++ t) = z ++ (t ++ b) := by
    calc
      z ++ (b ++ t) = (z ++ b) ++ t := by simp only [List.append_assoc]
      _ = (a ++ z) ++ t := by rw [h]
      _ = a ++ (z ++ t) := by simp only [List.append_assoc]
      _ = (z ++ t) ++ b := h'
      _ = z ++ (t ++ b) := by simp only [List.append_assoc]
  exact List.append_cancel_left h₁

private theorem nonempty_right_of_inner
    {a b z : List α} (ha : a ≠ []) (h : a ++ z = z ++ b) : b ≠ [] := by
  intro hb
  subst b
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_nil, Nat.add_zero] at hlen
  have hapos : 0 < a.length := List.length_pos_of_ne_nil ha
  have hazero : a.length = 0 := by omega
  exact ha (List.eq_nil_of_length_eq_zero hazero)

private theorem commute_of_common_centralizer
    {w x y : List α} (hw : w ≠ [])
    (hx : w ++ x = x ++ w) (hy : w ++ y = y ++ w) :
    x ++ y = y ++ x := by
  obtain ⟨r, ⟨hr, hclass⟩, _⟩ := CyclicCentralizer.exists_unique_centralizer_root w hw
  obtain ⟨m, hxm⟩ := (hclass x).mp hx
  obtain ⟨n, hyn⟩ := (hclass y).mp hy
  exact (CommutingWords.commute_iff_common_power x y).mpr ⟨r, m, n, hxm, hyn⟩

private theorem commute_of_two_residuals
    {b t s : List α} (hb : b ≠ [])
    (hbt : b ++ t = t ++ b) (hbs : b ++ s = s ++ b) :
    t ++ s = s ++ t := commute_of_common_centralizer hb hbt hbs

private theorem transport_inner_witness
    {a b c d z₁ z₂ : List α} (ha : a ≠ [])
    (hab₁ : a ++ z₁ = z₁ ++ b) (hab₂ : a ++ z₂ = z₂ ++ b)
    (hcd₁ : c ++ z₁ = z₁ ++ d) (hcd₂ : c ++ z₂ = z₂ ++ d)
    (hne : z₁ ≠ z₂) :
    ∀ z : List α, a ++ z = z ++ b → c ++ z = z ++ d := by
  have hb : b ≠ [] := nonempty_right_of_inner ha hab₁
  rcases inner_solution_prefix_or_prefix ha hab₁ hab₂ with hp | hp
  · obtain ⟨t, ht⟩ := hp
    have htne : t ≠ [] := by
      intro ht0
      apply hne
      simpa [ht0] using ht
    have hbt : b ++ t = t ++ b := by
      apply residual_commutes_right hab₁
      simpa [ht]
    have hdt : d ++ t = t ++ d := by
      apply residual_commutes_right hcd₁
      simpa [ht]
    intro z haz
    rcases inner_solution_prefix_or_prefix ha hab₁ haz with hs | hs
    · obtain ⟨s, hs⟩ := hs
      have hbs : b ++ s = s ++ b := by
        apply residual_commutes_right hab₁
        simpa [hs]
      have hst : t ++ s = s ++ t := commute_of_two_residuals hb hbt hbs
      have hsd : s ++ d = d ++ s :=
        commute_of_common_centralizer htne hst hdt.symm
      calc
        c ++ z = c ++ (z₁ ++ s) := by rw [hs]
        _ = (c ++ z₁) ++ s := by simp only [List.append_assoc]
        _ = (z₁ ++ d) ++ s := by rw [hcd₁]
        _ = z₁ ++ (d ++ s) := by simp only [List.append_assoc]
        _ = z₁ ++ (s ++ d) := by rw [hsd]
        _ = (z₁ ++ s) ++ d := by simp only [List.append_assoc]
        _ = z ++ d := by rw [hs]
    · obtain ⟨s, hs⟩ := hs
      have hbs : b ++ s = s ++ b := by
        apply residual_commutes_right haz
        simpa [hs] using hab₁
      have hst : t ++ s = s ++ t := commute_of_two_residuals hb hbt hbs
      have hsd : s ++ d = d ++ s :=
        commute_of_common_centralizer htne hst hdt.symm
      have heq : (c ++ z) ++ s = (z ++ d) ++ s := by
        calc
          (c ++ z) ++ s = c ++ (z ++ s) := by simp only [List.append_assoc]
          _ = c ++ z₁ := by rw [hs]
          _ = z₁ ++ d := hcd₁
          _ = (z ++ s) ++ d := by rw [← hs]
          _ = (z ++ d) ++ s := by
            simp only [List.append_assoc]
            rw [hsd]
      exact List.append_cancel_right heq

  · obtain ⟨t, ht⟩ := hp
    have htne : t ≠ [] := by
      intro ht0
      apply hne.symm
      simpa [ht0] using ht
    have hbt : b ++ t = t ++ b := by
      apply residual_commutes_right hab₂
      simpa [ht] using hab₁
    have hdt : d ++ t = t ++ d := by
      apply residual_commutes_right hcd₂
      simpa [ht] using hcd₁
    intro z haz
    rcases inner_solution_prefix_or_prefix ha hab₂ haz with hs | hs
    · obtain ⟨s, hs⟩ := hs
      have hbs : b ++ s = s ++ b := by
        apply residual_commutes_right hab₂
        simpa [hs]
      have hst : t ++ s = s ++ t := commute_of_two_residuals hb hbt hbs
      have hsd : s ++ d = d ++ s :=
        commute_of_common_centralizer htne hst hdt.symm
      calc
        c ++ z = c ++ (z₂ ++ s) := by rw [hs]
        _ = (c ++ z₂) ++ s := by simp only [List.append_assoc]
        _ = (z₂ ++ d) ++ s := by rw [hcd₂]
        _ = z₂ ++ (d ++ s) := by simp only [List.append_assoc]
        _ = z₂ ++ (s ++ d) := by rw [hsd]
        _ = (z₂ ++ s) ++ d := by simp only [List.append_assoc]
        _ = z ++ d := by rw [hs]
    · obtain ⟨s, hs⟩ := hs
      have hbs : b ++ s = s ++ b := by
        apply residual_commutes_right haz
        simpa [hs] using hab₂
      have hst : t ++ s = s ++ t := commute_of_two_residuals hb hbt hbs
      have hsd : s ++ d = d ++ s :=
        commute_of_common_centralizer htne hst hdt.symm
      have heq : (c ++ z) ++ s = (z ++ d) ++ s := by
        calc
          (c ++ z) ++ s = c ++ (z ++ s) := by simp only [List.append_assoc]
          _ = c ++ z₂ := by rw [hs]
          _ = z₂ ++ d := hcd₂
          _ = (z ++ s) ++ d := by rw [← hs]
          _ = (z ++ d) ++ s := by
            simp only [List.append_assoc]
            rw [hsd]
      exact List.append_cancel_right heq

private theorem inner_finite_character
    (G : Set (List α × List α))
    (hfin : ∀ T : Set (List α × List α), T ⊆ G → T.Finite →
      ∃ z : List α, ∀ p ∈ T, Inner p z) :
    ∃ z : List α, ∀ p ∈ G, Inner p z := by
  classical
  by_cases hanchor : ∃ p, p ∈ G ∧ p.1 ≠ []
  · obtain ⟨p₀, hp₀, ha⟩ := hanchor
    have pair_witness : ∀ p, p ∈ G →
        ∃ z, Inner p₀ z ∧ Inner p z := by
      intro p hp
      obtain ⟨z, hz⟩ := hfin (insert p₀ {p}) (by
        intro q hq
        rcases Set.mem_insert_iff.mp hq with rfl | hq
        · exact hp₀
        · exact Set.mem_singleton_iff.mp hq ▸ hp)
        (Set.Finite.insert p₀ (Set.finite_singleton p))
      exact ⟨z, hz p₀ (by simp), hz p (by simp)⟩
    by_cases hmany : ∀ p, p ∈ G →
        ∃ z₁ z₂, Inner p₀ z₁ ∧ Inner p z₁ ∧
          Inner p₀ z₂ ∧ Inner p z₂ ∧ z₁ ≠ z₂
    · obtain ⟨z₀, hz₀⟩ := hfin {p₀} (by
        intro p hp
        exact Set.mem_singleton_iff.mp hp ▸ hp₀) (Set.finite_singleton p₀)
      have hz₀' : Inner p₀ z₀ := hz₀ p₀ (by simp)
      refine ⟨z₀, ?_⟩
      intro p hp
      obtain ⟨z₁, z₂, h₁, h₂, h₃, h₄, hne⟩ := hmany p hp
      exact (transport_inner_witness (a := p₀.1) (b := p₀.2)
        (c := p.1) (d := p.2) (z₁ := z₁) (z₂ := z₂)
        ha h₁ h₃ h₂ h₄ hne) z₀ hz₀'
    · push Not at hmany
      obtain ⟨p, hp, huniq⟩ := hmany
      obtain ⟨zc, hzc₀, hzc⟩ := pair_witness p hp
      refine ⟨zc, ?_⟩
      intro q hq
      obtain ⟨z, hz⟩ := hfin (insert p₀ (insert p {q})) (by
        intro r hr
        rcases Set.mem_insert_iff.mp hr with rfl | hr
        · exact hp₀
        · rcases Set.mem_insert_iff.mp hr with rfl | hr
          · exact hp
          · exact Set.mem_singleton_iff.mp hr ▸ hq)
        (Set.Finite.insert p₀ (Set.Finite.insert p (Set.finite_singleton q)))
      have hz₀ : Inner p₀ z := hz p₀ (by simp)
      have hzp : Inner p z := hz p (by simp)
      have hzq : Inner q z := hz q (by simp)
      have heq : z = zc := huniq z zc hz₀ hzp hzc₀ hzc
      exact heq ▸ hzq
  · have hfirst : ∀ p, p ∈ G → p.1 = [] := by
      intro p hp
      by_contra hne
      exact hanchor ⟨p, hp, hne⟩
    refine ⟨[], ?_⟩
    intro p hp
    obtain ⟨z, hz⟩ := hfin {p} (by
      intro q hq
      exact Set.mem_singleton_iff.mp hq ▸ hp) (Set.finite_singleton p)
    have hrow := hz p (by simp)
    have hsecond : p.2 = [] := by
      have hlen := congrArg List.length hrow
      simp only [hfirst p hp, List.nil_append, List.length_append,
        List.length_nil, Nat.add_zero] at hlen
      have hzpos : 0 ≤ z.length := Nat.zero_le _
      exact List.eq_nil_of_length_eq_zero (by omega)
    simp [Inner, hfirst p hp, hsecond]

private def swapPair (p : List α × List α) : List α × List α := (p.2, p.1)

private theorem outer_finite_character
    (G : Set (List α × List α))
    (hfin : ∀ T : Set (List α × List α), T ⊆ G → T.Finite →
      ∃ z : List α, ∀ p ∈ T, Outer p z) :
    ∃ z : List α, ∀ p ∈ G, Outer p z := by
  let H : Set (List α × List α) := {q | swapPair q ∈ G}
  have hfinH : ∀ T : Set (List α × List α), T ⊆ H → T.Finite →
      ∃ z : List α, ∀ q ∈ T, Inner q z := by
    intro T hT hTf
    obtain ⟨z, hz⟩ := hfin (T.image swapPair) (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hT hq) (hTf.image swapPair)
    refine ⟨z, ?_⟩
    intro q hq
    have hq' := hz (swapPair q) ⟨q, hq, rfl⟩
    exact hq'.symm
  obtain ⟨z, hz⟩ := inner_finite_character H hfinH
  refine ⟨z, ?_⟩
  intro p hp
  have hq : swapPair p ∈ H := by
    change swapPair (swapPair p) ∈ G
    simpa [swapPair] using hp
  exact (hz (swapPair p) hq).symm

theorem commonWitness_iff_finite
    (G : Set (List α × List α)) :
    CommonWitness G ↔
      ∀ T : Set (List α × List α), T ⊆ G → T.Finite → CommonWitness T := by
  constructor
  · rintro ⟨z, hinner | houter⟩ T hTG hTf
    · exact ⟨z, Or.inl (fun p hp => hinner p (hTG hp))⟩
    · exact ⟨z, Or.inr (fun p hp => houter p (hTG hp))⟩
  · intro hfin
    classical
    by_cases hIF : ∀ T : Set (List α × List α), T ⊆ G → T.Finite →
        ∃ z : List α, ∀ p ∈ T, Inner p z
    · obtain ⟨z, hz⟩ := inner_finite_character G hIF
      exact ⟨z, Or.inl hz⟩
    · push Not at hIF
      obtain ⟨T₀, hT₀G, hT₀f, hT₀no⟩ := hIF
      have hOF : ∀ T : Set (List α × List α), T ⊆ G → T.Finite →
          ∃ z : List α, ∀ p ∈ T, Outer p z := by
        intro T hTG hTf
        obtain ⟨z, hzI | hzO⟩ := hfin (T ∪ T₀) (by
          intro p hp
          rcases hp with hp | hp
          · exact hTG hp
          · exact hT₀G hp) (hTf.union hT₀f)
        · exfalso
          obtain ⟨p, hp, hbad⟩ := hT₀no z
          exact hbad (hzI p (Set.mem_union_right T hp))
        · exact ⟨z, fun p hp => hzO p (Set.mem_union_left T₀ hp)⟩
      obtain ⟨z, hz⟩ := outer_finite_character G hOF
      exact ⟨z, Or.inr hz⟩

/- A signed word has only one empty representative. -/
private abbrev SignedWord (α : Type u) := List α ⊕ {z : List α // z ≠ []}

private def SignedHolds (p : List α × List α) : SignedWord α → Prop
  | .inl z => Inner p z
  | .inr z => Outer p z.1

private theorem signed_of_common {G : Set (List α × List α)}
    (h : CommonWitness G) : ∃ s : SignedWord α, ∀ p ∈ G, SignedHolds p s := by
  classical
  obtain ⟨z, hz | hz⟩ := h
  · exact ⟨.inl z, hz⟩
  · by_cases hne : z = []
    · refine ⟨.inl [], ?_⟩
      intro p hp
      simpa [SignedHolds, Inner, Outer, hne] using (hz p hp).symm
    · exact ⟨.inr ⟨z, hne⟩, hz⟩

private theorem common_of_signed {G : Set (List α × List α)}
    (h : ∃ s : SignedWord α, ∀ p ∈ G, SignedHolds p s) : CommonWitness G := by
  obtain ⟨s, hs⟩ := h
  cases s with
  | inl z => exact ⟨z, .inl hs⟩
  | inr z => exact ⟨z.1, .inr hs⟩

private theorem sandwich_inner {p : List α × List α} {x y : List α}
    (hx : Inner p x) (hy : Outer p y) : Inner p (x ++ y ++ x) := by
  change p.1 ++ (x ++ y ++ x) = (x ++ y ++ x) ++ p.2
  change p.1 ++ x = x ++ p.2 at hx
  change y ++ p.1 = p.2 ++ y at hy
  calc
    p.1 ++ (x ++ y ++ x) = (p.1 ++ x) ++ y ++ x := by simp [List.append_assoc]
    _ = (x ++ p.2) ++ y ++ x := by rw [hx]
    _ = x ++ (p.2 ++ y) ++ x := by simp [List.append_assoc]
    _ = x ++ (y ++ p.1) ++ x := by rw [hy]
    _ = (x ++ y) ++ (p.1 ++ x) := by simp [List.append_assoc]
    _ = (x ++ y) ++ (x ++ p.2) := by rw [hx]
    _ = (x ++ y ++ x) ++ p.2 := by simp [List.append_assoc]

private theorem outer_of_sandwich {p : List α × List α} {x y : List α}
    (hx : Inner p x) (hxyx : Inner p (x ++ y ++ x)) : Outer p y := by
  change p.1 ++ x = x ++ p.2 at hx
  change p.1 ++ (x ++ y ++ x) = (x ++ y ++ x) ++ p.2 at hxyx
  have heq : x ++ ((p.2 ++ y) ++ x) = x ++ ((y ++ p.1) ++ x) := by
    calc
      x ++ ((p.2 ++ y) ++ x) = (p.1 ++ x) ++ y ++ x := by
        rw [hx]; simp [List.append_assoc]
      _ = (x ++ y ++ x) ++ p.2 := by simpa [List.append_assoc] using hxyx
      _ = x ++ ((y ++ p.1) ++ x) := by rw [hx]; simp [List.append_assoc]
  exact (List.append_cancel_right (List.append_cancel_left heq)).symm

private theorem signed_transport_of_two_inner
    {p q : List α × List α} {x y : List α} (hp : p.1 ≠ [])
    (hpx : Inner p x) (hpy : Inner p y)
    (hqx : Inner q x) (hqy : Inner q y) (hne : x ≠ y) :
    ∀ s : SignedWord α, SignedHolds p s → SignedHolds q s := by
  have htransport : ∀ z, Inner p z → Inner q z :=
    transport_inner_witness hp hpx hpy hqx hqy hne
  intro s hs
  cases s with
  | inl z => exact htransport z hs
  | inr z =>
      exact outer_of_sandwich hqx (htransport _ (sandwich_inner hpx hs))

private theorem signed_transport_of_two_outer
    {p q : List α × List α} {x y : List α} (hp : p.1 ≠ [])
    (hpx : Outer p x) (hpy : Outer p y)
    (hqx : Outer q x) (hqy : Outer q y) (hne : x ≠ y) :
    ∀ s : SignedWord α, SignedHolds p s → SignedHolds q s := by
  have hp' : p.2 ≠ [] := nonempty_right_of_inner hp hpx.symm
  have htransport : ∀ z, Outer p z → Outer q z := by
    intro z hz
    exact (transport_inner_witness hp' hpx.symm hpy.symm hqx.symm hqy.symm hne
      z hz.symm).symm
  intro s hs
  cases s with
  | inr z => exact htransport z.1 hs
  | inl z =>
      have hpx' : Inner (swapPair p) x := hpx.symm
      have hpz' : Outer (swapPair p) z := hs.symm
      have hsand : Outer p (x ++ z ++ x) := (sandwich_inner hpx' hpz').symm
      have hqx' : Inner (swapPair q) x := hqx.symm
      have hqs' : Inner (swapPair q) (x ++ z ++ x) := (htransport _ hsand).symm
      exact (outer_of_sandwich hqx' hqs').symm

private theorem signed_transport_of_two
    {p q : List α × List α} (hp : p.1 ≠ [])
    {s t : SignedWord α} (hps : SignedHolds p s) (hpt : SignedHolds p t)
    (hqs : SignedHolds q s) (hqt : SignedHolds q t) (hne : s ≠ t) :
    ∀ r : SignedWord α, SignedHolds p r → SignedHolds q r := by
  have mixed : ∀ (x : List α) (y : {z : List α // z ≠ []}),
      Inner p x → Outer p y.1 → Inner q x → Outer q y.1 →
      ∀ r : SignedWord α, SignedHolds p r → SignedHolds q r := by
    intro x y hpx hpy hqx hqy
    apply signed_transport_of_two_inner hp hpx (sandwich_inner hpx hpy)
      hqx (sandwich_inner hqx hqy)
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_append] at hlen
    have hyzero : y.1.length = 0 := by omega
    exact y.2 (List.eq_nil_of_length_eq_zero hyzero)
  cases s with
  | inl x =>
      cases t with
      | inl y =>
          exact signed_transport_of_two_inner hp hps hpt hqs hqt
            (fun h => hne (congrArg Sum.inl h))
      | inr y => exact mixed x y hps hpt hqs hqt
  | inr x =>
      cases t with
      | inl y => exact mixed y x hpt hps hqt hqs
      | inr y =>
          apply signed_transport_of_two_outer hp hps hpt hqs hqt
          intro h
          exact hne (congrArg Sum.inr (Subtype.ext h))

/-- Three-row finite character, with independently chosen local orientations. -/
theorem commonWitness_iff_three
    (G : Set (List α × List α)) :
    CommonWitness G ↔
      ∀ T : Set (List α × List α), T ⊆ G → T.Finite → T.ncard ≤ 3 →
        CommonWitness T := by
  constructor
  · intro h T hTG _ _
    obtain ⟨z, hz | hz⟩ := h
    · exact ⟨z, .inl (fun p hp => hz p (hTG hp))⟩
    · exact ⟨z, .inr (fun p hp => hz p (hTG hp))⟩
  · intro hthree
    classical
    have hlocal : ∀ p ∈ G, ∀ q ∈ G, ∀ r ∈ G,
        ∃ s : SignedWord α,
          SignedHolds p s ∧ SignedHolds q s ∧ SignedHolds r s := by
      intro p hp q hq r hr
      have hsub : insert p (insert q {r}) ⊆ G := by
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · exact hp
        · exact hq
        · exact hr
      have hcard : (insert p (insert q {r})).ncard ≤ 3 := by
        have h₁ := Set.ncard_insert_le p (insert q {r})
        have h₂ := Set.ncard_insert_le q {r}
        have h₃ := Set.ncard_singleton r
        omega
      obtain ⟨s, hs⟩ := signed_of_common (hthree _ hsub
        ((Set.finite_singleton r).insert q |>.insert p) hcard)
      exact ⟨s, hs p (by simp), hs q (by simp), hs r (by simp)⟩
    by_cases hanchor : ∃ p, p ∈ G ∧ p.1 ≠ []
    · obtain ⟨p, hp, hpne⟩ := hanchor
      by_cases hmany : ∀ q, q ∈ G → ∃ s t : SignedWord α,
          SignedHolds p s ∧ SignedHolds q s ∧
          SignedHolds p t ∧ SignedHolds q t ∧ s ≠ t
      · obtain ⟨s, hps, _, _⟩ := hlocal p hp p hp p hp
        apply common_of_signed
        refine ⟨s, ?_⟩
        intro q hq
        obtain ⟨t, r, hpt, hqt, hpr, hqr, hne⟩ := hmany q hq
        exact signed_transport_of_two hpne hpt hpr hqt hqr hne s hps
      · push Not at hmany
        obtain ⟨q, hq, huniq⟩ := hmany
        obtain ⟨s, hps, hqs, _⟩ := hlocal p hp q hq q hq
        apply common_of_signed
        refine ⟨s, ?_⟩
        intro r hr
        obtain ⟨t, hpt, hqt, hrt⟩ := hlocal p hp q hq r hr
        have heq : t = s := huniq t s hpt hqt hps hqs
        exact heq ▸ hrt
    · have hfirst : ∀ p ∈ G, p.1 = [] := by
        intro p hp
        by_contra hne
        exact hanchor ⟨p, hp, hne⟩
      refine ⟨[], .inl ?_⟩
      intro p hp
      obtain ⟨s, hs, _, _⟩ := hlocal p hp p hp p hp
      have hsecond : p.2 = [] := by
        cases s with
        | inl z =>
            have hlen := congrArg List.length hs
            simp only [SignedHolds, Inner, hfirst p hp, List.nil_append,
              List.length_append] at hlen
            exact List.eq_nil_of_length_eq_zero (by omega)
        | inr z =>
            have hlen := congrArg List.length hs
            simp only [SignedHolds, Outer, hfirst p hp, List.append_nil,
              List.length_append] at hlen
            exact List.eq_nil_of_length_eq_zero (by omega)
      simp [Inner, hfirst p hp, hsecond]

end D5.S1.Words.Powers.CommonWitnessCompactness
