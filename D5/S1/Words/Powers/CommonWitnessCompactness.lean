/- GID: D5/S1/Words/Powers/CommonWitnessCompactness
   generality: G
   mirror-B: D5/B/S1/Words/Powers/CommonWitnessCompactness
   mirror-E: none(waiver:universal-word-family-compactness)
   anchors: []
   utility: none
   digest: Finite-character compactness for globally oriented common word witnesses.
-/

module

public import D5.S1.Words.Powers.CyclicCentralizer
public import D5.S1.Words.Powers.ConjugacyNormalForm
public import Mathlib.Data.Set.Finite.Basic

/-!
For a relation of word pairs, an inner witness solves `a ++ z = z ++ b` and an
outer witness solves the swapped equation.  The family theorem below keeps one
orientation for the whole relation.  The proof uses the finite cut normal form
for one nonempty row, then transports a second row along the resulting centralizer.
The empty row is neutral and is handled directly by cancellation.

The literature source for the finite-family argument is C. Aiswarya, Amaldev
Manuel and Saina Sunny, *Deciding Conjugacy of a Rational Relation*,
arXiv:2307.06777v4 (2026), Definition 5 and Lemma 6, p. 25.  Their printed
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

private theorem wordPower_add (m n : Nat) (w : List α) :
    wordPower (m + n) w = wordPower m w ++ wordPower n w := by
  unfold wordPower
  rw [List.replicate_add, List.flatten_append]

private theorem prefix_eq_of_length_eq {x y : List α}
    (hxy : x <+: y) (hlen : x.length = y.length) : x = y := by
  rcases hxy with ⟨r, hr⟩
  have hlen' := congrArg List.length hr
  have : r.length = 0 := by
    rw [List.length_append] at hlen'
    omega
  have hrnil : r = [] := List.eq_nil_of_length_eq_zero this
  simpa [hrnil] using hr

private theorem inner_solution_prefix_or_prefix
    {a b z₁ z₂ : List α} (ha : a ≠ [])
    (h₁ : a ++ z₁ = z₁ ++ b) (h₂ : a ++ z₂ = z₂ ++ b) :
    z₁ <+: z₂ ∨ z₂ <+: z₁ := by
  obtain ⟨⟨n₁, p₁, q₁⟩, ⟨ha₁, hb₁, hz₁, hcut₁⟩, _⟩ :=
    (ConjugacyNormalForm.conjugacy_iff_exists_unique_short_cut a b z₁ ha).mp h₁
  obtain ⟨⟨n₂, p₂, q₂⟩, ⟨ha₂, hb₂, hz₂, hcut₂⟩, _⟩ :=
    (ConjugacyNormalForm.conjugacy_iff_exists_unique_short_cut a b z₂ ha).mp h₂
  change a = p₁ ++ q₁ at ha₁
  change b = q₁ ++ p₁ at hb₁
  change z₁ = wordPower n₁ a ++ p₁ at hz₁
  change p₁.length < a.length at hcut₁
  change a = p₂ ++ q₂ at ha₂
  change b = q₂ ++ p₂ at hb₂
  change z₂ = wordPower n₂ a ++ p₂ at hz₂
  change p₂.length < a.length at hcut₂
  have hp₁ : p₁ <+: a := by
    refine ⟨q₁, ?_⟩
    exact ha₁.symm
  have hp₂ : p₂ <+: a := by
    refine ⟨q₂, ?_⟩
    exact ha₂.symm
  have hlen₁ : z₁.length = n₁ * a.length + p₁.length := by
    rw [hz₁, List.length_append, length_wordPower]
  have hlen₂ : z₂.length = n₂ * a.length + p₂.length := by
    rw [hz₂, List.length_append, length_wordPower]
  rcases Nat.le_total n₁ n₂ with hnn | hnn
  · by_cases heq : n₁ = n₂
    · subst n₂
      rcases Nat.le_total p₁.length p₂.length with hple | hple
      · rcases List.prefix_or_prefix_of_prefix hp₁ hp₂ with hp | hp
        · left
          rcases hp with ⟨r, hr⟩
          refine ⟨r, ?_⟩
          rw [hz₁, hz₂, List.append_assoc, hr]
        · have heqP : p₁ = p₂ := by
            rcases hp with ⟨r, hr⟩
            have hpr := congrArg List.length hr
            have hrlen : r.length = 0 := by
              rw [List.length_append] at hpr
              omega
            have hrnil : r = [] := List.eq_nil_of_length_eq_zero hrlen
            simpa [hrnil] using hr.symm
          subst p₂
          left
          exact ⟨[], by simp [hz₁, hz₂]⟩
      · rcases List.prefix_or_prefix_of_prefix hp₁ hp₂ with hp | hp
        · have heqP : p₁ = p₂ := by
            rcases hp with ⟨r, hr⟩
            have hpr := congrArg List.length hr
            have hrlen : r.length = 0 := by
              rw [List.length_append] at hpr
              omega
            have hrnil : r = [] := List.eq_nil_of_length_eq_zero hrlen
            simpa [hrnil] using hr
          subst p₂
          right
          exact ⟨[], by simp [hz₁, hz₂]⟩
        · right
          rcases hp with ⟨r, hr⟩
          refine ⟨r, ?_⟩
          rw [hz₂, hz₁, List.append_assoc, hr]
    · have hlt : n₁ < n₂ := Nat.lt_of_le_of_ne hnn heq
      obtain ⟨k, hk⟩ : ∃ k, n₂ = n₁ + (k + 1) := by
        refine ⟨n₂ - n₁ - 1, ?_⟩
        omega
      left
      have hprefix : p₁ <+: wordPower (k + 1) a ++ p₂ := by
        apply hp₁.trans
        refine ⟨wordPower k a ++ p₂, ?_⟩
        rw [wordPower_succ]
        simp only [List.append_assoc]
      rcases hprefix with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [hz₁, hz₂, hk, wordPower_add, List.append_assoc, hr]
      simp only [List.append_assoc]
  · by_cases heq : n₂ = n₁
    · subst n₁
      rcases Nat.le_total p₁.length p₂.length with hple | hple
      · rcases List.prefix_or_prefix_of_prefix hp₁ hp₂ with hp | hp
        · left
          rcases hp with ⟨r, hr⟩
          refine ⟨r, ?_⟩
          rw [hz₁, hz₂, List.append_assoc, hr]
        · have heqP : p₁ = p₂ := by
            rcases hp with ⟨r, hr⟩
            have hpr := congrArg List.length hr
            have hrlen : r.length = 0 := by
              rw [List.length_append] at hpr
              omega
            have hrnil : r = [] := List.eq_nil_of_length_eq_zero hrlen
            simpa [hrnil] using hr.symm
          subst p₂
          left
          exact ⟨[], by simp [hz₁, hz₂]⟩
      · rcases List.prefix_or_prefix_of_prefix hp₁ hp₂ with hp | hp
        · have heqP : p₁ = p₂ := by
            rcases hp with ⟨r, hr⟩
            have hpr := congrArg List.length hr
            have hrlen : r.length = 0 := by
              rw [List.length_append] at hpr
              omega
            have hrnil : r = [] := List.eq_nil_of_length_eq_zero hrlen
            simpa [hrnil] using hr
          subst p₂
          right
          exact ⟨[], by simp [hz₁, hz₂]⟩
        · right
          rcases hp with ⟨r, hr⟩
          refine ⟨r, ?_⟩
          rw [hz₂, hz₁, List.append_assoc, hr]
    · have hlt : n₂ < n₁ := Nat.lt_of_le_of_ne hnn heq
      obtain ⟨k, hk⟩ : ∃ k, n₁ = n₂ + (k + 1) := by
        refine ⟨n₁ - n₂ - 1, ?_⟩
        omega
      right
      have hprefix : p₂ <+: wordPower (k + 1) a ++ p₁ := by
        apply hp₂.trans
        refine ⟨wordPower k a ++ p₁, ?_⟩
        rw [wordPower_succ]
        simp only [List.append_assoc]
      rcases hprefix with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [hz₂, hz₁, hk, wordPower_add, List.append_assoc, hr]
      simp only [List.append_assoc]

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

private theorem residual_commutes_left
    {a b z t : List α} (h : a ++ z = z ++ b)
    (h' : a ++ (z ++ t) = (z ++ t) ++ b) :
    b ++ t = t ++ b := residual_commutes_right h h'

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

end D5.S1.Words.Powers.CommonWitnessCompactness
