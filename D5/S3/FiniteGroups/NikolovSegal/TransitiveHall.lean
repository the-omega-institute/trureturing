/- GID: D5/S3/FiniteGroups/NikolovSegal/TransitiveHall
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TransitiveHall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hall selections on actual cycles and consecutive generator intervals. -/

import D5.S3.FiniteGroups.NikolovSegal.TransitiveCoverage
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false
namespace NikolovSegal
universe u

theorem finite_degree_matching
    {W M : Type*} [Fintype W] [Fintype M] [DecidableEq W] [DecidableEq M]
    (q : ℕ) (hq : 0 < q) (t : W → Finset M)
    (hM : ∀ m : M, (Finset.univ.filter (fun w : W => m ∈ t w)).card ≤ q)
    (hW : ∀ w : W, q ≤ (t w).card) :
    ∃ f : W → M, Function.Injective f ∧ ∀ w, f w ∈ t w := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp
  intro A
  let E : Finset (Σ w : W, M) := A.sigma t
  let U : Finset M := A.biUnion t
  have hE : E.card = ∑ w ∈ A, (t w).card := by
    simp [E]
  have hEA : E.card ≥ q * A.card := by
    rw [hE]
    calc
      q * A.card = ∑ w ∈ A, q := by simp [Nat.mul_comm]
      _ ≤ ∑ w ∈ A, (t w).card := by
        apply Finset.sum_le_sum
        intro w hw
        exact hW w
  have hmap : E.card = ∑ m ∈ U, (E.filter (fun e => e.2 = m)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro e he
    change e.2 ∈ U
    change e ∈ A.sigma t at he
    exact Finset.mem_biUnion.mpr
      ⟨e.1, (Finset.mem_sigma.mp he).1, (Finset.mem_sigma.mp he).2⟩
  have hfiber : ∀ m ∈ U, (E.filter (fun e => e.2 = m)).card ≤
      (Finset.univ.filter (fun w : W => m ∈ t w)).card := by
    intro m hm
    let F : Finset (Σ w : W, M) := E.filter (fun e => e.2 = m)
    have hinj : Set.InjOn (fun e : (Σ w : W, M) => e.1) F := by
      intro a ha b hb hab
      apply Sigma.ext hab
      have ha' : a.2 = m :=
        (Finset.mem_filter.mp
          (show a ∈ E.filter (fun e => e.2 = m) from ha)).2
      have hb' : b.2 = m :=
        (Finset.mem_filter.mp
          (show b ∈ E.filter (fun e => e.2 = m) from hb)).2
      exact heq_of_eq (ha'.trans hb'.symm)
    calc
      (E.filter (fun e => e.2 = m)).card = F.card := by rfl
      _ = (F.image (fun e => e.1)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ.filter (fun w : W => m ∈ t w)).card := by
        apply Finset.card_le_card
        intro w hw
        simp only [Finset.mem_image] at hw
        obtain ⟨e, he, rfl⟩ := hw
        have heF : e ∈ E.filter (fun e => e.2 = m) := by exact he
        have heE : e ∈ A.sigma t := (Finset.mem_filter.mp heF).1
        have het : e.2 ∈ t e.1 := (Finset.mem_sigma.mp heE).2
        have hem : e.2 = m := (Finset.mem_filter.mp heF).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [hem] using het
  have hEU : E.card ≤ q * U.card := by
    rw [hmap]
    calc
      (∑ m ∈ U, (E.filter (fun e => e.2 = m)).card) ≤ ∑ m ∈ U, q := by
        apply Finset.sum_le_sum
        intro m hm
        exact (hfiber m hm).trans (hM m)
      _ = q * U.card := by simp [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left (hEA.trans hEU) hq

theorem finite_cycle_incidence_matching
    {O J I : Type*} [Fintype O] [Fintype J] [Fintype I]
    [DecidableEq O] [DecidableEq J] [DecidableEq I]
    (q : ℕ) (hq : 0 < q) (rep : O → I) (hinjrep : Function.Injective rep)
    (good : J → I → Prop) (cyc : J → I → Finset I)
    [∀ j, DecidablePred (good j)]
    (hcard : ∀ j x, good j x → (cyc j x).card ≤ q)
    (hfixed : ∀ o, q ≤ (Finset.univ.filter (fun j => good j (rep o))).card)
    (hcycle : ∀ j o, good j (rep o) → rep o ∈ cyc j (rep o)) :
    ∃ f : O → J × Finset I, Function.Injective f ∧
      ∀ o, good (f o).1 (rep o) ∧ (f o).2 = cyc (f o).1 (rep o) ∧
        rep o ∈ (f o).2 := by
  classical
  let t : O → Finset (J × Finset I) := fun o =>
    (Finset.univ.filter (fun j : J => good j (rep o))).image
      (fun j => (j, cyc j (rep o)))
  have hM : ∀ p : J × Finset I,
      (Finset.univ.filter (fun o : O => p ∈ t o)).card ≤ q := by
    intro p
    let A : Finset O := Finset.univ.filter (fun o : O => p ∈ t o)
    let R : Finset I := A.image rep
    have hR : R.card = A.card := by
      apply Finset.card_image_of_injOn
      intro o ho o' ho' heq
      exact hinjrep heq
    have hRA : R ⊆ p.2 := by
      intro x hx
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hx
      have hto : p ∈ t o := (Finset.mem_filter.mp
        (show o ∈ Finset.univ.filter (fun o : O => p ∈ t o) from ho)).2
      obtain ⟨j, hj, hp⟩ := Finset.mem_image.mp hto
      have hpc : cyc j (rep o) = p.2 := congrArg Prod.snd hp
      have hgood : good j (rep o) := (Finset.mem_filter.mp hj).2
      rw [← hpc]
      exact hcycle j o hgood
    by_cases hA : A.Nonempty
    · let o := Classical.choose hA
      have ho : o ∈ A := Classical.choose_spec hA
      have hto : p ∈ t o := (Finset.mem_filter.mp
        (show o ∈ Finset.univ.filter (fun o : O => p ∈ t o) from ho)).2
      obtain ⟨j, hj, hp⟩ := Finset.mem_image.mp hto
      have hpc : cyc j (rep o) = p.2 := congrArg Prod.snd hp
      have hgood : good j (rep o) := (Finset.mem_filter.mp hj).2
      have hRq : R.card ≤ q := by
        calc
          R.card ≤ p.2.card := Finset.card_le_card hRA
          _ = (cyc j (rep o)).card := by rw [hpc]
          _ ≤ q := hcard j (rep o) hgood
      simpa [hR] using hRq
    · have hAc : A.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hA)
      change A.card ≤ q
      omega
  have hW : ∀ o : O, q ≤ (t o).card := by
    intro o
    let B : Finset J := Finset.univ.filter (fun j => good j (rep o))
    let V : Finset (J × Finset I) := B.image (fun j => (j, cyc j (rep o)))
    have hV : V.card = B.card := by
      rw [Finset.card_image_of_injective]
      intro a b hab
      exact congrArg Prod.fst hab
    have hVB : V ⊆ t o := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      simp only [t]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    calc
      q ≤ B.card := hfixed o
      _ = V.card := hV.symm
      _ ≤ (t o).card := Finset.card_le_card hVB
  obtain ⟨f, hf, hft⟩ := finite_degree_matching q hq t hM hW
  refine ⟨f, hf, ?_⟩
  intro o
  obtain ⟨j, hj, hp⟩ := Finset.mem_image.mp (hft o)
  have hgood : good (f o).1 (rep o) := by
    rw [← congrArg Prod.fst hp]
    exact (Finset.mem_filter.mp hj).2
  have hcyc : (f o).2 = cyc (f o).1 (rep o) := by
    rw [← congrArg Prod.snd hp, ← congrArg Prod.fst hp]
  have hmem : rep o ∈ (f o).2 := by
    rw [← congrArg Prod.snd hp]
    exact hcycle j o (Finset.mem_filter.mp hj).2
  exact ⟨hgood, hcyc, hmem⟩

private theorem periodicOrbit_toFinset_card {I : Type u} [DecidableEq I]
    (f : I → I) (x : I) :
    (Function.periodicOrbit f x).toFinset.card = Function.minimalPeriod f x := by
  have hn := Function.nodup_periodicOrbit (f := f) (x := x)
  induction hs : Function.periodicOrbit f x using Quotient.inductionOn' with
  | _ l =>
    have hn' : l.Nodup := by
      rw [← Cycle.nodup_coe_iff]
      simpa [hs] using hn
    change l.toFinset.card = _
    rw [List.toFinset_card_of_nodup hn']
    have hlen : l.length = (Function.periodicOrbit f x).length := by
      rw [hs]
      exact (Cycle.length_coe l).symm
    calc
      l.length = (Function.periodicOrbit f x).length := hlen
      _ = Function.minimalPeriod f x := Function.periodicOrbit_length

private theorem periodicOrbit_mem_toFinset {I : Type u} [DecidableEq I]
    (f : I → I) (x : I) (hx : x ∈ Function.periodicPts f) :
    x ∈ (Function.periodicOrbit f x).toFinset := by
  apply Multiset.mem_toFinset.mpr
  induction hs : Function.periodicOrbit f x using Quotient.inductionOn' with
  | _ l =>
    change x ∈ (↑l : Cycle I).toMultiset
    change x ∈ l
    have hm := Function.self_mem_periodicOrbit hx
    rw [hs] at hm
    exact hm

def ConsecutiveInterval {m : ℕ} (X : Finset (Fin m)) : Prop :=
  ∀ ⦃a b c : Fin m⦄, a ∈ X → b ∈ X → a ≤ c → c ≤ b → c ∈ X

private def consecutiveBlock {m L K : ℕ} (hL : 0 < L) (hbound : K * L ≤ m)
    (t : Fin K) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin L)).image (fun a =>
    ⟨t.val * L + a.val, by
      have ht : t.val + 1 ≤ K := Nat.succ_le_of_lt t.isLt
      have hu : (t.val + 1) * L ≤ K * L := Nat.mul_le_mul_right L ht
      rw [Nat.add_mul] at hu
      omega⟩)

theorem consecutive_block_family {m q D M : ℕ} (hq : 0 < q) (hD : 0 < D) (hM : 0 < M)
    (hm : M * D * (q + D) ≤ m) :
    ∃ X : Fin (M * D) → Finset (Fin m),
      (∀ t, ConsecutiveInterval (X t)) ∧
      (∀ ⦃t t'⦄, t ≠ t' → Disjoint (X t) (X t')) ∧
      (∀ t, (X t).card = q + D) := by
  let L := q + D
  have hL : 0 < L := by dsimp [L]; omega
  let K := M * D
  have hbound : K * L ≤ m := by simpa [K, L] using hm
  let X : Fin K → Finset (Fin m) := fun t => consecutiveBlock hL hbound t
  have hcard : ∀ t, (X t).card = L := by
    intro t
    have hinj : Function.Injective (fun a : Fin L =>
        (⟨t.val * L + a.val, by
          have ht : t.val + 1 ≤ K := Nat.succ_le_of_lt t.isLt
          have hu : (t.val + 1) * L ≤ K * L := Nat.mul_le_mul_right L ht
          rw [Nat.add_mul] at hu
          omega⟩ : Fin m)) := by
      intro a b hab
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val hab)
    simp [X, consecutiveBlock, Finset.card_image_of_injective _ hinj, L]
  have hinterval : ∀ t, ConsecutiveInterval (X t) := by
    intro t a b c ha hb hac hcb
    obtain ⟨a', ha', hax⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', hbx⟩ := Finset.mem_image.mp hb
    have ha_val : t.val * L + a'.val = a.val := congrArg Fin.val hax
    have hb_val : t.val * L + b'.val = b.val := congrArg Fin.val hbx
    have hac' : a.val ≤ c.val := hac
    have hcb' : c.val ≤ b.val := hcb
    rw [← ha_val] at hac'
    rw [← hb_val] at hcb'
    have hlow : t.val * L ≤ c.val := by omega
    have hu : (t.val + 1) * L ≤ K * L := by
      apply Nat.mul_le_mul_right L
      exact Nat.succ_le_of_lt t.isLt
    rw [Nat.add_mul] at hu
    have hu' : c.val < t.val * L + L := by omega
    let z : Fin L := ⟨c.val - t.val * L, by omega⟩
    change c ∈ consecutiveBlock hL hbound t
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp [z]
    omega
  have hdisjoint : ∀ ⦃t t' : Fin K⦄, t ≠ t' → Disjoint (X t) (X t') := by
    intro t t' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx'
    have hax' : t.val * L + a.val = x.val := congrArg Fin.val hax
    have hbx' : t'.val * L + b.val = x.val := congrArg Fin.val hbx
    have htu : x.val < (t.val + 1) * L := by
      rw [Nat.add_mul]
      omega
    have htl' : t'.val * L ≤ x.val := by omega
    have htu' : x.val < (t'.val + 1) * L := by
      rw [Nat.add_mul]
      omega
    have htl : t.val * L ≤ x.val := by omega
    have hval : t.val ≠ t'.val := by
      intro h
      apply hne
      apply Fin.ext
      exact h
    rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
    · have hs : t.val + 1 ≤ t'.val := Nat.succ_le_of_lt hlt
      have hm := Nat.mul_le_mul_right L hs
      rw [Nat.add_mul] at hm
      omega
    · have hs : t'.val + 1 ≤ t.val := Nat.succ_le_of_lt hgt
      have hm := Nat.mul_le_mul_right L hs
      rw [Nat.add_mul] at hm
      omega
  refine ⟨X, hinterval, hdisjoint, ?_⟩
  intro t
  simpa [L] using hcard t

def fixedChoice {m : ℕ} {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (good : Fin m → I → Prop) [∀ j, DecidablePred (good j)]
    (rep : O → I) (o : O) : Finset (Fin m) :=
  Finset.univ.filter (fun j => good j (rep o))

def badChoice {m : ℕ} {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (good : Fin m → I → Prop) [∀ j, DecidablePred (good j)]
    (rep : O → I) (o : O) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ¬ good j (rep o))

private def pref {m : ℕ} (b : Finset (Fin m)) (j : Fin m) : Finset (Fin m) :=
  b.filter (fun x => x < j)

def prefixPiece {m D : ℕ} {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (good : Fin m → I → Prop) [∀ j, DecidablePred (good j)]
    (rep : O → I) (o : O) (d : Fin D) : Finset (Fin m) :=
  (fixedChoice good rep o).filter (fun j => (pref (badChoice good rep o) j).card = d.val)

 theorem fixed_choice_prefix_cover {m D : ℕ} {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (good : Fin m → I → Prop) [∀ j, DecidablePred (good j)]
    (rep : O → I)
    (hbad : ∀ o, (badChoice good rep o).card < D) (hD : 0 < D) :
    ∀ o, fixedChoice good rep o ⊆ (Finset.univ : Finset (Fin D)).biUnion (prefixPiece good rep o) := by
  intro o j hj
  have hsub : pref (badChoice good rep o) j ⊆ badChoice good rep o := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hlt : (pref (badChoice good rep o) j).card < D :=
    (Finset.card_le_card hsub).trans_lt (hbad o)
  let d : Fin D := ⟨(pref (badChoice good rep o) j).card, hlt⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_univ d, ?_⟩
  simp only [prefixPiece, Finset.mem_filter]
  exact ⟨hj, rfl⟩

 theorem fixed_choice_prefix_interval {m D : ℕ} {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    (good : Fin m → I → Prop) [∀ j, DecidablePred (good j)]
    (rep : O → I) (o : O) (d : Fin D) :
    ConsecutiveInterval (prefixPiece good rep o d) := by
  intro a b c ha hb hac hcb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hsub_ac : pref (badChoice good rep o) a ⊆ pref (badChoice good rep o) c := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨hx'.1, lt_of_lt_of_le hx'.2 hac⟩
  have hsub_cb : pref (badChoice good rep o) c ⊆ pref (badChoice good rep o) b := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    exact ⟨hx'.1, lt_of_lt_of_le hx'.2 hcb⟩
  have hcarda : (pref (badChoice good rep o) a).card = d.val := ha'.2
  have hcardb : (pref (badChoice good rep o) b).card = d.val := hb'.2
  have hgoodb : good b (rep o) := (Finset.mem_filter.mp hb'.1).2
  have hleac := Finset.card_le_card hsub_ac
  have hlecb := Finset.card_le_card hsub_cb
  have hcardc : (pref (badChoice good rep o) c).card = d.val := by omega
  have hgoodc : good c (rep o) := by
    by_contra hgc
    have hcbstrict : c < b := by
      by_cases hcb_eq : c = b
      · subst b
        exact False.elim (hgc hgoodb)
      · exact lt_of_le_of_ne hcb hcb_eq
    have hmem_b : c ∈ pref (badChoice good rep o) b := by
      simp only [pref, Finset.mem_filter]
      exact ⟨by simp [badChoice, hgc], hcbstrict⟩
    have hnot_c : c ∉ pref (badChoice good rep o) c := by
      simp [pref]
    have hproper : pref (badChoice good rep o) c ⊂ pref (badChoice good rep o) b :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub_cb, by
        intro heq
        exact hnot_c (heq ▸ hmem_b)⟩
    have hltcard := Finset.card_lt_card hproper
    omega
  have hgc_mem : c ∈ fixedChoice good rep o := by
    simp [fixedChoice, hgoodc]
  exact Finset.mem_filter.mpr ⟨hgc_mem, hcardc⟩

theorem finite_cover_pigeonhole
    {α : Type*} [Fintype α] [DecidableEq α]
    {D M : ℕ} (hD : 0 < D) (hM : 0 < M)
    (s : Finset α) (cover : Fin D → Finset α)
    (hsub : s ⊆ (Finset.univ : Finset (Fin D)).biUnion cover)
    (hcard : M * D ≤ s.card) :
    ∃ d : Fin D, M ≤ (s ∩ cover d).card := by
  classical
  letI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  by_contra h
  push_neg at h
  let pieces : Fin D → Finset α := fun d => s ∩ cover d
  let U : Finset α := (Finset.univ : Finset (Fin D)).biUnion pieces
  have hsubU : s ⊆ U := by
    intro a ha
    have ha' := hsub ha
    obtain ⟨d, hd, had⟩ := Finset.mem_biUnion.mp ha'
    apply Finset.mem_biUnion.mpr
    have hpiece : a ∈ s ∩ cover d := by
      simp only [Finset.mem_inter]
      exact ⟨ha, had⟩
    exact ⟨d, Finset.mem_univ d, by simpa [pieces] using hpiece⟩
  have hsU : s.card ≤ U.card := Finset.card_le_card hsubU
  have hU : U.card ≤ ∑ d : Fin D, (pieces d).card := by
    exact Finset.card_biUnion_le
  have hsum : (∑ d : Fin D, (pieces d).card) < M * D := by
    have hle : ∀ d : Fin D, (pieces d).card ≤ M - 1 := by
      intro d
      have hd := h d
      dsimp [pieces] at hd ⊢
      omega
    have hlt : (∑ d : Fin D, (pieces d).card) ≤
        ∑ d : Fin D, (M - 1) := by
      exact Finset.sum_le_sum (fun d _ => hle d)
    have hpred : (∑ d : Fin D, (M - 1)) < ∑ d : Fin D, M := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      intro d hd
      omega
    have hconst : (∑ d : Fin D, M) = M * D := by
      simp [Finset.sum_const, Nat.mul_comm]
    exact hlt.trans_lt (hpred.trans_eq hconst)
  exact (Nat.not_lt_of_ge (hcard.trans (hsU.trans hU))) hsum

theorem lemma10_3_repeated_matching
    {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    {m q D M : ℕ} (hq : 0 < q) (X : Fin (M * D) → Finset (Fin m))
    (hinterval : ∀ t, ConsecutiveInterval (X t))
    (hdisjoint : ∀ ⦃t t' : Fin (M * D)⦄, t ≠ t' → Disjoint (X t) (X t'))
    (hcardX : ∀ t, q + D ≤ (X t).card)
    (rep : O → I) (hinjrep : Function.Injective rep)
    (good : Fin m → I → Prop)
    (cyc : Fin m → I → Finset I)
    [∀ j, DecidablePred (good j)]
    (hcard : ∀ j x, good j x → (cyc j x).card ≤ q)
    (hbad : ∀ o,
      (Finset.univ.filter (fun j : Fin m => ¬ good j (rep o))).card < D)
    (hcycle : ∀ j o, good j (rep o) → rep o ∈ cyc j (rep o)) :
    ∃ pick : Fin (M * D) → O → Fin m × Finset I,
      (∀ t, Function.Injective (pick t)) ∧
      (∀ t o, (pick t o).1 ∈ X t ∧
        good (pick t o).1 (rep o) ∧
        (pick t o).2 = cyc (pick t o).1 (rep o) ∧
        rep o ∈ (pick t o).2) ∧
      (∀ ⦃t o t' o'⦄, (t,o) ≠ (t',o') →
        (pick t o).1 ≠ (pick t' o').1 ∨
          (pick t o).2 ≠ (pick t' o').2) := by
  classical
  have hfixed : ∀ t o,
      q ≤ ((X t).filter (fun j => good j (rep o))).card := by
    intro t o
    let G : Finset (Fin m) := (X t).filter (fun j => good j (rep o))
    let B : Finset (Fin m) := (X t).filter (fun j => ¬ good j (rep o))
    have hBsub : B ⊆ (Finset.univ.filter (fun j : Fin m => ¬ good j (rep o))) := by
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj'
    have hBlt : B.card < D :=
      (Finset.card_le_card hBsub).trans_lt (hbad o)
    have hBeq : B = X t \ G := by
      simp [B, G, Finset.filter_not]
    have hGsub : G ⊆ X t := by
      simpa [G] using (Finset.filter_subset (fun j => good j (rep o)) (X t))
    have hsum : B.card + G.card = (X t).card := by
      rw [hBeq, Finset.card_sdiff_add_card]
      have hUG : X t ∪ G = X t := by
        exact Finset.union_eq_left.mpr hGsub
      rw [hUG]
    have hqD := hcardX t
    dsimp [G] at hsum ⊢
    omega
  have hm : ∀ t : Fin (M * D), ∃ f : O → Fin m × Finset I,
      Function.Injective f ∧ ∀ o,
        (f o).1 ∈ X t ∧ good (f o).1 (rep o) ∧
          (f o).2 = cyc (f o).1 (rep o) ∧ rep o ∈ (f o).2 := by
    intro t
    let good' : Fin m → I → Prop := fun j x => j ∈ X t ∧ good j x
    have hcard' : ∀ j x, good' j x → (cyc j x).card ≤ q := by
      intro j x hx
      exact hcard j x hx.2
    have hfixed' : ∀ o, q ≤
        (Finset.univ.filter (fun j : Fin m => good' j (rep o))).card := by
      intro o
      have heq : (Finset.univ.filter (fun j : Fin m =>
          j ∈ X t ∧ good j (rep o))) =
          (X t).filter (fun j => good j (rep o)) := by
        ext j
        simp
      rw [heq]
      exact hfixed t o
    have hcycle' : ∀ j o, good' j (rep o) → rep o ∈ cyc j (rep o) := by
      intro j o hj
      exact hcycle j o hj.2
    obtain ⟨f, hf, hmem⟩ := finite_cycle_incidence_matching q
      hq rep hinjrep good' cyc hcard' hfixed' hcycle'
    refine ⟨f, hf, ?_⟩
    intro o
    have ho := hmem o
    exact ⟨ho.1.1, ho.1.2, ho.2.1, ho.2.2⟩
  choose pick hpick using hm
  refine ⟨pick, ?_, ?_, ?_⟩
  · intro t
    exact (hpick t).1
  · intro t o
    exact (hpick t).2 o
  · intro t o t' o' hne
    by_cases htt : t = t'
    · subst t'
      by_cases hj : (pick t o).1 ≠ (pick t o').1
      · exact Or.inl hj
      · right
        intro hcyc
        have hoo : o ≠ o' := by
          intro hoo
          apply hne
          simp [hoo]
        apply hoo
        apply (hpick t).1
        apply Prod.ext
        · exact not_ne_iff.mp hj
        · exact hcyc
    · have hj : (pick t o).1 ≠ (pick t' o').1 := by
        intro heq
        have hmemt := (hpick t).2 o |>.1
        have hmemt' := (hpick t').2 o' |>.1
        exact (Finset.disjoint_left.mp (hdisjoint htt)) hmemt (heq ▸ hmemt')
      exact Or.inl hj

theorem lemma10_3_interval_selection
    {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    {m q D M : ℕ} (hq : 0 < q) (X : Fin (M * D) → Finset (Fin m))
    (hinterval : ∀ t, ConsecutiveInterval (X t))
    (hdisjoint : ∀ ⦃t t' : Fin (M * D)⦄, t ≠ t' → Disjoint (X t) (X t'))
    (hcardX : ∀ t, q + D ≤ (X t).card)
    (rep : O → I) (hinjrep : Function.Injective rep)
    (good : Fin m → I → Prop)
    (cyc : Fin m → I → Finset I)
    [∀ j, DecidablePred (good j)]
    (hcard : ∀ j x, good j x → (cyc j x).card ≤ q)
    (hbad : ∀ o,
      (Finset.univ.filter (fun j : Fin m => ¬ good j (rep o))).card < D)
    (hcycle : ∀ j o, good j (rep o) → rep o ∈ cyc j (rep o))
    (fixed : O → Finset (Fin m)) (cover : O → Fin D → Finset (Fin m))
    (hgood_fixed : ∀ j o, good j (rep o) → rep o ∈ cyc j (rep o) → j ∈ fixed o)
    (hcover : ∀ o, fixed o ⊆
      (Finset.univ : Finset (Fin D)).biUnion (cover o))
    (hcover_interval : ∀ o d, ConsecutiveInterval (cover o d))
    (hcover_sub : ∀ o d, cover o d ⊆ fixed o)
    (hD : 0 < D) (hM : 0 < M) :
    ∃ J : O → Fin D, ∃ Iset : O → Finset (Fin m),
      (∀ o, Iset o ⊆ cover o (J o) ∧ (Iset o).card = M) ∧
      (∀ o j, j ∈ Iset o → j ∈ fixed o) ∧
      (∀ o, ConsecutiveInterval (cover o (J o))) ∧
      (∀ ⦃o j o' j'⦄, (o,j) ≠ (o',j') →
        j ∈ Iset o → j' ∈ Iset o' →
        j ≠ j' ∨ cyc j (rep o) ≠ cyc j' (rep o')) := by
  classical
  obtain ⟨pick, hpick_inj, hpick_mem, hpick_ind⟩ :=
    lemma10_3_repeated_matching hq X hinterval hdisjoint hcardX rep hinjrep good cyc
      hcard hbad hcycle
  let selected : O → Finset (Fin m) := fun o =>
    Finset.image (fun t => (pick t o).1) Finset.univ
  have hselected_card : ∀ o, (selected o).card = M * D := by
    intro o
    have hinj : Set.InjOn (fun t => (pick t o).1) (↑(Finset.univ : Finset (Fin (M * D))) : Set _) := by
      intro t ht t' ht' heq
      change (pick t o).1 = (pick t' o).1 at heq
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisjoint hne))
        (hpick_mem t o |>.1) (heq ▸ hpick_mem t' o |>.1)
    have hc := Finset.card_image_of_injOn hinj
    simpa [selected] using hc
  have hselected_sub : ∀ o, selected o ⊆ fixed o := by
    intro o j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    have hmem : rep o ∈ cyc (pick t o).1 (rep o) := by
      rw [← (hpick_mem t o).2.2.1]
      exact (hpick_mem t o).2.2.2
    exact hgood_fixed _ _ (hpick_mem t o |>.2.1) hmem
  have hselected_cover : ∀ o, selected o ⊆
      (Finset.univ : Finset (Fin D)).biUnion (cover o) := by
    intro o
    exact (hselected_sub o).trans (hcover o)
  have hchoice : ∀ o, ∃ d : Fin D, M ≤ (selected o ∩ cover o d).card := by
    intro o
    apply finite_cover_pigeonhole hD hM
    · exact hselected_cover o
    · simpa [hselected_card o]
  choose J hJ using hchoice
  have hsubset : ∀ o, ∃ T : Finset (Fin m),
      And (∀ j, j ∈ T → j ∈ selected o)
        (And (∀ j, j ∈ T → j ∈ cover o (J o)) (T.card = M)) := by
    intro o
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (hJ o)
    have hsel : ∀ j, j ∈ T → j ∈ selected o := by
      intro j hj
      have hji : j ∈ selected o ∩ cover o (J o) := hT hj
      exact (Finset.mem_inter.mp hji).1
    have hcov : ∀ j, j ∈ T → j ∈ cover o (J o) := by
      intro j hj
      have hji : j ∈ selected o ∩ cover o (J o) := hT hj
      exact (Finset.mem_inter.mp hji).2
    exact ⟨T, And.intro hsel (And.intro hcov hTc)⟩
  let Iset : O → Finset (Fin m) := fun o => Classical.choose (hsubset o)
  have hI_sel : ∀ o, ∀ j, j ∈ Iset o → j ∈ selected o := by
    intro o j hj
    exact (Classical.choose_spec (hsubset o)).1 j hj
  have hI_cov : ∀ o, ∀ j, j ∈ Iset o → j ∈ cover o (J o) := by
    intro o j hj
    exact (Classical.choose_spec (hsubset o)).2.1 j hj
  have hI_card : ∀ o, (Iset o).card = M := by
    intro o
    exact (Classical.choose_spec (hsubset o)).2.2
  refine ⟨J, Iset, ?_, ?_, ?_, ?_⟩
  · intro o
    exact ⟨fun j hj => hI_cov o j hj, hI_card o⟩
  · intro o j hj
    exact hcover_sub o (J o) (hI_cov o j hj)
  · intro o
    exact hcover_interval o (J o)
  · intro o j o' j' hpair hjo hj'o'
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp (hI_sel o j hjo)
    obtain ⟨t', ht', heq'⟩ := Finset.mem_image.mp (hI_sel o' j' hj'o')
    have heqj : (pick t o).1 = j := heq
    have heqj' : (pick t' o').1 = j' := heq'
    have hind := hpick_ind (t := t) (o := o) (t' := t') (o' := o') (by
      intro h
      apply hpair
      have ht_eq : t = t' := congrArg Prod.fst h
      have ho_eq : o = o' := congrArg Prod.snd h
      subst t'
      subst o'
      apply Prod.ext
      · rfl
      · change j = j'
        exact heqj.symm.trans heqj')
    rcases hind with hind | hind
    · exact Or.inl (by simpa [heqj, heqj'] using hind)
    · exact Or.inr (by
        intro htarget
        have hx0 := (hpick_mem t o).2.2.1
        have hx'0 := (hpick_mem t' o').2.2.1
        apply hind
        calc
          (pick t o).2 = cyc (pick t o).1 (rep o) := hx0
          _ = cyc j (rep o) := by rw [heqj]
          _ = cyc j' (rep o') := htarget
          _ = cyc (pick t' o').1 (rep o') := by rw [heqj']
          _ = (pick t' o').2 := hx'0.symm)

theorem lemma10_3_interval_selection_from_bound
    {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    {m q D M : ℕ} (hq : 0 < q) (hD : 0 < D) (hM : 0 < M)
    (hm : M * D * (q + D) ≤ m)
    (rep : O → I) (hinjrep : Function.Injective rep)
    (good : Fin m → I → Prop) (cyc : Fin m → I → Finset I)
    [∀ j, DecidablePred (good j)]
    (hcard : ∀ j x, good j x → (cyc j x).card ≤ q)
    (hbad : ∀ o,
      (Finset.univ.filter (fun j : Fin m => ¬ good j (rep o))).card < D)
    (hcycle : ∀ j o, good j (rep o) → rep o ∈ cyc j (rep o)) :
    ∃ J : O → Fin D, ∃ Iset : O → Finset (Fin m),
      (∀ o, Iset o ⊆ prefixPiece (D := D) good rep o (J o) ∧ (Iset o).card = M) ∧
      (∀ o j, j ∈ Iset o → j ∈ fixedChoice good rep o) ∧
      (∀ o, ConsecutiveInterval (prefixPiece (D := D) good rep o (J o))) ∧
      (∀ ⦃o j o' j'⦄, (o,j) ≠ (o',j') →
        j ∈ Iset o → j' ∈ Iset o' →
        j ≠ j' ∨ cyc j (rep o) ≠ cyc j' (rep o')) := by
  have hbad' : ∀ o, (badChoice good rep o).card < D := by
    intro o
    simpa [badChoice] using hbad o
  obtain ⟨X, hinterval, hdisjoint, hcardX⟩ :=
    consecutive_block_family hq hD hM hm
  have hcardX' : ∀ t, q + D ≤ (X t).card := by
    intro t
    rw [hcardX t]
  have hcover : ∀ o, fixedChoice good rep o ⊆
      (Finset.univ : Finset (Fin D)).biUnion (prefixPiece (D := D) good rep o) := by
    exact fixed_choice_prefix_cover (D := D) good rep hbad' hD
  have hcover_interval : ∀ o d, ConsecutiveInterval (prefixPiece (D := D) good rep o d) := by
    exact fixed_choice_prefix_interval (D := D) good rep
  have hcover_sub : ∀ o d, prefixPiece (D := D) good rep o d ⊆ fixedChoice good rep o := by
    intro o d j hj
    exact (Finset.mem_filter.mp hj).1
  have hgood_fixed : ∀ j o, good j (rep o) →
      rep o ∈ cyc j (rep o) → j ∈ fixedChoice good rep o := by
    intro j o hj hjo
    simp [fixedChoice, hj]
  obtain ⟨J, Iset, hI, hfixed, hintervalI, hind⟩ :=
    lemma10_3_interval_selection hq X hinterval hdisjoint hcardX'
      rep hinjrep good cyc hcard hbad hcycle
      (fixedChoice good rep) (prefixPiece (D := D) good rep) hgood_fixed
      hcover hcover_interval hcover_sub hD hM
  exact ⟨J, Iset, hI, hfixed, hintervalI, hind⟩

theorem lemma10_3_interval_selection_actual
    {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I]
    {m q D M : ℕ} (hq : 0 < q) (hD : 0 < D) (hM : 0 < M)
    (hm : M * D * (q + D) ≤ m)
    (rep : O → I) (hinjrep : Function.Injective rep)
    (good : Fin m → I → Prop) (σ : Fin m → Equiv.Perm I)
    [∀ j, DecidablePred (good j)]
    (hperiod : ∀ j x, good j x → Function.IsPeriodicPt (σ j) q x)
    (hbad : ∀ o,
      (Finset.univ.filter (fun j : Fin m => ¬ good j (rep o))).card < D) :
    ∃ J : O → Fin D, ∃ Iset : O → Finset (Fin m),
      (∀ o, Iset o ⊆ prefixPiece good rep o (J o) ∧ (Iset o).card = M) ∧
      (∀ o j, j ∈ Iset o → j ∈ fixedChoice good rep o) ∧
      (∀ o, ConsecutiveInterval (prefixPiece good rep o (J o))) ∧
      (∀ ⦃o j o' j'⦄, (o,j) ≠ (o',j') →
        j ∈ Iset o → j' ∈ Iset o' →
        j ≠ j' ∨
          (Function.periodicOrbit (σ j) (rep o)).toFinset ≠
            (Function.periodicOrbit (σ j') (rep o')).toFinset) := by
  let cyc : Fin m → I → Finset I := fun j x =>
    (Function.periodicOrbit (σ j) x).toFinset
  have hcard : ∀ j x, good j x → (cyc j x).card ≤ q := by
    intro j x hx
    have hp := hperiod j x hx
    have hdvd := hp.minimalPeriod_dvd
    rw [show (cyc j x).card = Function.minimalPeriod (σ j) x by
      exact periodicOrbit_toFinset_card (σ j) x]
    exact Nat.le_of_dvd hq hdvd
  have hcycle : ∀ j o, good j (rep o) → rep o ∈ cyc j (rep o) := by
    intro j o ho
    exact periodicOrbit_mem_toFinset (σ j) (rep o)
      (Function.mk_mem_periodicPts hq (hperiod j (rep o) ho))
  obtain ⟨J, Iset, hI, hfixed, hinterval, hind⟩ :=
    lemma10_3_interval_selection_from_bound hq hD hM hm rep hinjrep good cyc
      hcard hbad hcycle
  refine ⟨J, Iset, hI, hfixed, hinterval, ?_⟩
  intro o j o' j' hpair hjo hj'o'
  exact hind hpair hjo hj'o'

end NikolovSegal
