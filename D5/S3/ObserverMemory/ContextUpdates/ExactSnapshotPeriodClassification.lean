/- GID: D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotPeriodClassification
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/ExactSnapshotPeriodClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact snapshots have common binary sender periods and even global switches. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

namespace D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification

open scoped BigOperators

variable {G I C : Type*} [AddCommGroup G] [Fintype I]
    {M : I → Type*}

/-- The receiver is separated from the finite family of senders. -/
abbrev Source (χ : G →+ ZMod 2) := (G × (I → G)) × χ.ker

/-- A deterministic query and one reply function for each sender. -/
structure Protocol (G I C : Type*) (M : I → Type*) where
  query : G → G → C
  reply : (i : I) → G → G → C → M i

/-- The value to be decoded. -/
def target {χ : G →+ ZMod 2} (s : Source (I := I) χ) : G :=
  s.1.1 + ∑ i, s.1.2 i

/-- The observed clock includes precisely the kernel-valued offset. -/
def clock {χ : G →+ ZMod 2} (s : Source (I := I) χ) : G :=
  target s + s.2

/-- The complete received snapshot, with its original reply labels. -/
def observe (P : Protocol G I C M) {χ : G →+ ZMod 2}
    (s : Source (I := I) χ) : G × G × ((i : I) → M i) :=
  (s.1.1, clock s, fun i => P.reply i (s.1.2 i) (clock s) (P.query s.1.1 (clock s)))

/-- A branch is used only when one actual source produces it. -/
def Reachable (P : Protocol G I C M) (χ : G →+ ZMod 2) (a t : G) (c : C) : Prop :=
  ∃ s : Source (I := I) χ, s.1.1 = a ∧ clock s = t ∧ P.query a t = c

/-- Every local input occurs on each reachable branch: a second sender absorbs
exactly the amount needed to keep the clock fixed, with zero kernel offset. -/
theorem local_input_realizability [Nontrivial I] (P : Protocol G I C M)
    (χ : G →+ ZMod 2) (a t : G) (c : C) (hb : Reachable P χ a t c)
    (i : I) (x : G) :
    ∃ s : Source (I := I) χ,
      s.1.1 = a ∧ clock s = t ∧ P.query s.1.1 (clock s) = c ∧ s.1.2 i = x := by
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  let v : I → G := Pi.single i x + Pi.single j (t - a - x)
  have hv : ∑ k, v k = x + (t - a - x) := by
    simp [v, Finset.sum_add_distrib]
  have ht : clock (χ := χ) ((a, v), 0) = t := by
    simp only [clock, target, hv, ZeroMemClass.coe_zero, add_zero]
    abel
  refine ⟨((a, v), 0), rfl, ht, ?_, ?_⟩
  · rw [ht]
    exact hb.choose_spec.2.2
  · simp [v, Ne.symm hj]

/-- Periods must preserve every local input in every actually used branch. -/
def senderPeriods (P : Protocol G I C M) (χ : G →+ ZMod 2) (i : I) : AddSubgroup G where
  carrier := {p | ∀ a t c, Reachable P χ a t c →
    Function.Periodic (fun x => P.reply i x t c) p}
  zero_mem' := by simp [Function.Periodic]
  add_mem' hp hq := by
    intro a t c hb
    exact (hp a t c hb).add_period (hq a t c hb)
  neg_mem' hp := by
    intro a t c hb
    exact (hp a t c hb).neg

/-- Periods of the whole snapshot under source translations. -/
def globalPeriods (P : Protocol G I C M) (χ : G →+ ZMod 2) :
    AddSubgroup (Source (I := I) χ) where
  carrier := {v | Function.Periodic (observe P) v}
  zero_mem' := by simp [Function.Periodic]
  add_mem' hp hq := hp.add_period hq
  neg_mem' hp := hp.neg

/-- The senders with a nontrivial common period. -/
noncomputable def activeSenders (P : Protocol G I C M) (χ : G →+ ZMod 2) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => senderPeriods P χ i ≠ ⊥)

/-- Binary switches whose sum is zero, equivalently an even number of switches. -/
def evenSwitches (J : Finset I) : AddSubgroup (J → ZMod 2) :=
  { carrier := {b | ∑ i, b i = 0}
    zero_mem' := by simp
    add_mem' := by
      intro a b ha hb
      change ∑ i, a i = 0 at ha
      change ∑ i, b i = 0 at hb
      change ∑ i, (a i + b i) = 0
      rw [Finset.sum_add_distrib, ha, hb, add_zero]
    neg_mem' := by intro a ha; simpa [Finset.sum_neg_distrib, ha] }

/-- Exact decoding constrains sender periods and their simultaneous source translations. -/
theorem period_classification [Nontrivial I]
    (P : Protocol G I C M) (χ : G →+ ZMod 2)
    (D : (G × G × ((i : I) → M i)) → G)
    (hD : ∀ s : Source (I := I) χ, D (observe P s) = target s) :
    (∀ a t c, Reachable P χ a t c → ∀ i x,
      ∃ s : Source (I := I) χ,
        s.1.1 = a ∧ clock s = t ∧
        P.query s.1.1 (clock s) = c ∧ s.1.2 i = x) ∧
    (∀ i, senderPeriods P χ i = ⊥ ∨ ∃ τ : G,
      τ ≠ 0 ∧ χ τ = 1 ∧ τ + τ = 0 ∧
      ∀ p, p ∈ senderPeriods P χ i ↔ p = 0 ∨ p = τ) ∧
    (∀ i j p q, p ∈ senderPeriods P χ i → q ∈ senderPeriods P χ j →
      p ≠ 0 → q ≠ 0 → p = q) ∧
    (∀ v : Source (I := I) χ, v ∈ globalPeriods P χ ↔
      v.1.1 = 0 ∧ v.2 = 0 ∧ (∀ i, v.1.2 i ∈ senderPeriods P χ i) ∧
        ∑ i, v.1.2 i = 0) ∧
    ( (activeSenders P χ).card ≤ 1 → globalPeriods P χ = ⊥) ∧
    ( (activeSenders P χ).Nonempty →
      Nonempty (globalPeriods P χ ≃+ evenSwitches (activeSenders P χ)) ∧
      Nat.card (globalPeriods P χ) = 2 ^ ((activeSenders P χ).card - 1)) := by
  refine ⟨local_input_realizability P χ, ?_⟩
  classical
  have hb : Reachable P χ 0 0 (P.query 0 0) := by
    exact ⟨0, rfl, by simp [clock, target], rfl⟩
  have rigid (u : I → G) (hu : ∀ i, u i ∈ senderPeriods P χ i)
      (hc : χ (∑ i, u i) = 0) : ∑ i, u i = 0 := by
    let s : Source (I := I) χ := ((0, u), ⟨-(∑ i, u i), by simp [hc]⟩)
    have hs : clock s = 0 := by simp [s, clock, target]
    have ho : observe P s = observe P (0 : Source (I := I) χ) := by
      apply Prod.ext (by rfl)
      apply Prod.ext
      · simp [observe, s, clock, target]
      · funext i
        simpa [observe, s, clock, target] using hu i 0 0 (P.query 0 0) hb 0
    have hd := (hD s).symm.trans ((congrArg D ho).trans (hD 0))
    simpa [s, target] using hd
  have ker_zero (i : I) (p : G) (hp : p ∈ senderPeriods P χ i)
      (hc : χ p = 0) : p = 0 := by
    have hz := rigid (Pi.single i p) (by
      intro j
      by_cases hji : j = i
      · subst j; simpa using hp
      · simp [Pi.single_eq_of_ne hji]) (by simpa using hc)
    simpa using hz
  have odd (i : I) (p : G) (hp : p ∈ senderPeriods P χ i) (hne : p ≠ 0) : χ p = 1 := by
    have hn : χ p ≠ 0 := fun h => hne (ker_zero i p hp h)
    generalize χ p = z at hn ⊢
    fin_cases z
    · exact (hn rfl).elim
    · rfl
  have two_zero (i : I) (p : G) (hp : p ∈ senderPeriods P χ i) : p + p = 0 := by
    apply ker_zero i (p + p) ((senderPeriods P χ i).add_mem hp hp)
    rw [map_add]
    generalize χ p = z
    fin_cases z <;> decide
  have unique (i j : I) (p q : G) (hp : p ∈ senderPeriods P χ i)
      (hq : q ∈ senderPeriods P χ j) (hp0 : p ≠ 0) (hq0 : q ≠ 0) : p = q := by
    have hc : χ (p - q) = 0 := by rw [map_sub, odd i p hp hp0, odd j q hq hq0, sub_self]
    by_cases hij : i = j
    · subst j
      exact sub_eq_zero.mp (ker_zero i _ ((senderPeriods P χ i).sub_mem hp hq) hc)
    · have hz := rigid (Pi.single i p - Pi.single j q) (by
        intro k
        apply (senderPeriods P χ k).sub_mem
        · by_cases h : k = i
          · subst k; simpa using hp
          · simp [Pi.single_eq_of_ne h]
        · by_cases h : k = j
          · subst k; simpa using hq
          · simp [Pi.single_eq_of_ne h]) (by simpa [Finset.sum_sub_distrib] using hc)
      exact sub_eq_zero.mp (by simpa [Finset.sum_sub_distrib] using hz)
  have generators : ∀ i, senderPeriods P χ i = ⊥ ∨ ∃ τ : G,
      τ ≠ 0 ∧ χ τ = 1 ∧ τ + τ = 0 ∧
      ∀ p, p ∈ senderPeriods P χ i ↔ p = 0 ∨ p = τ := by
    intro i
    by_cases hi : senderPeriods P χ i = ⊥
    · exact Or.inl hi
    · right
      have hex : ∃ τ ∈ senderPeriods P χ i, τ ≠ 0 := by
        simpa only [AddSubgroup.eq_bot_iff_forall, not_forall, exists_prop] using hi
      obtain ⟨τ, hτ, hτ0⟩ := hex
      refine ⟨τ, hτ0, odd i τ hτ hτ0, two_zero i τ hτ, ?_⟩
      intro p
      constructor
      · intro hp
        by_cases hp0 : p = 0
        · exact Or.inl hp0
        · exact Or.inr (unique i i p τ hp hτ hp0 hτ0)
      · rintro (rfl | rfl)
        · exact (senderPeriods P χ i).zero_mem
        · exact hτ
  have global : ∀ v : Source (I := I) χ, v ∈ globalPeriods P χ ↔
      v.1.1 = 0 ∧ v.2 = 0 ∧ (∀ i, v.1.2 i ∈ senderPeriods P χ i) ∧
        ∑ i, v.1.2 i = 0 := by
    intro v
    constructor
    · intro hv
      have ho := hv (0 : Source (I := I) χ)
      simp only [zero_add] at ho
      have ha : v.1.1 = 0 := congrArg Prod.fst ho
      have ht : clock v = 0 := by simpa [observe, clock, target] using congrArg (fun z => z.2.1) ho
      have hy : target v = 0 := by
        simpa [target] using (hD v).symm.trans ((congrArg D ho).trans (hD 0))
      have hk : v.2 = 0 := Subtype.ext (by simpa [clock, hy] using ht)
      refine ⟨ha, hk, ?_, by simpa [target, ha] using hy⟩
      intro i a t c hb' x
      obtain ⟨s, hsa, hst, hsq, hsx⟩ := local_input_realizability P χ a t c hb' i x
      have hadd : clock (s + v) = clock s := by
        simp only [clock, target, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Finset.sum_add_distrib, AddSubgroup.coe_add, ha, hk, ZeroMemClass.coe_zero]
        have hz : ∑ k, v.1.2 k = 0 := by simpa [target, ha] using hy
        rw [hz]
        abel
      have he := congrArg (fun z => z.2.2 i) (hv s)
      simpa [observe, hadd, ha, hst, hsa, hsx, hb'.choose_spec.2.2] using he
    · rintro ⟨ha, hk, hu, hz⟩ s
      have hadd : clock (s + v) = clock s := by
        simp only [clock, target, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Finset.sum_add_distrib, AddSubgroup.coe_add, ha, hk, ZeroMemClass.coe_zero, hz]
        abel
      apply Prod.ext (by simp [observe, ha])
      apply Prod.ext hadd
      funext i
      simpa [observe, hadd, ha] using
        hu i s.1.1 (clock s) (P.query s.1.1 (clock s)) ⟨s, rfl, rfl, rfl⟩ (s.1.2 i)
  let J := activeSenders P χ
  have memJ (i : I) : i ∈ J ↔ senderPeriods P χ i ≠ ⊥ := by
    simp [J, activeSenders]
  have off (u : I → G) (hu : ∀ i, u i ∈ senderPeriods P χ i)
      (i : I) (hi : i ∉ J) : u i = 0 := by
    have hbot : senderPeriods P χ i = ⊥ := not_not.mp (hi ∘ (memJ i).mpr)
    simpa [hbot] using hu i
  have sumJ (u : I → G) (hu : ∀ i, u i ∈ senderPeriods P χ i) :
      ∑ i : J, u i = ∑ i, u i := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => off u hu i hi)
  refine ⟨generators, unique, global, ?_, ?_⟩
  · intro hcard
    apply (AddSubgroup.eq_bot_iff_forall _).mpr
    intro v hv
    obtain ⟨ha, hk, hu, hz⟩ := (global v).mp hv
    have huv : v.1.2 = 0 := by
      funext i
      by_contra hi
      have hiJ : i ∈ J := by by_contra h; exact hi (off _ hu i h)
      have heq : (∑ k, v.1.2 k) = v.1.2 i := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          by_contra hk0
          have hkJ : k ∈ J := by by_contra h; exact hk0 (off _ hu k h)
          exact hki (Finset.card_le_one.mp hcard k hkJ i hiJ)
        · simp
      exact hi (heq.symm.trans hz)
    exact Prod.ext (Prod.ext ha huv) hk
  · intro hJ
    have char_inj (i : I) : Function.Injective
        (fun p : senderPeriods P χ i => χ (p : G)) := by
      intro p q hpq
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply ker_zero i _ ((senderPeriods P χ i).sub_mem p.property q.property)
      simp [map_sub, hpq]
    have char_surj (i : J) : Function.Surjective
        (fun p : senderPeriods P χ i => χ (p : G)) := by
      obtain hbot | ⟨τ, hτ0, hχ, htwo, hτ⟩ := generators i
      · exact False.elim ((memJ i).mp i.property hbot)
      · intro z
        fin_cases z
        · exact ⟨0, map_zero χ⟩
        · exact ⟨⟨τ, (hτ τ).mpr (Or.inr rfl)⟩, hχ⟩
    let encode : globalPeriods P χ →+ evenSwitches J :=
      { toFun := fun v => ⟨fun i => χ (v.val.1.2 i), by
          have hv := (global v).mp v.property
          change ∑ i : J, χ (v.val.1.2 i) = 0
          rw [← map_sum, sumJ _ hv.2.2.1, hv.2.2.2, map_zero]⟩
        map_zero' := by ext i; exact map_zero χ
        map_add' := by intro v w; ext i; exact map_add χ _ _ }
    have enc_inj : Function.Injective encode := by
      intro v w he
      obtain ⟨hva, hvk, hvu, hvz⟩ := (global v).mp v.property
      obtain ⟨hwa, hwk, hwu, hwz⟩ := (global w).mp w.property
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext (hva.trans hwa.symm)
        funext i
        by_cases hi : i ∈ J
        · exact congrArg Subtype.val (char_inj i (a₁ := ⟨_, hvu i⟩) (a₂ := ⟨_, hwu i⟩)
            (congrArg (fun b : evenSwitches J => b.val ⟨i, hi⟩) he))
        · exact (off _ hvu i hi).trans (off _ hwu i hi).symm
      · exact hvk.trans hwk.symm
    have enc_surj : Function.Surjective encode := by
      intro b
      choose lift hlift using fun i : J => char_surj i (b.val i)
      let u : I → G := fun i => if hi : i ∈ J then (lift ⟨i, hi⟩).val else 0
      have hu (i : I) : u i ∈ senderPeriods P χ i := by
        dsimp [u]
        split
        · rename_i hi
          exact (lift ⟨i, hi⟩).property
        · exact (senderPeriods P χ i).zero_mem
      have hc : χ (∑ i, u i) = 0 := by
        rw [← sumJ _ hu, map_sum]
        have hb' : ∑ i : J, b.val i = 0 := b.property
        convert hb' using 1
        apply Finset.sum_congr rfl
        intro i _
        simpa [u, i.property] using hlift i
      have hz := rigid u hu hc
      refine ⟨⟨((0, u), 0), (global _).mpr ⟨rfl, rfl, hu, hz⟩⟩, ?_⟩
      apply Subtype.ext
      funext i
      simpa [encode, u, i.property] using hlift i
    let e := AddEquiv.ofBijective encode ⟨enc_inj, enc_surj⟩
    refine ⟨⟨e⟩, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    let σ : (J → ZMod 2) →+ ZMod 2 :=
      { toFun := fun b => ∑ i, b i
        map_zero' := by simp
        map_add' := by intros; simp [Finset.sum_add_distrib] }
    obtain ⟨j, hj⟩ := hJ
    have hσ : Function.Surjective σ := by
      intro z
      exact ⟨Pi.single ⟨j, hj⟩ z, by simp [σ]⟩
    have hcard := σ.ker.card_mul_index
    rw [AddSubgroup.index_ker, σ.range_eq_top.mpr hσ] at hcard
    have hker : σ.ker = evenSwitches J := rfl
    rw [hker] at hcard
    have hcard' : Nat.card (evenSwitches J) * 2 = 2 ^ J.card := by
      simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using hcard
    have hn : 1 ≤ J.card := Finset.card_pos.mpr ⟨j, hj⟩
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
    rw [hcard', ← pow_succ, Nat.sub_add_cancel hn]


#print axioms local_input_realizability
#print axioms period_classification

end D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
