/- GID: D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact decoding and source injectivity are classified by branch collisions. -/

import D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

namespace D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotCollisionClassification

open scoped BigOperators
open D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification

variable {G I : Type*} [AddCommGroup G] [Fintype I]
variable {M : I → Type*}

/-- Exactness of a fixed reachable branch, expressed on its parity fibre. -/
def BranchExact (χ : G →+ ZMod 2) (f : (i : I) → G → M i) (p : ZMod 2) : Prop :=
  ∀ x y : I → G,
    χ (∑ i, x i) = p → χ (∑ i, y i) = p →
      (∀ i, f i (x i) = f i (y i)) → ∑ i, x i = ∑ i, y i

/-- Each reply map is injective within each characteristic fibre. -/
def FiberSeparated (χ : G →+ ZMod 2) (f : (i : I) → G → M i) : Prop :=
  ∀ i x y, χ x = χ y → f i x = f i y → x = y

/-- The sender indices having at least one reply collision. -/
noncomputable def NoninjectiveSenders (f : (i : I) → G → M i) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ¬Function.Injective (f i))

/-- Every nonzero collision has one common odd involution. -/
def CommonOddCollision (χ : G →+ ZMod 2) (f : (i : I) → G → M i) : Prop :=
  ∃ τ : G, χ τ = 1 ∧ τ + τ = 0 ∧
    ∀ i x y, f i x = f i y → x ≠ y → y - x = τ

def ExactRecovery (P : Protocol G I C M) (χ : G →+ ZMod 2) : Prop :=
  ∃ D : (G × G × ((i : I) → M i)) → G,
    ∀ s : Source (I := I) χ, D (observe P s) = target s

def BranchCondition (χ : G →+ ZMod 2) (f : (i : I) → G → M i) : Prop :=
  FiberSeparated χ f ∧
    ((NoninjectiveSenders f).card ≤ 1 ∨ CommonOddCollision χ f)

def SourceInjective (P : Protocol G I C M) (χ : G →+ ZMod 2) : Prop :=
  Function.Injective (observe P (χ := χ))

def BranchSingle (P : Protocol G I C M) (χ : G →+ ZMod 2) : Prop :=
  ∀ a t c, Reachable P χ a t c →
    (NoninjectiveSenders (fun i x => P.reply i x t c)).card ≤ 1

/-- Exact recovery is classified by the collisions on each reachable branch. -/
theorem exact_recovery_iff_branch_conditions
    (P : Protocol G I C M) (χ : G →+ ZMod 2)
    (hχ : Function.Surjective χ)
    (hcardI : 3 ≤ Fintype.card I) :
    ExactRecovery P χ ↔
      ∀ a t c, Reachable P χ a t c →
        BranchCondition χ (fun i x => P.reply i x t c) := by
  classical
  have : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  constructor
  · rintro ⟨D, hD⟩ a t c hb
    let f : (i : I) → G → M i := fun i x => P.reply i x t c
    let p := χ (t - a)
    have hexact : BranchExact χ f p := by
      intro x y hx hy hreply
      let hxoff : χ (t - a - ∑ i, x i) = 0 := by
        simpa only [p, map_sub] using (sub_eq_zero.mpr hx.symm)
      let hyoff : χ (t - a - ∑ i, y i) = 0 := by
        simpa only [p, map_sub] using (sub_eq_zero.mpr hy.symm)
      let sx : Source (I := I) χ := ((a, x), ⟨t - a - ∑ i, x i, hxoff⟩)
      let sy : Source (I := I) χ := ((a, y), ⟨t - a - ∑ i, y i, hyoff⟩)
      have htx : clock sx = t := by
        simp [sx, clock, target]
      have hty : clock sy = t := by
        simp [sy, clock, target]
      have hobs : observe P sx = observe P sy := by
        apply Prod.ext (by rfl)
        apply Prod.ext
        · simp [observe, htx, hty]
        · funext i
          have hqc : P.query a t = c := by simpa using hb.choose_spec.2.2
          simpa [observe, sx, sy, htx, hty, hqc] using hreply i
      have hd := (hD sx).symm.trans ((congrArg D hobs).trans (hD sy))
      simpa [sx, sy, target] using hd
    have embed (i : I) (x : G) :
        ∃ z : I → G, χ (∑ k, z k) = p ∧ z i = x := by
      obtain ⟨j, hij⟩ := exists_ne i
      obtain ⟨k, hk⟩ := hχ (p - χ x)
      let z : I → G := Pi.single i x + Pi.single j k
      refine ⟨z, ?_, ?_⟩
      · suffices χ x + χ k = p by simpa [z, Finset.sum_add_distrib] using this
        calc
          χ x + χ k = χ x + (p - χ x) := by rw [hk]
          _ = p := by abel
      · simp [z, hij]
    have sep : FiberSeparated χ f := by
      intro i x y hxy hreply
      obtain ⟨z, hz, hzi⟩ := embed i x
      let z' : I → G := z + Pi.single i (y - x)
      have hsum : ∑ k, z' k = (∑ k, z k) + (y - x) := by
        simp [z', Finset.sum_add_distrib]
      have hpar : χ (∑ k, z' k) = p := by
        rw [hsum, map_add, map_sub, hxy, sub_self, add_zero, hz]
      have hreplies : ∀ k, f k (z k) = f k (z' k) := by
        intro k
        by_cases hki : k = i
        · subst k
          simpa [z', hzi]
        · simp [z', Pi.single_eq_of_ne hki]
      have heq := hexact z z' hz hpar hreplies
      rw [hsum] at heq
      have hd : y - x = 0 := by
        have heq' : (∑ k, z k) + 0 = (∑ k, z k) + (y - x) := by simpa using heq
        exact add_left_cancel heq'.symm
      exact (sub_eq_zero.mp hd).symm
    have oddDiff (q : I) (a b : G) (hab : f q a = f q b)
        (hne : a ≠ b) : χ (b - a) = 1 := by
      have hneq : χ a ≠ χ b := by
        intro heq
        exact hne (sep q a b heq hab)
      rw [map_sub]
      generalize χ b = b' at hneq ⊢
      generalize χ a = a' at hneq ⊢
      fin_cases a' <;> fin_cases b'
      · exact (hneq rfl).elim
      · decide
      · decide
      · exact (hneq rfl).elim
    have cancel (i j : I) (hij : i ≠ j) (x y u v : G)
        (hix : f i x = f i y) (hxy : x ≠ y)
        (hjv : f j u = f j v) (huv : u ≠ v) :
        (y - x) + (v - u) = 0 := by
      have hd : χ (y - x) = 1 := oddDiff i x y hix hxy
      have he : χ (v - u) = 1 := oddDiff j u v hjv huv
      obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({i, j} : Finset I)) (t := Finset.univ)
        (lt_of_le_of_lt Finset.card_le_two
          (by simpa only [Finset.card_univ] using (Nat.lt_of_succ_le hcardI)))
      have hki : k ≠ i := fun h => hk (by simp [h])
      have hkj : k ≠ j := fun h => hk (by simp [h])
      obtain ⟨w, hw⟩ := hχ (p - χ x - χ u)
      let base : I → G := Pi.single i x + Pi.single j u + Pi.single k w
      have hbase : χ (∑ q, base q) = p := by
        suffices χ x + χ u + χ w = p by
          simpa [base, Finset.sum_add_distrib] using this
        rw [hw]
        abel
      let both : I → G := base + Pi.single i (y - x) + Pi.single j (v - u)
      have hbothsum : ∑ q, both q = (∑ q, base q) + (y - x) + (v - u) := by
        simp [both, Finset.sum_add_distrib]
      have hboth : χ (∑ q, both q) = p := by
        rw [hbothsum]
        simp only [map_add]
        rw [hbase, hd, he]
        have hone : (1 : ZMod 2) + 1 = 0 := by decide
        calc
          p + 1 + 1 = p + (1 + 1) := by abel
          _ = p := by rw [hone, add_zero]
      have hrepboth : ∀ q, f q (base q) = f q (both q) := by
        intro q
        by_cases hqi : q = i
        · subst q
          convert hix using 1 <;>
            simp [both, base, Ne.symm hij, hki, add_comm]
        · by_cases hqj : q = j
          · subst q
            convert hjv using 1 <;>
              simp [both, base, hij, hkj, add_left_comm, add_comm]
          · simp [both, base, Pi.single_eq_of_ne hqi, Pi.single_eq_of_ne hqj]
      have hsumboth := hexact base both hbase hboth hrepboth
      rw [hbothsum] at hsumboth
      have hsumzero : (y - x) + (v - u) = 0 := by
        have h' : (∑ q, base q) + 0 = (∑ q, base q) + ((y - x) + (v - u)) := by
          simpa [add_assoc] using hsumboth
        exact add_left_cancel h'.symm
      exact hsumzero
    have hrigid (i j : I) (hij : i ≠ j) (x y u v : G)
        (hix : f i x = f i y) (hxy : x ≠ y)
        (hjv : f j u = f j v) (huv : u ≠ v) :
        (y - x) + (v - u) = 0 ∧ (y - x) - (v - u) = 0 := by
      refine ⟨cancel i j hij x y u v hix hxy hjv huv, ?_⟩
      have h := cancel i j hij x y v u hix hxy hjv.symm (Ne.symm huv)
      convert h using 1
      abel
    refine ⟨sep, ?_⟩
    by_cases hcard : (NoninjectiveSenders f).card ≤ 1
    · exact Or.inl hcard
    · right
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hcard)
      have collides (q : I) (hq : q ∈ NoninjectiveSenders f) :
          ∃ x y, f q x = f q y ∧ x ≠ y := by
        have hqN : ¬Function.Injective (f q) := by
          simpa [NoninjectiveSenders] using hq
        simpa only [Function.Injective, not_forall, exists_prop] using hqN
      obtain ⟨x, y, hix, hxy⟩ := collides i hi
      obtain ⟨u, v, hjv, huv⟩ := collides j hj
      have hrig := hrigid i j hij x y u v hix hxy hjv huv
      let τ : G := y - x
      have hτodd : χ τ = 1 := oddDiff i x y hix hxy
      have hτinvol : τ + τ = 0 := by
        have hsum : (y - x) + (y - x) = ((y - x) + (v - u)) +
            ((y - x) - (v - u)) := by abel
        rw [hrig.1, hrig.2] at hsum
        simpa [τ] using hsum
      refine ⟨τ, hτodd, hτinvol, ?_⟩
      intro q a b hab hne
      by_cases hqi : q = i
      · subst q
        have hleft := hrigid i j hij a b u v hab hne hjv huv
        have hright := hrigid i j hij x y u v hix hxy hjv huv
        have heq : b - a = y - x := by
          calc
            b - a = v - u := sub_eq_zero.mp hleft.2
            _ = y - x := (sub_eq_zero.mp hright.2).symm
        exact heq
      · have hleft := hrigid i q (Ne.symm hqi) x y a b hix hxy hab hne
        simpa [τ] using (sub_eq_zero.mp hleft.2).symm
  · intro hcond
    have branch_exact (f : (i : I) → G → M i) (p : ZMod 2)
        (hcond : BranchCondition χ f) : BranchExact χ f p := by
      intro x y hx hy hreply
      rcases hcond with ⟨hsep, hcase⟩
      by_cases hcard : (NoninjectiveSenders f).card ≤ 1
      · by_cases hne : (NoninjectiveSenders f).Nonempty
        · obtain ⟨i₀, hi₀⟩ := hne
          have hxi : ∀ i, i ≠ i₀ → x i = y i := by
            intro i hii
            have hiN : i ∉ NoninjectiveSenders f := by
              intro hiN
              exact hii (Finset.card_le_one.mp hcard i hiN i₀ hi₀)
            have hinj : Function.Injective (f i) := by
              simpa [NoninjectiveSenders] using hiN
            exact hinj (hreply i)
          have hsingle : (∑ i, (x i - y i)) = x i₀ - y i₀ := by
            apply Finset.sum_eq_single i₀
            · intro i _ hi
              simp [hxi i hi]
            · simp
          have hpar : χ (x i₀) = χ (y i₀) := by
            apply sub_eq_zero.mp
            rw [← map_sub, ← hsingle, Finset.sum_sub_distrib, map_sub, hx, hy, sub_self]
          have hi₀eq := hsep i₀ _ _ hpar (hreply i₀)
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i = i₀
          · simpa [hi] using hi₀eq
          · exact hxi i hi
        · have hxi : ∀ i, x i = y i := by
            intro i
            have hiN : i ∉ NoninjectiveSenders f := by
              intro hiN
              exact hne ⟨i, hiN⟩
            have hinj : Function.Injective (f i) := by
              simpa [NoninjectiveSenders] using hiN
            exact hinj (hreply i)
          have : x = y := by funext i; exact hxi i
          simp [this]
      · have hcommon : CommonOddCollision χ f := hcase.resolve_left hcard
        rcases hcommon with ⟨τ, hτχ, hτ2, hcollision⟩
        let δ : I → G := fun i => y i - x i
        have hδ : ∀ i, δ i = 0 ∨ δ i = τ := by
          intro i
          by_cases hi : x i = y i
          · exact Or.inl (by simp [δ, hi])
          · exact Or.inr (by
              exact hcollision i (x i) (y i) (hreply i) hi)
        have hcases : ∀ s : Finset I, (∀ i ∈ s, δ i = 0 ∨ δ i = τ) →
            ((∑ i ∈ s, δ i) = 0 ∨ (∑ i ∈ s, δ i) = τ) := by
          intro s hs
          induction s using Finset.induction_on with
          | empty => simp
          | @insert a s ha ih =>
              have ha' := hs a (by simp)
              have hs' : ∀ i ∈ s, δ i = 0 ∨ δ i = τ := by
                intro i hi
                exact hs i (by simp [hi])
              rcases ih hs' with h0 | ht
              · rcases ha' with ha0 | hat
                · left; simp [Finset.sum_insert, ha, h0, ha0]
                · right; simp [Finset.sum_insert, ha, h0, hat]
              · rcases ha' with ha0 | hat
                · right; simp [Finset.sum_insert, ha, ht, ha0]
                · left; simp [Finset.sum_insert, ha, ht, hat, hτ2]
        have hsum_cases := hcases Finset.univ (fun i _ => hδ i)
        have hsumzero : ∑ i, δ i = 0 := by
          rcases hsum_cases with hzero | ht
          · exact hzero
          · exfalso
            have hpar : χ (∑ i, δ i) = 0 := by
              rw [show (∑ i, δ i) = (∑ i, y i) - ∑ i, x i by
                simp [δ, Finset.sum_sub_distrib], map_sub, hx, hy, sub_self]
            rw [ht, hτχ] at hpar
            exact one_ne_zero hpar
        have hsum : (∑ i, y i) - ∑ i, x i = 0 := by
          simpa [δ, Finset.sum_sub_distrib] using hsumzero
        exact (sub_eq_zero.mp hsum).symm
    have hconst : ∀ (s s' : Source (I := I) χ),
        observe P s = observe P s' → target s = target s' := by
      intro s s' hobs
      have ha : s.1.1 = s'.1.1 := congrArg (fun o : G × G × ((i : I) → M i) => o.1) hobs
      have ht : clock s = clock s' := congrArg (fun o => o.2.1) hobs
      let a := s.1.1
      let t := clock s
      let c := P.query a t
      have hb : Reachable P χ a t c := by
        exact ⟨s, by simp [a], rfl, rfl⟩
      have hc : P.query s'.1.1 (clock s') = c := by simp [a, t, c, ha, ht]
      let f : (i : I) → G → M i := fun i x => P.reply i x t c
      have hbranch : BranchCondition χ f := by
        simpa [f, a, t, c] using hcond a t c hb
      have par (u : Source (I := I) χ) :
          χ (∑ i, u.1.2 i) = χ (clock u - u.1.1) := by
        have hu : χ (u.2 : G) = 0 := u.2.property
        simp [clock, target, map_sub, map_add, hu]
      have hxpar : χ (∑ i, s.1.2 i) = χ (t - a) := par s
      have hypar : χ (∑ i, s'.1.2 i) = χ (t - a) := by
        simpa only [t, a, ha, ht] using par s'
      have hreply : ∀ i, f i (s.1.2 i) = f i (s'.1.2 i) := by
        intro i
        have hi := congrArg (fun o => o.2.2 i) hobs
        change P.reply i _ (clock s) (P.query s.1.1 (clock s)) =
          P.reply i _ (clock s') (P.query s'.1.1 (clock s')) at hi
        simpa only [f, c, a, t, ha, ht] using hi
      have hsum := branch_exact f (χ (t - a)) hbranch
        s.1.2 s'.1.2 hxpar hypar hreply
      simp only [target, ha, hsum]
    have hf : Function.FactorsThrough (target (χ := χ) (I := I)) (observe P) :=
      fun {_ _} h => hconst _ _ h
    exact ⟨Function.extend (observe P) target (fun _ => 0),
      fun s => hf.extend_apply (fun _ => 0) s⟩

/-- Two colliding senders give distinct sources with one observation;
one exception is recoverable. -/
theorem source_injective_iff_branch_single
    (P : Protocol G I C M) (χ : G →+ ZMod 2)
    (hχ : Function.Surjective χ)
    (hcardI : 3 ≤ Fintype.card I)
    (hexact : ExactRecovery P χ) :
    SourceInjective P χ ↔ BranchSingle P χ := by
  classical
  have hcond : ∀ a t c, Reachable P χ a t c →
      BranchCondition χ (fun i x => P.reply i x t c) :=
    (exact_recovery_iff_branch_conditions P χ hχ hcardI).mp hexact
  constructor
  · intro hinj a t c hb
    by_contra hcard
    have htwo : 1 < (NoninjectiveSenders (fun i x => P.reply i x t c)).card :=
      Nat.lt_of_not_ge hcard
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
    obtain ⟨hsep, hcase⟩ := hcond a t c hb
    have hcommon : CommonOddCollision χ (fun i x => P.reply i x t c) :=
      hcase.resolve_left hcard
    rcases hcommon with ⟨τ, hτχ, hτ2, hcollision⟩
    have hiN : ¬ Function.Injective (fun x => P.reply i x t c) := by
      simpa [NoninjectiveSenders] using hi
    have hjN : ¬ Function.Injective (fun x => P.reply j x t c) := by
      simpa [NoninjectiveSenders] using hj
    obtain ⟨x, y, hix, hxy⟩ := by
      simpa only [Function.Injective, not_forall, exists_prop] using hiN
    obtain ⟨u, v, hjv, huv⟩ := by
      simpa only [Function.Injective, not_forall, exists_prop] using hjN
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i, j} : Finset I)) (t := Finset.univ)
      (lt_of_le_of_lt Finset.card_le_two
        (by simpa only [Finset.card_univ] using (Nat.lt_of_succ_le hcardI)))
    have hki : k ≠ i := fun h => hk (by simp [h])
    have hkj : k ≠ j := fun h => hk (by simp [h])
    obtain ⟨w, hw⟩ := hχ (χ (t - a) - χ x - χ u)
    let base : I → G := Pi.single i x + Pi.single j u + Pi.single k w
    let both : I → G := base + Pi.single i (y - x) + Pi.single j (v - u)
    have hbase : χ (t - a - ∑ q, base q) = 0 := by
      suffices χ (t - a) - (χ x + χ u + χ w) = 0 by
        simpa [base, Finset.sum_add_distrib] using this
      rw [hw]
      abel
    have hd : y - x = τ := hcollision i x y hix hxy
    have he : v - u = τ := hcollision j u v hjv huv
    have hbothsum : ∑ q, both q = (∑ q, base q) + (y - x) + (v - u) := by
      simp [both, Finset.sum_add_distrib]
    have hbothzero : χ (t - a - ∑ q, both q) = 0 := by
      have hsum_eq : ∑ q, both q = ∑ q, base q := by
        calc
          ∑ q, both q = (∑ q, base q) + (y - x) + (v - u) := hbothsum
          _ = (∑ q, base q) + τ + τ := by rw [hd, he]
          _ = ∑ q, base q := by rw [add_assoc, hτ2, add_zero]
      rw [hsum_eq]
      exact hbase
    let s₁ : Source (I := I) χ := ((a, base), ⟨t - a - ∑ q, base q, hbase⟩)
    let s₂ : Source (I := I) χ := ((a, both), ⟨t - a - ∑ q, both q, hbothzero⟩)
    have hclock₁ : clock s₁ = t := by
      simp [s₁, clock, target, sub_eq_add_neg]
      abel
    have hclock₂ : clock s₂ = t := by
      simp [s₂, clock, target, sub_eq_add_neg]
      abel
    have hquery : P.query a t = c := by simpa using hb.choose_spec.2.2
    have hobs : observe P s₁ = observe P s₂ := by
      apply Prod.ext (by rfl)
      apply Prod.ext
      · simp [observe, hclock₁, hclock₂]
      · funext q
        change P.reply q (s₁.1.2 q) (clock s₁) (P.query s₁.1.1 (clock s₁)) =
          P.reply q (s₂.1.2 q) (clock s₂) (P.query s₂.1.1 (clock s₂))
        by_cases hqi : q = i
        · subst q
          rw [hclock₁, hclock₂, hquery]
          simpa [s₁, s₂, base, both, hij, hki, hkj,
            add_assoc, add_left_comm, add_comm] using hix
        · by_cases hqj : q = j
          · subst q
            rw [hclock₁, hclock₂, hquery]
            simpa [s₁, s₂, base, both, hij, hki, hkj,
              add_assoc, add_left_comm, add_comm] using hjv
          · rw [hclock₁, hclock₂, hquery]
            simp [s₁, s₂, base, both, hqi, hqj]
    have hne : s₁ ≠ s₂ := by
      intro heq
      have hcoord := congrArg (fun s : Source (I := I) χ => s.1.2 i) heq
      apply hxy
      simpa [s₁, s₂, base, both, hki, hkj, hij, add_assoc, add_left_comm, add_comm] using hcoord
    exact hne (hinj hobs)
  · intro hsingle s s' hobs
    have ha : s.1.1 = s'.1.1 := congrArg (fun o : G × G × ((i : I) → M i) => o.1) hobs
    have ht : clock s = clock s' := congrArg (fun o => o.2.1) hobs
    let a := s.1.1
    let t := clock s
    let c := P.query a t
    have hb : Reachable P χ a t c := ⟨s, by simp [a], rfl, rfl⟩
    have hsingle' := hsingle a t c hb
    have hreply : ∀ i, P.reply i (s.1.2 i) t c =
        P.reply i (s'.1.2 i) t c := by
      intro i
      have hi := congrArg (fun o => o.2.2 i) hobs
      change P.reply i _ (clock s) (P.query s.1.1 (clock s)) =
        P.reply i _ (clock s') (P.query s'.1.1 (clock s')) at hi
      simpa only [a, t, c, ha, ht] using hi
    obtain ⟨D, hD⟩ := hexact
    have htarget := (hD s).symm.trans ((congrArg D hobs).trans (hD s'))
    have hsum : (∑ i, s.1.2 i) = ∑ i, s'.1.2 i := by
      simpa only [target, ha, add_right_inj] using htarget
    have htuple : s.1.2 = s'.1.2 := by
      by_cases hne : (NoninjectiveSenders (fun i x => P.reply i x t c)).Nonempty
      · obtain ⟨i₀, hi₀⟩ := hne
        have hxi : ∀ i, i ≠ i₀ → s.1.2 i = s'.1.2 i := by
          intro i hii
          have hiN : i ∉ NoninjectiveSenders (fun i x => P.reply i x t c) := by
            intro hiN
            exact hii (Finset.card_le_one.mp hsingle' i hiN i₀ hi₀)
          have hinj_i : Function.Injective (fun x => P.reply i x t c) := by
            simpa [NoninjectiveSenders] using hiN
          exact hinj_i (hreply i)
        have hsingle_sum : (∑ i, (s.1.2 i - s'.1.2 i)) =
            s.1.2 i₀ - s'.1.2 i₀ := by
          apply Finset.sum_eq_single i₀
          · intro i _ hi
            simp [hxi i hi]
          · simp
        have hi_eq : s.1.2 i₀ = s'.1.2 i₀ := by
          apply sub_eq_zero.mp
          rw [← hsingle_sum, Finset.sum_sub_distrib, hsum, sub_self]
        funext i
        by_cases hi : i = i₀
        · simpa [hi] using hi_eq
        · exact hxi i hi
      · have hxi : ∀ i, s.1.2 i = s'.1.2 i := by
          intro i
          have hiN : i ∉ NoninjectiveSenders (fun i x => P.reply i x t c) := by
            intro hiN
            exact hne ⟨i, hiN⟩
          have hinj_i : Function.Injective (fun x => P.reply i x t c) := by
            simpa [NoninjectiveSenders] using hiN
          exact hinj_i (hreply i)
        funext i
        exact hxi i
    have hh : (s.2 : G) = (s'.2 : G) := by
      have ht' : target s + (s.2 : G) = target s + (s'.2 : G) := by
        simpa [clock, target, ha, htuple] using ht
      exact add_left_cancel ht'
    exact Prod.ext (Prod.ext ha htuple) (Subtype.ext hh)

end D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotCollisionClassification
