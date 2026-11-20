/- GID: D5/S3/Combinatorics/Graph/CliqueFactorization/Algebraic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CliqueFactorization/Algebraic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonedge rectangles characterize clique factorization over commutative groups. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Algebraic clique factorization

Anchored restrictions give a triangular family of interactions. Nonedge
rectangles annihilate precisely the interactions with nonclique support.
-/

public section
noncomputable section
open Finset Function
open scoped BigOperators
universe u v w

namespace SimpleGraph.CliqueFactorization

variable {V : Type u} {Ω : V → Type v} {A : Type w} [CommGroup A]
local instance : DecidableEq V := Classical.decEq V

private def mask (o : ∀ i, Ω i) (s : Finset V) (x : ∀ i, Ω i) : ∀ i, Ω i :=
  Function.updateFinset o s (fun i => x i)

private theorem mask_agree (o : ∀ i, Ω i) (s : Finset V) {x y : ∀ i, Ω i}
    (h : ∀ i ∈ s, x i = y i) : mask o s x = mask o s y := by
  funext i
  by_cases hi : i ∈ s <;> simp [mask, Function.updateFinset, hi, h]

private theorem mask_update (o x : ∀ i, Ω i) (s : Finset V) (i : V) :
    Function.update (mask o s x) i (x i) = mask o (insert i s) x := by
  funext k
  by_cases hk : k = i
  · subst k; simp [mask, Function.updateFinset]
  · simp [mask, Function.updateFinset, hk]

private def interaction (f : (∀ i, Ω i) → A) (o : ∀ i, Ω i)
    (s : Finset V) : (∀ i, Ω i) → A :=
  s.strongInductionOn fun s prev x =>
    f (mask o s x) / ∏ t ∈ s.ssubsets.attach, prev t.1 (mem_ssubsets.mp t.2) x

private theorem interaction_eq (f : (∀ i, Ω i) → A) (o : ∀ i, Ω i)
    (s : Finset V) (x : ∀ i, Ω i) :
    interaction f o s x = f (mask o s x) /
      ∏ t ∈ s.ssubsets, interaction f o t x := by
  conv_lhs => unfold interaction
  rw [Finset.strongInductionOn_eq]
  change f (mask o s x) / (∏ t ∈ s.ssubsets.attach, interaction f o t.1 x) = _
  rw [Finset.prod_attach s.ssubsets (fun t => interaction f o t x)]

private theorem interaction_support (f : (∀ i, Ω i) → A) (o : ∀ i, Ω i)
    (s : Finset V) : DependsOn (interaction f o s) (s : Set V) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro x y h
    rw [interaction_eq, interaction_eq, mask_agree o s h]
    congr 1
    apply Finset.prod_congr rfl
    intro t ht
    exact ih t (mem_ssubsets.mp ht) (fun i hi => h i ((mem_ssubsets.mp ht).subset hi))

private theorem interaction_reconstruct (f : (∀ i, Ω i) → A) (o : ∀ i, Ω i)
    (s : Finset V) (x : ∀ i, Ω i) :
    f (mask o s x) = ∏ t ∈ s.powerset, interaction f o t x := by
  have h := Finset.prod_erase_mul s.powerset (fun t => interaction f o t x)
    (Finset.mem_powerset.mpr (Finset.Subset.refl s))
  rw [← Finset.ssubsets, interaction_eq, mul_div_cancel] at h
  exact h

/-- For any one family reconstructing every anchored restriction of the same function,
the rectangle law kills every interaction whose support is not a clique. -/
private theorem nonclique_vanish (G : SimpleGraph V) (f : (∀ i, Ω i) → A)
    (o : ∀ i, Ω i) (κ : Finset V → (∀ i, Ω i) → A)
    (rec : ∀ s x, f (mask o s x) = ∏ t ∈ s.powerset, κ t x)
    (rect : ∀ i j, i ≠ j → ¬ G.Adj i j → ∀ x a b,
      f x * f (Function.update (Function.update x i a) j b) =
        f (Function.update x i a) * f (Function.update x j b))
    (s : Finset V) (hs : ¬ G.IsClique (s : Set V)) (x : ∀ i, Ω i) : κ s x = 1 := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    obtain ⟨i, j, hij, hnon⟩ := G.not_isClique_iff.mp hs
    have hi : (i : V) ∈ s := i.2
    have hj : (j : V) ∈ s := j.2
    have hne : (i : V) ≠ j := fun h => hij (Subtype.ext h)
    let p := (s.erase i).powerset
    let q := (s.erase j).powerset
    have hp : p ⊆ s.ssubsets := by
      intro t ht
      exact mem_ssubsets.mpr ((mem_powerset.mp ht).trans_ssubset (erase_ssubset hi))
    have hq : q ⊆ s.ssubsets := by
      intro t ht
      exact mem_ssubsets.mpr ((mem_powerset.mp ht).trans_ssubset (erase_ssubset hj))
    have hprod : (∏ t ∈ p ∪ q, κ t x) = ∏ t ∈ s.ssubsets, κ t x := by
      apply Finset.prod_subset (Finset.union_subset hp hq)
      intro t ht htunion
      have hts := mem_ssubsets.mp ht
      have hti : (i : V) ∈ t := by
        by_contra hn
        exact htunion (mem_union.mpr (Or.inl (mem_powerset.mpr
          (subset_erase.mpr ⟨hts.subset, hn⟩))))
      have htj : (j : V) ∈ t := by
        by_contra hn
        exact htunion (mem_union.mpr (Or.inr (mem_powerset.mpr
          (subset_erase.mpr ⟨hts.subset, hn⟩))))
      exact ih t hts (fun hc => hnon (hc hti htj hne))
    have hinter : p ∩ q = ((s.erase i).erase j).powerset := by
      ext t
      simp only [p, q, mem_inter, mem_powerset, subset_erase]
      tauto
    have overlap := Finset.prod_union_inter (s₁ := p) (s₂ := q) (f := fun t => κ t x)
    rw [hprod, hinter, ← rec, ← rec, ← rec] at overlap
    have hui := mask_update o x ((s.erase i).erase j) i
    have huj := mask_update o x ((s.erase i).erase j) j
    have hii : insert (i : V) ((s.erase i).erase j) = s.erase j := by
      ext k
      simp only [mem_insert, mem_erase]
      constructor
      · rintro (rfl | ⟨hkj, hki, hks⟩)
        · exact ⟨hne, hi⟩
        · exact ⟨hkj, hks⟩
      · rintro ⟨hkj, hks⟩
        by_cases hki : k = i
        · exact Or.inl hki
        · exact Or.inr ⟨hkj, hki, hks⟩
    have hjj : insert (j : V) ((s.erase i).erase j) = s.erase i :=
      Finset.insert_erase (mem_erase.mpr ⟨hne.symm, hj⟩)
    rw [hii] at hui
    rw [hjj] at huj
    have hdouble : Function.update
        (Function.update (mask o ((s.erase i).erase j) x) i (x i)) j (x j) =
        mask o s x := by
      rw [hui, mask_update, Finset.insert_erase hj]
    have hr := rect i j hne hnon (mask o ((s.erase i).erase j) x) (x i) (x j)
    rw [hdouble, hui, huj] at hr
    have heq : f (mask o s x) = ∏ t ∈ s.ssubsets, κ t x := by
      apply mul_right_cancel (b := f (mask o ((s.erase i).erase j) x))
      calc
        f (mask o s x) * f (mask o ((s.erase i).erase j) x) =
            f (mask o (s.erase i) x) * f (mask o (s.erase j) x) := by
              simpa [mul_comm] using hr
        _ = _ := overlap.symm
    have hall := Finset.prod_erase_mul s.powerset (fun t => κ t x)
      (mem_powerset.mpr (Finset.Subset.refl s))
    rw [← Finset.ssubsets, ← rec, heq] at hall
    exact mul_left_cancel (hall.trans (mul_one _).symm)

omit [CommGroup A] in
private theorem support_update {g : (∀ i, Ω i) → A} {s : Finset V}
    (hg : DependsOn g (s : Set V)) {i : V} (hi : i ∉ s)
    (x : ∀ i, Ω i) (a : Ω i) : g (Function.update x i a) = g x := by
  apply hg
  intro j hj
  have hji : j ≠ i := by
    intro he
    subst j
    exact hi hj
  exact Function.update_of_ne hji a x

/-- A group-valued function on an arbitrary dependent configuration space factors
over cliques exactly when every nonedge has vanishing multiplicative rectangles.
The empty clique carries the unrestricted global constant. -/
theorem rectangle_iff_clique_factorization [Fintype V] (G : SimpleGraph V)
    (f : (∀ i, Ω i) → A) :
    (∀ i j, i ≠ j → ¬ G.Adj i j → ∀ (x : ∀ i, Ω i) (a : Ω i) (b : Ω j),
      f x * f (Function.update (Function.update x i a) j b) =
        f (Function.update x i a) * f (Function.update x j b)) ↔
    ∃ Φ : Finset V → (∀ i, Ω i) → A,
      (∀ s : Finset V, DependsOn (Φ s) (s : Set V)) ∧
      (∀ s : Finset V, ¬ G.IsClique (s : Set V) → ∀ x, Φ s x = 1) ∧
      (∀ x, f x = ∏ s : Finset V, Φ s x) := by
  classical
  constructor
  · intro rect
    by_cases hx : Nonempty (∀ i, Ω i)
    · let o := Classical.choice hx
      refine ⟨interaction f o, interaction_support f o, ?_, ?_⟩
      · exact nonclique_vanish G f o (interaction f o) (interaction_reconstruct f o) rect
      · intro x
        simpa [mask, Function.updateFinset_univ] using
          interaction_reconstruct f o Finset.univ x
    · refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
      · intro s x; exact (hx ⟨x⟩).elim
      · intro s hs x; exact (hx ⟨x⟩).elim
      · intro x; exact (hx ⟨x⟩).elim
  · rintro ⟨Φ, hsupport, hneutral, hrec⟩ i j hne hnon x a b
    simp only [hrec]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s _
    by_cases hc : G.IsClique (s : Set V)
    · have homit : i ∉ s ∨ j ∉ s := by
        by_contra h
        push Not at h
        exact hnon (hc h.1 h.2 hne)
      rcases homit with hi | hj
      · rw [Function.update_comm hne a b x,
          support_update (hsupport s) hi (Function.update x j b) a,
          support_update (hsupport s) hi x a]
      · rw [support_update (hsupport s) hj (Function.update x i a) b,
          support_update (hsupport s) hj x b, mul_comm]
    · simp only [hneutral s hc, mul_one]

end SimpleGraph.CliqueFactorization
