/- GID: D5/S3/Combinatorics/Graph/StarForming/CyclicProjection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CyclicProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: Cyclic bridges between varying connected fibers survive deletion. -/

import D5.S3.Combinatorics.Graph.StarForming.CyclicConnectivity

/-! The cyclic path argument with genuinely varying vertex fibers, needed
for unequal padding cores. The projection and ports are actual graph data;
no uniform fiber type or cardinality is assumed. -/
namespace D5.S3.Combinatorics.Graph.StarForming.CyclicProjection

variable {V I : Type*} [DecidableEq I]

theorem preconnected (G : SimpleGraph V) (f : V → I)
    (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j)
    (p q : I → V) (hp : ∀ i, f (p i)=i) (hq : ∀ i, f (q i)=i)
    (hlocal : ∀ a b, f a=f b → G.Reachable a b)
    (hbridge : ∀ i, G.Adj (p i) (q (e i))) : G.Preconnected := by
  have hn : ∀ n : ℕ, ∀ i j, (e : I → I)^[n] i=j →
      ∀ a b, f a=i → f b=j → G.Reachable a b := by
    intro n
    induction n with
    | zero =>
      intro i j hij a b ha hb
      change i=j at hij
      exact hlocal a b (ha.trans (hij.trans hb.symm))
    | succ n ih =>
      intro i j hij a b ha hb
      exact (hlocal a (p i) (ha.trans (hp i).symm)).trans
        ((hbridge i).reachable.trans (ih (e i) j hij (q (e i)) b (hq _) hb))
  intro a b
  obtain ⟨n,hn'⟩ := horbit (f a) (f b)
  exact hn n _ _ hn' a b rfl rfl

/-- Distinct entrance and exit ports allow the cyclic route to choose its
direction after one arbitrary vertex is deleted. -/
theorem delete_preconnected (G : SimpleGraph V) (f : V → I)
    (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j)
    (p q : I → V) (hp : ∀ i, f (p i)=i) (hq : ∀ i, f (q i)=i)
    (hne : ∀ i, p i≠q i) (z : V)
    (hlocal : ∀ a b : {x : V // x≠z}, f a.val=f b.val →
      (G.induce {x | x≠z}).Reachable a b)
    (hbridge : ∀ i, G.Adj (p i) (q (e i))) :
    (G.induce {x | x≠z}).Preconnected := by
  classical
  let H := G.induce {x | x≠z}
  let root : V := if p (f z)=z then q (f z) else p (f z)
  have hroot : root≠z := by
    dsimp [root]
    split_ifs with h
    · exact fun he => hne (f z) (h.trans he.symm)
    · exact h
  have fr : f root=f z := by
    dsimp [root]
    split_ifs
    · exact hq _
    · exact hp _
  let r : {x : V // x≠z} := ⟨root,hroot⟩
  have path (t : Equiv.Perm I)
      (ht : ∀ i j, ∃ n : ℕ, (t : I → I)^[n] i=j)
      (a b : I → V) (ha : ∀ i, f (a i)=i) (hb : ∀ i, f (b i)=i)
      (hs : b (f z)≠z) (hedge : ∀ i, G.Adj (a i) (b (t i))) :
      ∀ v (hv : v≠z), H.Reachable ⟨v,hv⟩ r := by
    have bs (i : I) : b i≠z := by
      intro he
      have hi : i=f z := (hb i).symm.trans (congrArg f he)
      exact hs (hi ▸ he)
    have hn : ∀ n : ℕ, ∀ i, (t : I → I)^[n] i=f z →
        ∀ v (hv : v≠z), f v=i → H.Reachable ⟨v,hv⟩ r := by
      intro n
      induction n with
      | zero =>
        intro i hi v hv hf
        change i=f z at hi
        exact hlocal _ _ (hf.trans (hi.trans fr.symm))
      | succ n ih =>
        intro i hi v hv hf
        by_cases he : i=f z
        · exact hlocal _ _ (hf.trans (he.trans fr.symm))
        · have has : a i≠z := fun h => he ((ha i).symm.trans (congrArg f h))
          have hadj : H.Adj ⟨a i,has⟩ ⟨b (t i),bs (t i)⟩ := hedge i
          exact (hlocal _ _ (hf.trans (ha i).symm)).trans
            (hadj.reachable.trans (ih (t i) hi (b (t i)) (bs _) (hb _)))
    intro v hv
    obtain ⟨n,hn'⟩ := ht (f v) (f z)
    exact hn n _ hn' v hv rfl
  have hall : ∀ v : {x : V // x≠z}, H.Reachable v r := by
    rintro ⟨v,hv⟩
    by_cases he : q (f z)=z
    · have hs : p (f z)≠z := fun h => hne (f z) (h.trans he.symm)
      have hi : ∀ i j, ∃ n : ℕ, (e.symm : I → I)^[n] i=j := by
        intro i j
        obtain ⟨n,hn⟩ := horbit j i
        refine ⟨n,?_⟩
        rw [← hn]
        exact (Function.LeftInverse.iterate e.symm_apply_apply n) j
      apply path e.symm hi q p hq hp hs ?_ v hv
      intro i
      simpa using (hbridge (e.symm i)).symm
    · exact path e horbit p q hp hq he hbridge v hv
  intro a b
  exact (hall a).trans (hall b).symm

end D5.S3.Combinatorics.Graph.StarForming.CyclicProjection
