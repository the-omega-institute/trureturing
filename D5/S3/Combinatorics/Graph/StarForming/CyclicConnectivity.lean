/- GID: D5/S3/Combinatorics/Graph/StarForming/CyclicConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CyclicConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: Actual cyclic bridges join vertex-deleted connected fibers. -/

import D5.S3.Combinatorics.Graph.StarForming.FiberConnectivity

/-! The cyclic block-path argument in the received H0, padding and long-core
constructions. The hypotheses require actual internal and bridge edges.
A single deletion is bypassed in the appropriate cyclic direction. -/
namespace D5.S3.Combinatorics.Graph.StarForming.CyclicConnectivity
variable {I A : Type} [DecidableEq I] [DecidableEq A]

/-- Local connectivity and actual cyclic bridges give global connectivity. -/
theorem preconnected (G : SimpleGraph (I × A)) (B : SimpleGraph A)
    (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j)
    (p q : A) (hB : B.Preconnected)
    (hint : ∀ i a b, B.Adj a b → G.Adj (i,a) (i,b))
    (hbridge : ∀ i, G.Adj (i,p) (e i,q)) : G.Preconnected := by
  have hlocal (i : I) (a b : A) : G.Reachable (i,a) (i,b) := by
    let f : B →g G := ⟨fun a => (i,a),fun h => hint i _ _ h⟩
    exact (hB a b).map f
  have hn : ∀ n : ℕ, ∀ i j, (e : I → I)^[n] i=j →
      ∀ a b : A, G.Reachable (i,a) (j,b) := by
    intro n
    induction n with
    | zero =>
      intro i j hij a b
      change i=j at hij
      subst j
      exact hlocal i a b
    | succ n ih =>
      intro i j hij a b
      exact (hlocal i a p).trans ((hbridge i).reachable.trans (ih (e i) j hij q b))
  rintro ⟨i,a⟩ ⟨j,b⟩
  obtain ⟨n,hn'⟩ := horbit i j
  exact hn n i j hn' a b

/-- When both distinct bridge ports and all vertex-deleted fibers are
available, every actual one-vertex deletion of the cyclic assembly is connected. -/
theorem delete_preconnected (G : SimpleGraph (I × A)) (B : SimpleGraph A)
    (e : Equiv.Perm I) (horbit : ∀ i j, ∃ n : ℕ, (e : I → I)^[n] i=j)
    (p q : A) (hpq : p≠q) (hB : B.Preconnected)
    (hdelete : ∀ z : A, (B.induce {a | a≠z}).Preconnected)
    (hint : ∀ i a b, B.Adj a b → G.Adj (i,a) (i,b))
    (hbridge : ∀ i, G.Adj (i,p) (e i,q)) (z : I × A) :
    (G.induce {x | x≠z}).Preconnected := by
  let H := G.induce {x | x≠z}
  let root : A := if z.2=p then q else p
  have hroot : (z.1,root)≠z := by
    intro he
    have hv := congrArg Prod.snd he
    dsimp [root] at hv
    split_ifs at hv with h
    · exact hpq (h.symm.trans hv.symm)
    · exact h hv.symm
  let r : {x : I × A // x≠z} := ⟨(z.1,root),hroot⟩
  have hlocal (i : I) (a b : A) (ha : (i,a)≠z) (hb : (i,b)≠z) :
      H.Reachable ⟨(i,a),ha⟩ ⟨(i,b),hb⟩ := by
    by_cases hi : i=z.1
    · subst i
      have ha' : a≠z.2 := fun he => ha (Prod.ext rfl he)
      have hb' : b≠z.2 := fun he => hb (Prod.ext rfl he)
      let f : (B.induce {a | a≠z.2}) →g H :=
        ⟨fun a => ⟨(z.1,a.val),fun h => a.property (congrArg Prod.snd h)⟩,
          fun h => hint z.1 _ _ h⟩
      exact ((hdelete z.2) ⟨a,ha'⟩ ⟨b,hb'⟩).map f
    · let f : B →g H :=
        ⟨fun a => ⟨(i,a),fun h => hi (congrArg Prod.fst h)⟩,fun h => hint i _ _ h⟩
      exact (hB a b).map f
  have path (t : Equiv.Perm I)
      (ht : ∀ i j, ∃ n : ℕ, (t : I → I)^[n] i=j) (a b : A)
      (hb : b≠z.2)
      (hedge : ∀ i, G.Adj (i,a) (t i,b)) :
      ∀ i v (hv : (i,v)≠z), H.Reachable ⟨(i,v),hv⟩ r := by
    have hn : ∀ n : ℕ, ∀ i, (t : I → I)^[n] i=z.1 →
        ∀ v (hv : (i,v)≠z), H.Reachable ⟨(i,v),hv⟩ r := by
      intro n
      induction n with
      | zero =>
        intro i hi v hv
        change i=z.1 at hi
        subst i
        exact hlocal z.1 v root hv hroot
      | succ n ih =>
        intro i hi v hv
        by_cases he : i=z.1
        · subst i
          exact hlocal z.1 v root hv hroot
        · have ha : (i,a)≠z := fun h => he (congrArg Prod.fst h)
          have hb' : (t i,b)≠z := fun h => hb (congrArg Prod.snd h)
          have hed : H.Adj ⟨(i,a),ha⟩ ⟨(t i,b),hb'⟩ := hedge i
          exact (hlocal i v a hv ha).trans (hed.reachable.trans (ih (t i) hi b hb'))
    intro i v hv
    obtain ⟨n,hi⟩ := ht i z.1
    exact hn n i hi v hv
  have hall : ∀ x : {x : I × A // x≠z}, H.Reachable x r := by
    rintro ⟨⟨i,v⟩,hv⟩
    by_cases hq : q=z.2
    · have hp : p≠z.2 := fun h => hpq (h.trans hq.symm)
      have hi : ∀ i j, ∃ n : ℕ, (e.symm : I → I)^[n] i=j := by
        intro i j
        obtain ⟨n,hn⟩ := horbit j i
        refine ⟨n,?_⟩
        rw [← hn]
        exact (Function.LeftInverse.iterate e.symm_apply_apply n) j
      apply path e.symm hi q p hp ?_ i v hv
      intro j
      simpa using (hbridge (e.symm j)).symm
    · exact path e horbit p q hq hbridge i v hv
  intro a b
  exact (hall a).trans (hall b).symm

end D5.S3.Combinatorics.Graph.StarForming.CyclicConnectivity
