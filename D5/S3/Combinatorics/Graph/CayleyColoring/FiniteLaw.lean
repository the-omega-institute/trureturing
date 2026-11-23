/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native move-count law equals the occupied-bin law of independent uniformly marked targets. -/

import D5.S3.Combinatorics.Graph.CayleyColoring.ForestReassembly
import D5.S3.Combinatorics.Graph.CayleyColoring.CentralScheduler
import D5.S3.Combinatorics.Graph.CayleyColoring.CayleyCode

section

namespace CayleyReduction

open CayleyProbe CayleyScheduler CayleyColors CayleyForest CayleyMarks SimpleGraph

universe u w
variable {V : Type u} {A : Type w}

abbrev Colored (V : Type u) (A : Type w) := (V × Tree V) × (V → A)
abbrev EdgeDraw (V : Type u) (A : Type w) := Σ p : V × Tree V, A × (p.2.val.edgeSet → A)
abbrev ParentDraw (V : Type u) (A : Type w) := Σ p : V × Tree V, A × (Away p.1 → A)

noncomputable def edgeDrawEquiv [AddGroup A] : Colored V A ≃ EdgeDraw V A :=
  (Equiv.sigmaEquivProd (V × Tree V) (V → A)).symm.trans
    (Equiv.sigmaCongrRight fun p => edgeColorEquiv p.2 p.1)

noncomputable def parentDrawEquiv : EdgeDraw V A ≃ ParentDraw V A :=
  Equiv.sigmaCongrRight fun p =>
    Equiv.prodCongr (Equiv.refl A) (Equiv.arrowCongr (edgeEquiv p.2 p.1).symm (Equiv.refl A))

theorem parentDraw_values (s : EdgeDraw V A) :
    (parentDrawEquiv s).2.2 = s.2.2 ∘ edgeEquiv s.1.2 s.1.1 := rfl

def relabelColored (e : Equiv.Perm V) : Colored V A ≃ Colored V A :=
  Equiv.prodCongr (Equiv.prodCongr e (relabelEquiv e)) (Equiv.arrowCongr e (Equiv.refl A))

theorem relabel_conflict_iff (rank : Equiv.Perm V) (x : Colored V A) (v w : V) :
    (conflict ((relabelColored rank x).1.2).val (relabelColored rank x).2).Adj (rank v) (rank w)
      ↔ (conflict x.1.2.val x.2).Adj v w := by
  change (x.1.2.val.Adj (rank.symm (rank v)) (rank.symm (rank w)) ∧
    x.2 (rank.symm (rank v)) = x.2 (rank.symm (rank w))) ↔ _
  simp [conflict]

theorem ranked_peaks_card [Fintype V] [LinearOrder V] (rank : Equiv.Perm V)
    (s : Colored V A) :
    Nat.card {v // ∀ w, (conflict s.1.2.val s.2).Adj v w → rank w < rank v} =
      Nat.card {v // Peak (conflict (relabelColored rank s).1.2.val (relabelColored rank s).2) v} := by
  apply Nat.card_congr (Equiv.subtypeEquiv rank ?_)
  intro v
  unfold Peak
  constructor
  · intro h w hw
    obtain ⟨x,rfl⟩ := rank.surjective w
    exact h x ((relabel_conflict_iff rank s v x).mp hw)
  · intro h w hw
    exact h (rank w) ((relabel_conflict_iff rank s v w).mpr hw)

noncomputable def markedAt (V : Type u) (A : Type w) [Zero A] :=
  V × A × Marked V A

noncomputable def edgeMarked [Zero A] : EdgeDraw V A ≃ markedAt V A where
  toFun := fun s => (s.1.1, s.2.1, markedEquiv ⟨s.1.2,s.2.2⟩)
  invFun := fun s =>
    let x := markedEquiv.symm s.2.2
    ⟨(s.1,x.1),s.2.1,x.2⟩
  left_inv := by
    rintro ⟨⟨r,T⟩,a,d⟩
    let f (p : Σ T : Tree V, T.val.edgeSet → A) : EdgeDraw V A := ⟨(r,p.1),a,p.2⟩
    exact congrArg f ((markedEquiv (V := V) (A := A)).symm_apply_apply ⟨T,d⟩)
  right_inv := by
    rintro ⟨r,a,s⟩
    exact congrArg (fun x => (r,a,x)) ((markedEquiv (V := V) (A := A)).apply_symm_apply s)

noncomputable def markedAtTransport [Zero A] [Finite V] [LinearOrder V] :
    markedAt V A ≃ markedAt V A :=
  (Equiv.sigmaEquivProd V (A × Marked V A)).symm.trans <|
    (Equiv.sigmaCongrRight fun r => Equiv.prodCongr (Equiv.refl A) (markedForestEquiv r)).trans
      (Equiv.sigmaEquivProd V (A × Marked V A))

noncomputable def fromColored [AddGroup A] [Finite V] [LinearOrder V] :
    Colored V A ≃ ParentDraw V A :=
  edgeDrawEquiv.trans (edgeMarked.trans (markedAtTransport.trans (edgeMarked.symm.trans parentDrawEquiv)))

theorem card_complement [Fintype V] (P : V → Prop) :
    CayleyProbe.filterCard (fun v => ¬ P v) = Fintype.card V - Nat.card {v // P v} := by
  classical
  rw [filterCard_eq_natCard]
  have h := Nat.card_congr (Equiv.sumCompl P)
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := V)] at h
  omega

/-- An exact transport from the fixed-order monochrome peak count to the retained parent-target count. -/
theorem fromColored_count [AddGroup A] [Fintype V] [LinearOrder V] (s : Colored V A) :
    Fintype.card V - Nat.card {v // Peak (conflict s.1.2.val s.2) v} =
      filterCard (HasTarget (fromColored s).1.2 (fromColored s).1.1 (fromColored s).2.2) := by
  let x : EdgeDraw V A := edgeDrawEquiv s
  let m : Marked V A := markedEquiv ⟨x.1.2,x.2.2⟩
  have hconf : m.1.val.2 = conflict s.1.2.val s.2 :=
    conflict_retained s.1.2 s.1.1 s.2
  let m' : Marked V A := markedForestEquiv s.1.1 m
  let x' : (Σ T : Tree V, T.val.edgeSet → A) := markedEquiv.symm m'
  have hx' : retained x'.1 x'.2 = m'.1.val.2 := join_retained m'
  rw [← hconf, forestEquiv_peaks s.1.1 m.1]
  change Fintype.card V - Nat.card {v // NoRetainedChild m'.1.val.1 m'.1.val.2 s.1.1 v} =
    filterCard (HasTarget x'.1 s.1.1 (x'.2 ∘ edgeEquiv x'.1 s.1.1))
  rw [← card_complement]
  unfold NoRetainedChild
  have hp (v : V) : (¬ ¬ ∃ w, m'.1.val.2.Adj v w ∧
      m'.1.val.1.val.dist s.1.1 v < m'.1.val.1.val.dist s.1.1 w) ↔
      HasTarget x'.1 s.1.1 (x'.2 ∘ edgeEquiv x'.1 s.1.1) v := by
    classical
    rw [not_not, ← hx']
    exact retained_child_iff x'.1 s.1.1 x'.2 v
  rw [filterCard_eq_natCard, filterCard_eq_natCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight hp)

noncomputable def rankedTransport [AddGroup A] [Fintype V] [LinearOrder V] :
    (Equiv.Perm V × Colored V A) ≃ (Equiv.Perm V × ParentDraw V A) :=
  (Equiv.sigmaEquivProd (Equiv.Perm V) (Colored V A)).symm.trans <|
    (Equiv.sigmaCongrRight fun rank => (relabelColored rank).trans fromColored).trans
      (Equiv.sigmaEquivProd (Equiv.Perm V) (ParentDraw V A))

noncomputable def recolorCount [Fintype V] [LinearOrder V] (s : Equiv.Perm V × Colored V A) : Nat :=
  (rankedHistory (conflict s.2.1.2.val s.2.2) s.1 Set.univ).length

noncomputable def retainedTargetCount [Fintype V] [Zero A] (s : ParentDraw V A) : Nat :=
  filterCard (HasTarget s.1.2 s.1.1 s.2.2)

theorem rankedTransport_count [AddGroup A] [Fintype V] [LinearOrder V]
    (s : Equiv.Perm V × Colored V A) :
    recolorCount s = retainedTargetCount (rankedTransport s).2 := by
  rw [recolorCount, ranked_moves_complement, filterCard_eq_natCard, ranked_peaks_card s.1 s.2]
  exact fromColored_count (relabelColored s.1 s.2)

/-- The original sample and the independent uniform edge-label sample give equal probability
to each count. Equal numerator and denominator are witnessed by the same sample equivalence. -/
theorem recolor_retained_target_fibers [AddGroup A] [Fintype V] [LinearOrder V] (j : Nat) :
    Nat.card {s : Equiv.Perm V × Colored V A // recolorCount s = j} =
      Nat.card {s : Equiv.Perm V × ParentDraw V A // retainedTargetCount s.2 = j} :=
  Nat.card_congr ((rankedTransport (V := V) (A := A)).subtypeEquiv
    fun s => congrArg (· = j) (rankedTransport_count s) |>.to_iff)


end CayleyReduction

end

section

namespace CayleyFiniteLaw

open CayleyCore CayleyColors CayleyMarks CayleyParent CayleyProbe CayleyReduction CayleyScheduler SimpleGraph

universe u w
variable {V : Type u} {A : Type w} {K : Type*}

abbrev Throw (V : Type u) (A : Type w) := V × A
abbrev Throws (a : V) (A : Type w) := Away a → Throw V A

/-- The zero color-difference mark keeps the target. Every other mark sends it to discard. -/
noncomputable def bin [Zero A] (a : Throw V A) : Option V := by
  classical
  exact if a.2 = 0 then some a.1 else none

theorem bin_some_iff [Zero A] (x : Throw V A) (v : V) :
    bin x = some v ↔ x.1 = v ∧ x.2 = 0 := by
  classical
  by_cases h : x.2 = 0 <;> simp [bin, h]

theorem bin_none_iff [Zero A] (x : Throw V A) : bin x = none ↔ x.2 ≠ 0 := by
  classical
  by_cases h : x.2 = 0 <;> simp [bin, h]

noncomputable def occupied [Fintype V] [Zero A] {a : V} (t : Throws a A) : Nat :=
  filterCard (fun v : V => ∃ i, bin (t i) = some v)

noncomputable def codedDraw [Finite V] (a : V) (t : Throws a A) :
    (Σ p : V × Tree V, Away p.1 → A) :=
  let f : Away a → V := Prod.fst ∘ t
  let p := rootedCode a f
  ⟨(p.1,p.2), Prod.snd ∘ t ∘ (codeCoordinates a f).symm⟩

def prodFunctions (I : Type*) (X : Type*) (Y : Type*) :
    (I → X × Y) ≃ (I → X) × (I → Y) where
  toFun f := (Prod.fst ∘ f, Prod.snd ∘ f)
  invFun p i := (p.1 i,p.2 i)
  left_inv f := by funext i; rfl
  right_inv _ := rfl

noncomputable def codedDrawEquiv [Finite V] (a : V) :
    Throws a A ≃ (Σ p : V × Tree V, Away p.1 → A) :=
  (prodFunctions (Away a) V A).trans <|
    (Equiv.sigmaEquivProd (Away a → V) (Away a → A)).symm.trans <|
    Equiv.sigmaCongr ((rootedCode a).trans (Equiv.sigmaEquivProd V (Tree V))) (fun f =>
      Equiv.arrowCongr (codeCoordinates a f) (Equiv.refl A))

theorem codedDraw_eq [Finite V] (a : V) (t : Throws a A) :
    codedDrawEquiv a t = codedDraw a t := rfl

theorem coded_target_iff [Fintype V] [Zero A] {a : V} (t : Throws a A) (v : V) :
    HasTarget (codedDraw a t).1.2 (codedDraw a t).1.1 (codedDraw a t).2 v ↔
      ∃ i, bin (t i) = some v := by
  let f := Prod.fst ∘ t
  let e := codeCoordinates a f
  change (∃ j, parent ((rootedCode a) f).2 ((rootedCode a) f).1 j = v ∧
    (t (e.symm j)).2 = 0) ↔ _
  constructor
  · rintro ⟨j,hj,hc⟩
    refine ⟨e.symm j, (bin_some_iff _ _).mpr ⟨?_,hc⟩⟩
    have hs := rootedCode_targets a f (e.symm j)
    change parent ((rootedCode a) f).2 ((rootedCode a) f).1 (e (e.symm j)) =
      (t (e.symm j)).1 at hs
    rw [e.apply_symm_apply] at hs
    exact hs.symm.trans hj
  · rintro ⟨j,hj⟩
    obtain ⟨ht,hc⟩ := (bin_some_iff _ _).mp hj
    refine ⟨e j,(rootedCode_targets a f j).trans ht,?_⟩
    simpa only [Equiv.symm_apply_apply] using hc

noncomputable def rootedDrawEquiv [Finite V] (a : V) : A × Throws a A ≃ ParentDraw V A where
  toFun t := let d := codedDrawEquiv a t.2; ⟨d.1,t.1,d.2⟩
  invFun t := (t.2.1, (codedDrawEquiv a).symm ⟨t.1,t.2.2⟩)
  left_inv t := by simp
  right_inv t := by
    rcases t with ⟨p,c,d⟩
    let f (x : Σ p : V × Tree V, Away p.1 → A) : ParentDraw V A := ⟨x.1,c,x.2⟩
    exact congrArg f ((codedDrawEquiv a).apply_symm_apply ⟨p,d⟩)

theorem rootedDraw_count [Fintype V] [Zero A] (a : V) (t : A × Throws a A) :
    retainedTargetCount (rootedDrawEquiv a t) = occupied t.2 := by
  change filterCard (HasTarget (codedDrawEquiv a t.2).1.2 (codedDrawEquiv a t.2).1.1
    (codedDrawEquiv a t.2).2) = _
  rw [codedDraw_eq, occupied, filterCard_eq_natCard, filterCard_eq_natCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (coded_target_iff t.2))

noncomputable def countEquiv [Fintype V] [LinearOrder V] [AddGroup A] (a : V) :
    (Equiv.Perm V × Colored V A) ≃ (Equiv.Perm V × A) × Throws a A :=
  rankedTransport.trans ((Equiv.prodCongr (Equiv.refl _) (rootedDrawEquiv a).symm).trans
    (Equiv.prodAssoc _ _ _).symm)

theorem countEquiv_stat [Fintype V] [LinearOrder V] [AddGroup A] (a : V)
    (s : Equiv.Perm V × Colored V A) : recolorCount s = occupied ((countEquiv a) s).2 := by
  rw [rankedTransport_count]
  change retainedTargetCount (rankedTransport s).2 =
    occupied ((rootedDrawEquiv a).symm (rankedTransport s).2).2
  rw [← rootedDraw_count a, Equiv.apply_symm_apply]

noncomputable def frequency (X : Type*) (f : X → Nat) (j : Nat) : Nat :=
  Nat.card {x : X // f x = j}

theorem frequency_prod (B X : Type*) (f : X → Nat) (j : Nat) :
    frequency (B × X) (f ∘ Prod.snd) j = Nat.card B * frequency X f j := by
  let e : {x : B × X // f x.2 = j} ≃ B × {x : X // f x = j} :=
    ⟨fun x => (x.val.1,⟨x.val.2,x.prop⟩),
      fun x => ⟨(x.1,x.2.val),x.2.prop⟩,fun _ => rfl,fun _ => rfl⟩
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

/-- The exact equality of all finite pushforward probabilities, expressed by cross multiplying
the cardinalities of fibers and sample spaces. -/
theorem exact_count_law [Fintype V] [LinearOrder V] [AddGroup A] [Finite A]
    (anchor : V) (j : Nat) :
    frequency (Equiv.Perm V × Colored V A) recolorCount j * Nat.card (Throws anchor A) =
      frequency (Throws anchor A) occupied j * Nat.card (Equiv.Perm V × Colored V A) := by
  have hn : frequency (Equiv.Perm V × Colored V A) recolorCount j =
      frequency ((Equiv.Perm V × A) × Throws anchor A) (occupied ∘ Prod.snd) j :=
    Nat.card_congr ((countEquiv anchor).subtypeEquiv (fun s =>
      (congrArg (· = j) (countEquiv_stat anchor s)).to_iff))
  rw [hn, frequency_prod, Nat.card_congr (countEquiv (A := A) anchor)]
  simp only [Nat.card_prod]
  ac_rfl

theorem bin_some_card [Zero A] (v : V) :
    Nat.card {x : Throw V A // bin x = some v} = 1 := by
  let e : {x : Throw V A // bin x = some v} ≃ PUnit := by
    refine ⟨fun _ => (), fun _ => ⟨(v,0), (bin_some_iff _ _).mpr ⟨rfl,rfl⟩⟩, ?_, fun _ => rfl⟩
    intro x
    obtain ⟨h₁,h₂⟩ := (bin_some_iff x.val v).mp x.prop
    exact Subtype.ext (Prod.ext h₁.symm h₂.symm)
  rw [Nat.card_congr e]
  exact Nat.card_unique

theorem bin_none_card [Zero A] :
    Nat.card {x : Throw V A // bin x = none} = Nat.card V * Nat.card {c : A // c ≠ 0} := by
  let e : {x : Throw V A // bin x = none} ≃ V × {c : A // c ≠ 0} :=
    ⟨fun x => (x.val.1,⟨x.val.2,(bin_none_iff _).mp x.prop⟩),
      fun x => ⟨(x.1,x.2.val),(bin_none_iff _).mpr x.2.prop⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_prod]

theorem cardinality_nonzero {k : Nat} [NeZero k] :
    Nat.card {c : ZMod k // c ≠ 0} = k - 1 := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl (· = (0 : ZMod k)))
  have h₁ : Nat.card {x : ZMod k // x = 0} = 1 :=
    Nat.card_of_subsingleton ⟨0,rfl⟩
  rw [Nat.card_sum, h₁, Nat.card_eq_fintype_card (α := ZMod k), ZMod.card] at h
  change 1 + Nat.card {c : ZMod k // c ≠ 0} = k at h
  omega

theorem throw_fiber_product [Finite V] [Finite A] [Zero A] {I : Type*} [Fintype I]
    (outcome : I → Option V) :
    Nat.card {draw : I → Throw V A // ∀ i, bin (draw i) = outcome i} =
      ∏ i, Nat.card {x : Throw V A // bin x = outcome i} := by
  classical
  let e : {draw : I → Throw V A // ∀ i, bin (draw i) = outcome i} ≃
      ∀ i, {x : Throw V A // bin x = outcome i} :=
    ⟨fun draw i => ⟨draw.val i,draw.prop i⟩,
      fun draws => ⟨fun i => (draws i).val, fun i => (draws i).prop⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Nat.card_congr e]
  let : ∀ i, Fintype {x : Throw V A // bin x = outcome i} := fun _ => Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Nat.card_eq_fintype_card]

theorem embedded_conflict (G : SimpleGraph V) (embed : A ↪ K) (init : V → A) :
    conflict G (embed ∘ init) = conflict G init := by
  ext v w
  exact and_congr_right fun _ => embed.injective.eq_iff

/-- The sample over `Fin (n+1)` has exactly `n` throws. The bin fibers are one ordinary
microstate per label and `(n+1)*(k-1)` discard microstates out of `(n+1)*k`. -/
theorem fin_exact_law (n k : Nat) (hk : 2 ≤ k) (j : Nat) :
    let V := Fin (n + 1)
    let a : V := 0
    (frequency (Equiv.Perm V × Colored V (ZMod k)) recolorCount j *
        Nat.card (Throws a (ZMod k)) =
      frequency (Throws a (ZMod k)) occupied j *
        Nat.card (Equiv.Perm V × Colored V (ZMod k))) ∧
    Nat.card (Away a) = n ∧
    Nat.card (Throw V (ZMod k)) = (n + 1) * k ∧
    (∀ v : V, Nat.card {x : Throw V (ZMod k) // bin x = some v} = 1) ∧
    Nat.card {x : Throw V (ZMod k) // bin x = none} = (n + 1) * (k - 1) := by
  let V := Fin (n+1)
  let a : V := 0
  let : NeZero k := ⟨by omega⟩
  have aux : Nat.card (ZMod k) = k := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hA : Nat.card (Away a) = n := by
    classical
    have h := Nat.card_congr (Equiv.sumCompl (· = a))
    have h₁ : Nat.card {x : V // x = a} = 1 := Nat.card_of_subsingleton ⟨a,rfl⟩
    rw [Nat.card_sum, h₁, Nat.card_fin] at h
    change 1 + Nat.card (Away a) = n+1 at h
    omega
  have hT : Nat.card (Throw V (ZMod k)) = (n+1)*k := by
    rw [Nat.card_prod, aux]
    exact congrArg (· * k) (Nat.card_fin (n+1))
  refine ⟨exact_count_law a j,hA,hT,fun v => bin_some_card v,?_⟩
  rw [bin_none_card, cardinality_nonzero]
  exact congrArg (· * (k - 1)) (Nat.card_fin (n+1))


end CayleyFiniteLaw

end

section

namespace CayleyExactAudit

open CayleyColors CayleyFiniteLaw CayleyProbe CayleyReduction CayleyScheduler SimpleGraph

universe u w
variable {V : Type u} {K : Type w}
variable [Fintype V] [LinearOrder V]

/-- The source recoloring count evaluated via the exact terminal-history sampler. The embedding
allows the initial palette to be smaller than the free-color palette used for updates. -/
noncomputable def sourceCount {k : Nat} (embed : ZMod k ↪ K)
    (s : Equiv.Perm V × Colored V (ZMod k)) : Nat :=
  (rankedHistory (conflict s.2.1.2.val (embed ∘ s.2.2)) s.1 Set.univ).length

theorem sourceCount_eq {k : Nat} (embed : ZMod k ↪ K)
    (s : Equiv.Perm V × Colored V (ZMod k)) :
    sourceCount embed s = recolorCount s := by
  unfold sourceCount recolorCount
  rw [embedded_conflict]

/-- Every valid free-color policy has the terminal-history law used by the source sampler.
This holds for each original rooted tree, initial coloring and fixed policy tape. -/
theorem all_policy_histories {k : Nat} (embed : ZMod k ↪ K)
    (s : Colored V (ZMod k)) (policy : FreePolicy (K := K) s.1.2.val) (history : List V) :
    let color := embed ∘ s.2
    let G := s.1.2.val
    let accept := ∃ final, PolicyRun G policy [] color history final ∧
      ∀ v w, ¬ (conflict G final).Adj v w
    let chosen := {rank : Equiv.Perm V //
      rankedHistory (conflict G color) rank Set.univ = history}
    (accept → Nat.card chosen * choiceProduct (conflict G color) Set.univ history =
      Nat.card (Equiv.Perm V)) ∧
    (¬ accept → IsEmpty chosen) :=
  policy_terminal_law s.1.2.val policy (embed ∘ s.2) history

theorem source_count_law {k : Nat} (hk : 2 ≤ k) (embed : ZMod k ↪ K) (anchor : V) (j : Nat) :
    frequency (Equiv.Perm V × Colored V (ZMod k)) (sourceCount embed) j *
      Nat.card (Throws anchor (ZMod k)) =
      frequency (Throws anchor (ZMod k)) occupied j *
        Nat.card (Equiv.Perm V × Colored V (ZMod k)) := by
  let : NeZero k := ⟨by omega⟩
  simpa only [show sourceCount (V := V) embed = recolorCount from funext (sourceCount_eq embed)] using
    exact_count_law (A := ZMod k) anchor j

theorem sample_spaces_positive {k : Nat} (hk : 2 ≤ k) (anchor : V) :
    0 < Nat.card (Equiv.Perm V × Colored V (ZMod k)) ∧
      0 < Nat.card (Throws anchor (ZMod k)) := by
  let : NeZero k := ⟨by omega⟩
  let : Nonempty (Throws anchor (ZMod k)) := ⟨fun _ => (anchor,0)⟩
  let : Nonempty V := ⟨anchor⟩
  constructor
  · rw [Nat.card_congr (countEquiv (A := ZMod k) anchor)]
    exact Nat.card_pos
  · exact Nat.card_pos

theorem source_initially_proper {k : Nat} (embed : ZMod k ↪ K)
    (s : Equiv.Perm V × Colored V (ZMod k))
    (hproper : ∀ v w, s.2.1.2.val.Adj v w → s.2.2 v ≠ s.2.2 w) :
    sourceCount embed s = 0 := by
  rw [sourceCount_eq, recolorCount, initially_proper s.2.1.2.val s.2.2 hproper s.1]
  rfl

theorem singleton_samples {k : Nat} (embed : ZMod k ↪ K)
    (s : Equiv.Perm (Fin 1) × Colored (Fin 1) (ZMod k))
    (draw : Throws (0 : Fin 1) (ZMod k)) :
    sourceCount embed s = 0 ∧ occupied draw = 0 := by
  refine ⟨source_initially_proper embed s (fun a b h => (h.ne (Subsingleton.elim a b)).elim), ?_⟩
  rw [occupied, filterCard_eq_natCard]
  have h : IsEmpty {v : Fin 1 // ∃ i, bin (draw i) = some v} :=
    ⟨fun s => by
      obtain ⟨i,_⟩ := s.prop
      exact i.prop (Subsingleton.elim _ _)⟩
  let := h
  simp

/-- The exact all-size finite law for native labeled trees. The natural counts are the numerator
and denominator of each uniform sample probability. A throw is one independent uniform pair
of an ordinary label and a mark in `ZMod k`; its bin is the label precisely for mark zero. -/
theorem all_n_distribution (n k : Nat) (hn : 0 < n) (hk : 2 ≤ k) (embed : ZMod k ↪ K)
    (j : Nat) :
    let V := Fin n
    let a : V := ⟨0,hn⟩
    (frequency (Equiv.Perm V × Colored V (ZMod k)) (sourceCount embed) j *
        Nat.card (Throws a (ZMod k)) =
      frequency (Throws a (ZMod k)) occupied j *
        Nat.card (Equiv.Perm V × Colored V (ZMod k))) ∧
      0 < Nat.card (Equiv.Perm V × Colored V (ZMod k)) ∧
      0 < Nat.card (Throws a (ZMod k)) ∧
      Nat.card (Away a) = n - 1 ∧
      Nat.card (Throw V (ZMod k)) = n*k ∧
      (∀ v : V, Nat.card {x : Throw V (ZMod k) // bin x = some v} = 1) ∧
      Nat.card {x : Throw V (ZMod k) // bin x = none} = n * (k-1) := by
  cases n with
  | zero => omega
  | succ n =>
    let a : Fin (n+1) := 0
    have hs := sample_spaces_positive hk a
    have hc := fin_exact_law n k hk j
    exact ⟨source_count_law hk embed a j, hs.1, hs.2, hc.2.1, hc.2.2⟩



end CayleyExactAudit

end

section

namespace CayleyNativeLaw

open CayleyColors CayleyExactAudit CayleyFiniteLaw CayleyReduction CayleyScheduler SimpleGraph

universe u w
variable {V : Type u} {K : Type w}
variable [Fintype V] [LinearOrder V]

def Terminal (G : SimpleGraph V) (policy : FreePolicy (K := K) G) (c : V → K) (l : List V) : Prop :=
  ∃ final, PolicyRun G policy [] c l final ∧ ∀ v w, ¬ (conflict G final).Adj v w

/-- A common-denominator representation of the sequential process's probability at length `j`.
Each accepted mover history contributes the reciprocal product of its enabled-set sizes.
Multiplying that weight by the ranking-space cardinal gives its exact integer numerator. -/
abbrev NativeNumerator (G : SimpleGraph V) (policy : FreePolicy (K := K) G) (c : V → K) (j : Nat) :=
  Σ l : {l : List V // Terminal G policy c l ∧ l.length = j},
    Fin (Nat.card (Equiv.Perm V) / choiceProduct (conflict G c) Set.univ l.val)

noncomputable def conditionalEquiv (G : SimpleGraph V) (policy : FreePolicy (K := K) G)
    (c : V → K) (j : Nat) :
    NativeNumerator G policy c j ≃
      {rank : Equiv.Perm V // (rankedHistory (conflict G c) rank Set.univ).length = j} := by
  classical
  let hist : Equiv.Perm V → List V := fun rank => rankedHistory (conflict G c) rank Set.univ
  let I := {l : List V // Terminal G policy c l ∧ l.length = j}
  let Fiber (l : I) := {rank : Equiv.Perm V // hist rank = l.val}
  let W (l : I) := Nat.card (Equiv.Perm V) / choiceProduct (conflict G c) Set.univ l.val
  have hc (l : I) : Nat.card (Fiber l) = W l := by
    have h := (policy_terminal_law G policy c l.val).1 l.prop.1
    have hp : 0 < Nat.card (Equiv.Perm V) := Nat.card_pos
    change Nat.card (Fiber l) * choiceProduct (conflict G c) Set.univ l.val =
      Nat.card (Equiv.Perm V) at h
    have hd : 0 < choiceProduct (conflict G c) Set.univ l.val := by
      by_contra hn
      have hz := Nat.eq_zero_of_not_pos hn
      rw [hz, Nat.mul_zero] at h
      exact hp.ne' h.symm
    exact Nat.eq_div_of_mul_eq_right hd.ne' (by simpa only [Nat.mul_comm] using h)
  let coord (l : I) : Fiber l ≃ Fin (W l) :=
    let f : Fintype (Fiber l) := Fintype.ofFinite _
    Fintype.equivFinOfCardEq ((@Nat.card_eq_fintype_card (Fiber l) f).symm.trans (hc l))
  let f : (Σ l : I, Fiber l) → {rank : Equiv.Perm V // (hist rank).length = j} :=
    fun s => ⟨s.2.val, s.2.prop.symm ▸ s.1.prop.2⟩
  refine (Equiv.sigmaCongrRight fun l => (coord l).symm).trans (Equiv.ofBijective f ⟨?_,?_⟩)
  · rintro ⟨l,r,hr⟩ ⟨l',r',hr'⟩ h
    have he : r = r' := congrArg (fun x : {rank : Equiv.Perm V // (hist rank).length = j} => x.val) h
    subst r'
    have hl : l = l' := Subtype.ext (hr.symm.trans hr')
    subst l'
    rfl
  · rintro ⟨rank,h⟩
    have ok := rankedHistory_spec (conflict G c) rank Set.univ
    have hr : Terminal G policy c (hist rank) :=
      (proper_policyRun G policy c (hist rank)).mp ⟨ok.1.legal,ok.2⟩
    exact ⟨⟨⟨hist rank,hr,h⟩,⟨rank,rfl⟩⟩,rfl⟩

abbrev TotalNumerator {k : Nat} (embed : ZMod k ↪ K)
    (policy : (s : Colored V (ZMod k)) → FreePolicy (K := K) s.1.2.val) (j : Nat) :=
  Σ s : Colored V (ZMod k), NativeNumerator s.1.2.val (policy s) (embed ∘ s.2) j

noncomputable def totalEquiv {k : Nat} (embed : ZMod k ↪ K)
    (policy : (s : Colored V (ZMod k)) → FreePolicy (K := K) s.1.2.val) (j : Nat) :
    TotalNumerator embed policy j ≃
      {s : Equiv.Perm V × Colored V (ZMod k) // sourceCount embed s = j} := by
  let H := fun s : Colored V (ZMod k) =>
    {rank : Equiv.Perm V // sourceCount embed (rank,s) = j}
  refine (Equiv.sigmaCongrRight fun s => conditionalEquiv s.1.2.val (policy s) (embed ∘ s.2) j).trans ?_
  change (Σ s : Colored V (ZMod k), H s) ≃ {s // sourceCount embed s = j}
  exact ⟨fun x => ⟨(x.2.val,x.1),x.2.prop⟩,
    fun s => ⟨s.val.2, ⟨s.val.1,s.prop⟩⟩, fun _ => rfl, fun _ => rfl⟩

/-- The native-policy finite law with no ranking in the definition of the source numerator.
The right side counts distinct occupied ordinary bins after independent uniform microstate draws. -/
theorem native_daemon_occupancy (n k : Nat) (hn : 0 < n) (hk : 2 ≤ k) (embed : ZMod k ↪ K)
    (policy : (s : Colored (Fin n) (ZMod k)) → FreePolicy (K := K) s.1.2.val) (j : Nat) :
    let V := Fin n
    let a : V := ⟨0,hn⟩
    (Nat.card (TotalNumerator embed policy j) * Nat.card (Throws a (ZMod k)) =
      frequency (Throws a (ZMod k)) occupied j *
        Nat.card (Equiv.Perm V × Colored V (ZMod k))) ∧
      0 < Nat.card (Equiv.Perm V × Colored V (ZMod k)) ∧
      0 < Nat.card (Throws a (ZMod k)) ∧
      Nat.card (Away a) = n - 1 ∧
      Nat.card (Throw V (ZMod k)) = n*k ∧
      (∀ v : V, Nat.card {x : Throw V (ZMod k) // bin x = some v} = 1) ∧
      Nat.card {x : Throw V (ZMod k) // bin x = none} = n * (k-1) := by
  have h := all_n_distribution n k hn hk embed j
  dsimp only at h ⊢
  rw [Nat.card_congr (totalEquiv embed policy j)]
  exact h


end CayleyNativeLaw

end
