/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47Forest
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47Forest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Directed generator-labelled forest elimination with one residual per powered component. -/

import D5.S3.FiniteGroups.NikolovSegal.TransitiveCoordinates
import Mathlib.Data.List.Sort

/-!
Nikolov--Segal, Part I, pp. 230--231, equations (47)--(50).

Here an edge variable is labelled by `(generator, source)`.  Oppositely
directed permutation arcs are different variables.  We eliminate variables,
not vertex transports.  All products below retain generator order.
-/
set_option autoImplicit false
namespace NikolovSegal
namespace Equation47
universe u

variable {S I : Type u} [Group S] [DecidableEq I] {m : ℕ}

abbrev Arc (m : ℕ) (I : Type u) := Fin m × I

def incident (τ : Fin m → Equiv.Perm I) (e : Arc m I) (v : I) : Prop :=
  v = e.2 ∨ v = τ e.1 e.2

def vertex (τ : Fin m → Equiv.Perm I) (α : Fin m → I → MulAut S)
    (a : Arc m I → S) (v : I) : S :=
  orderedProduct (fun j =>
    (a (j, v))⁻¹ * α j ((τ j).symm v) (a (j, (τ j).symm v)))

theorem actual_vertex
    {q : ℕ} (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (y c : Fin m → I → S) (v : I) :
    vertex (fun j => σ j ^ q) (fun j i => correctedCycleComponent β σ y j i q)
      (fun e => c e.1 e.2) v =
      orderedProduct (fun j =>
          (c j v)⁻¹ * (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)) v) := by
  unfold vertex
  congr 1
  funext j
  have h := actual_corrected_q_power_coordinate k σ β hcoord y j
    ((σ j ^ q).symm v) q (c j)
  simpa only [Equiv.apply_symm_apply] using congrArg (fun z => (c j v)⁻¹ * z) h.symm

private theorem vertex_congr
    (τ : Fin m → Equiv.Perm I) (α : Fin m → I → MulAut S)
    {a b : Arc m I → S} (v : I)
    (h : ∀ e, incident τ e v → a e = b e) :
    vertex τ α a v = vertex τ α b v := by
  unfold vertex
  congr 1
  funext j
  rw [h (j,v) (Or.inl rfl), h (j,(τ j).symm v) (Or.inr (by simp))]

private theorem vertex_update_not_incident
    (τ : Fin m → Equiv.Perm I) (α : Fin m → I → MulAut S)
    (a : Arc m I → S) (e : Arc m I) (x : S) (v : I)
    (h : ¬ incident τ e v) :
    vertex τ α (Function.update a e x) v = vertex τ α a v := by
  apply vertex_congr
  intro f hf
  have hfe : f ≠ e := by
    intro he
    subst f
    exact h hf
  exact Function.update_of_ne hfe x a

private theorem ofFn_update (f : Fin m → S) (j : Fin m) (x : S) :
    List.ofFn (Function.update f j x) = (List.ofFn f).set j.val x := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < m := by simpa using h₁
    simp only [List.getElem_ofFn, List.getElem_set]
    by_cases h : i = j.val
    · subst i
      simp
    · have hfin : (⟨i,hi⟩ : Fin m) ≠ j := fun hj => h (congrArg Fin.val hj)
      simp [Ne.symm h,hfin]

private theorem ordered_update_bijective
    (f : Fin m → S) (j : Fin m) (g : S → S) (hg : Function.Bijective g) :
    Function.Bijective (fun x => orderedProduct (Function.update f j (g x))) := by
  have heq : ∀ x, orderedProduct (Function.update f j (g x)) =
      ((List.ofFn f).take j.val).prod * g x *
        ((List.ofFn f).drop (j.val + 1)).prod := by
    intro x
    unfold orderedProduct
    rw [ofFn_update, List.prod_set]
    simp [j.isLt]
  let A := ((List.ofFn f).take j.val).prod
  let B := ((List.ofFn f).drop (j.val + 1)).prod
  have hAB : Function.Bijective (fun x : S => A * x * B) := by
    constructor
    · intro x z h
      exact mul_left_cancel (mul_right_cancel h)
    · intro z
      exact ⟨A⁻¹ * z * B⁻¹, by simp [mul_assoc]⟩
  have hfun : (fun x => orderedProduct (Function.update f j (g x))) =
      (fun x => A * g x * B) := funext heq
  rw [hfun]
  exact hAB.comp hg

theorem vertex_update_bijective
    (τ : Fin m → Equiv.Perm I) (α : Fin m → I → MulAut S)
    (a : Arc m I → S) (e : Arc m I) (v : I)
    (hloop : τ e.1 e.2 ≠ e.2) (hv : incident τ e v) :
    Function.Bijective (fun x => vertex τ α (Function.update a e x) v) := by
  let f : Fin m → S := fun j =>
    (a (j,v))⁻¹ * α j ((τ j).symm v) (a (j,(τ j).symm v))
  let g : S → S := fun x =>
    ((Function.update a e x) (e.1,v))⁻¹ *
      α e.1 ((τ e.1).symm v) ((Function.update a e x) (e.1,(τ e.1).symm v))
  have heq : ∀ x, vertex τ α (Function.update a e x) v =
      orderedProduct (Function.update f e.1 (g x)) := by
    intro x
    unfold vertex
    congr 1
    funext j
    by_cases hj : j = e.1
    · subst j
      simp [g]
    · have h₁ : (j,v) ≠ e := fun h => hj (congrArg Prod.fst h)
      have h₂ : (j,(τ j).symm v) ≠ e := fun h => hj (congrArg Prod.fst h)
      simp [h₁, h₂, hj, f]
  have hg : Function.Bijective g := by
    rcases hv with hv | hv
    · subst v
      have hpre : (τ e.1).symm e.2 ≠ e.2 := by
        intro h
        have := congrArg (τ e.1) h
        simp only [Equiv.apply_symm_apply] at this
        exact hloop this.symm
      have hne : (e.1,(τ e.1).symm e.2) ≠ e := by
        intro h
        exact hpre (congrArg Prod.snd h)
      have hform : ∀ x, g x = x⁻¹ * α e.1 ((τ e.1).symm e.2)
          (a (e.1,(τ e.1).symm e.2)) := by
        intro x
        simp [g, hne]
      constructor
      · intro x z h
        simp only [hform] at h
        exact inv_injective (mul_right_cancel h)
      · intro z
        refine ⟨α e.1 ((τ e.1).symm e.2) (a (e.1,(τ e.1).symm e.2)) * z⁻¹, ?_⟩
        simp [hform, mul_assoc]
    · subst v
      have hne : (e.1,τ e.1 e.2) ≠ e := by
        intro h
        exact hloop (congrArg Prod.snd h)
      have hform : ∀ x, g x = (a (e.1,τ e.1 e.2))⁻¹ * α e.1 e.2 x := by
        intro x
        simp [g, hne]
      constructor
      · intro x z h
        simp only [hform] at h
        exact (α e.1 e.2).injective (mul_left_cancel h)
      · intro z
        refine ⟨(α e.1 e.2).symm (a (e.1,τ e.1 e.2) * z), ?_⟩
        simp [hform]
  simpa only [heq] using ordered_update_bijective f e.1 g hg

def LeafOrder (τ : Fin m → Equiv.Perm I) (L : List (I × Arc m I)) : Prop :=
  (∀ p ∈ L, τ p.2.1 p.2.2 ≠ p.2.2 ∧ incident τ p.2 p.1) ∧
    L.Pairwise (fun p r => ¬ incident τ r.2 p.1)

noncomputable def solve (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (a : Arc m I → S)
    (p : I × Arc m I) (κ : I → S) : S := by
  classical
  exact
    if h : τ p.2.1 p.2.2 ≠ p.2.2 ∧ incident τ p.2 p.1 then
      Classical.choose ((vertex_update_bijective τ α a p.2 p.1 h.1 h.2).2 (κ p.1))
    else 1

private theorem solve_spec (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (a : Arc m I → S)
    (p : I × Arc m I) (κ : I → S)
    (h : τ p.2.1 p.2.2 ≠ p.2.2 ∧ incident τ p.2 p.1) :
    vertex τ α (Function.update a p.2 (solve τ α a p κ)) p.1 = κ p.1 := by
  simp only [solve, dif_pos h]
  exact Classical.choose_spec ((vertex_update_bijective τ α a p.2 p.1 h.1 h.2).2 (κ p.1))

noncomputable def eliminate (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (κ : I → S) :
    List (I × Arc m I) → (Arc m I → S) → (Arc m I → S)
  | [], a => a
  | p :: L, a => eliminate τ α κ L
      (Function.update a p.2 (solve τ α a p κ))

theorem eliminate_unused (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (κ : I → S)
    (L : List (I × Arc m I)) (a : Arc m I → S) (e : Arc m I)
    (h : ∀ p ∈ L, e ≠ p.2) : eliminate τ α κ L a e = a e := by
  induction L generalizing a with
  | nil => rfl
  | cons p L ih =>
    rw [eliminate, ih _ (fun r hr => h r (by simp [hr]))]
    exact Function.update_of_ne (h p (by simp)) _ _

theorem eliminate_loop (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (κ : I → S)
    (L : List (I × Arc m I)) (hL : LeafOrder τ L)
    (a : Arc m I → S) (e : Arc m I) (h : τ e.1 e.2 = e.2) :
    eliminate τ α κ L a e = a e := by
  apply eliminate_unused
  intro p hp he
  exact (hL.1 p hp).1 (he ▸ h)

private theorem eliminate_vertex_untouched (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (κ : I → S)
    (L : List (I × Arc m I)) (a : Arc m I → S) (v : I)
    (h : ∀ p ∈ L, ¬ incident τ p.2 v) :
    vertex τ α (eliminate τ α κ L a) v = vertex τ α a v := by
  induction L generalizing a with
  | nil => rfl
  | cons p L ih =>
    rw [eliminate, ih _ (fun r hr => h r (by simp [hr]))]
    exact vertex_update_not_incident τ α a p.2 _ v (h p (by simp))

theorem eliminate_solves (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (κ : I → S)
    (L : List (I × Arc m I)) (hL : LeafOrder τ L) (a : Arc m I → S) :
    ∀ p ∈ L, vertex τ α (eliminate τ α κ L a) p.1 = κ p.1 := by
  induction L generalizing a with
  | nil => simp
  | cons p L ih =>
    have htail : LeafOrder τ L := ⟨fun r hr => hL.1 r (by simp [hr]),
      (List.pairwise_cons.mp hL.2).2⟩
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      rw [eliminate, eliminate_vertex_untouched τ α κ L _ p.1
        (List.pairwise_cons.mp hL.2).1]
      exact solve_spec τ α a p κ (hL.1 p (by simp))
    · exact ih htail _ r hr

theorem eliminate_unique (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (κ : I → S)
    (L : List (I × Arc m I)) (hL : LeafOrder τ L)
    (a z : Arc m I → S)
    (hunused : ∀ e, (∀ p ∈ L, e ≠ p.2) → z e = a e)
    (hz : ∀ p ∈ L, vertex τ α z p.1 = κ p.1) :
    eliminate τ α κ L a = z := by
  induction L generalizing a with
  | nil => exact (funext fun e => hunused e (by simp)).symm
  | cons p L ih =>
    have hp := hL.1 p (by simp)
    have htail : LeafOrder τ L := ⟨fun r hr => hL.1 r (by simp [hr]),
      (List.pairwise_cons.mp hL.2).2⟩
    have heq : vertex τ α (Function.update a p.2 (z p.2)) p.1 = κ p.1 := by
      rw [← hz p (by simp)]
      apply vertex_congr
      intro e he
      by_cases hep : e = p.2
      · subst e
        simp
      · rw [Function.update_of_ne hep]
        exact (hunused e (by
          intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · simpa [hr] using hep
          · intro her
            exact (List.pairwise_cons.mp hL.2).1 r hr (her ▸ he))).symm
    have hval : solve τ α a p κ = z p.2 :=
      (vertex_update_bijective τ α a p.2 p.1 hp.1 hp.2).1
        ((solve_spec τ α a p κ hp).trans heq.symm)
    rw [eliminate, hval]
    apply ih htail
    · intro e he
      by_cases hep : e = p.2
      · subst e
        simp
      · rw [Function.update_of_ne hep]
        apply hunused
        intro r hr
        rcases List.mem_cons.mp hr with hr | hr
        · simpa [hr] using hep
        · exact he r hr
    · exact fun r hr => hz r (by simp [hr])

theorem reconstruction (τ : Fin m → Equiv.Perm I)
    (α : Fin m → I → MulAut S) (κ : I → S)
    (L : List (I × Arc m I)) (hL : LeafOrder τ L) (a : Arc m I → S) :
    (∃ z : Arc m I → S,
      (∀ e, (∀ p ∈ L, e ≠ p.2) → z e = a e) ∧
      ∀ v, vertex τ α z v = κ v) ↔
    ∀ v, (∀ p ∈ L, v ≠ p.1) →
      vertex τ α (eliminate τ α κ L a) v = κ v := by
  constructor
  · rintro ⟨z, hu, hz⟩
    rw [eliminate_unique τ α κ L hL a z hu (fun p _ => hz p.1)]
    exact fun v _ => hz v
  · intro h
    refine ⟨eliminate τ α κ L a, ?_, ?_⟩
    · intro e he
      exact eliminate_unused τ α κ L a e he
    · intro v
      by_cases hv : ∃ p ∈ L, v = p.1
      · obtain ⟨p,hp,rfl⟩ := hv
        exact eliminate_solves τ α κ L hL a p hp
      · exact h v (by simpa only [not_exists, not_and] using hv)

theorem exists_actual_leafOrder
    [Fintype I] {q : ℕ} (σ : Fin m → Equiv.Perm I) (r : I → I)
    (hr : ∀ v, (qPowerGraph σ q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph σ q).Reachable v w → r v = r w) :
    ∃ (F : SimpleGraph I) (L : List (I × Arc m I)),
      F ≤ qPowerGraph σ q ∧ F.IsAcyclic ∧
      F.Reachable = (qPowerGraph σ q).Reachable ∧
      LeafOrder (fun j => σ j ^ q) L ∧
      (∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v) ∧
      (∀ p ∈ L, F.Adj p.2.2 ((σ p.2.1 ^ q) p.2.2)) := by
  classical
  obtain ⟨F,hF,hacyc,hreach⟩ := qPowerGraph_spanningForest σ (q := q)
  let d : I → ℕ := fun v => F.dist (r v) v
  have hparent : ∀ v, v ≠ r v → ∃ w, F.Adj v w ∧ d w < d v := by
    intro v hv
    have hrv : F.Reachable (r v) v := by rw [hreach]; exact hr v
    obtain ⟨p,hp,hlen⟩ := hrv.exists_path_of_dist
    have hnil : ¬ p.Nil := p.not_nil_of_ne hv.symm
    have hadj := (p.adj_penultimate hnil).symm
    have hroot : r p.penultimate = r v :=
      hconst _ _ ((hF hadj.symm).reachable)
    refine ⟨p.penultimate, hadj, ?_⟩
    have hdist := SimpleGraph.dist_le p.dropLast
    have hlen' := p.length_dropLast_add_one hnil
    dsimp [d]
    rw [hroot]
    omega
  let N := {v : I // v ≠ r v}
  let parent : N → I := fun v => Classical.choose (hparent v v.2)
  have hp : ∀ v : N, F.Adj v.val (parent v) ∧ d (parent v) < d v.val :=
    fun v => Classical.choose_spec (hparent v v.2)
  have he : ∀ v : N, ∃ e : Arc m I,
      (e.2 = v.val ∧ (σ e.1 ^ q) e.2 = parent v) ∨
      (e.2 = parent v ∧ (σ e.1 ^ q) e.2 = v.val) := by
    intro v
    obtain ⟨j,hj | hj⟩ := qPowerForestEdgeLabel σ hF (hp v).1
    · exact ⟨(j,v.val), Or.inl ⟨rfl,hj⟩⟩
    · exact ⟨(j,parent v), Or.inr ⟨rfl,hj⟩⟩
  let edge : N → Arc m I := fun v => Classical.choose (he v)
  have hespec : ∀ v : N,
      ((edge v).2 = v.val ∧ (σ (edge v).1 ^ q) (edge v).2 = parent v) ∨
      ((edge v).2 = parent v ∧ (σ (edge v).1 ^ q) (edge v).2 = v.val) :=
    fun v => Classical.choose_spec (he v)
  have hend : ∀ (v : N) w,
      incident (fun j => σ j ^ q) (edge v) w ↔ w = v.val ∨ w = parent v := by
    intro v w
    rcases hespec v with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · unfold incident
      rw [ht,hs]
    · unfold incident
      rw [ht,hs,or_comm]
  have hlo : ∀ v : N, (σ (edge v).1 ^ q) (edge v).2 ≠ (edge v).2 := by
    intro v
    rcases hespec v with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [ht,hs]
      intro h
      have := (hp v).2
      rw [h] at this
      exact (Nat.lt_irrefl _ this)
    · rw [ht,hs]
      intro h
      have := (hp v).2
      rw [← h] at this
      exact (Nat.lt_irrefl _ this)
  let B : List N := Finset.univ.toList
  let V := B.mergeSort (fun v w => decide (d w.val ≤ d v.val))
  have hmem : ∀ v : N, v ∈ V := by simp [V,B]
  have hnodup : V.Nodup := (List.mergeSort_perm B _).nodup_iff.mpr
    (Finset.nodup_toList _)
  have hsorted : V.Pairwise (fun v w => d w.val ≤ d v.val) := by
    have hh := List.pairwise_mergeSort
      (le := fun v w : N => decide (d w.val ≤ d v.val))
      (by intro a b c; simp only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) B
    simpa only [decide_eq_true_eq] using hh
  let f : N → I × Arc m I := fun v => (v.val,edge v)
  refine ⟨F,V.map f,hF,hacyc,hreach,?_,?_,?_⟩
  · constructor
    · intro p hp'
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp'
      exact ⟨hlo v, (hend v v.val).mpr (Or.inl rfl)⟩
    · rw [List.pairwise_map]
      apply (hsorted.and hnodup).imp
      intro v w h
      change ¬ incident (fun j => σ j ^ q) (edge w) v.val
      rw [hend]
      rintro (hvw | hvp)
      · exact h.2 (Subtype.ext hvw)
      · have hd := (hp w).2
        rw [← hvp] at hd
        omega
  · intro v
    constructor
    · rintro ⟨p,hp',hpv⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hp'
      change w.val = v at hpv
      simpa only [hpv] using w.2
    · intro hv
      exact ⟨f ⟨v,hv⟩, List.mem_map.mpr ⟨⟨v,hv⟩,hmem _,rfl⟩,rfl⟩
  · intro p hp'
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp'
    change F.Adj (edge v).2 ((σ (edge v).1 ^ q) (edge v).2)
    rcases hespec v with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [ht,hs]; exact (hp v).1
    · rw [ht,hs]; exact (hp v).1.symm

theorem actual_forest_reconstruction
    [Fintype I] {q : ℕ}
    (k : Fin m → MulAut (I → S)) (σ : Fin m → Equiv.Perm I)
    (β : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (σ j i) = β j i (z i))
    (y : Fin m → I → S) (r : I → I)
    (hr : ∀ v, (qPowerGraph σ q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph σ q).Reachable v w → r v = r w) :
    ∃ L : List (I × Arc m I),
      LeafOrder (fun j => σ j ^ q) L ∧
      (∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v) ∧
      ∀ (κ : I → S) (a : Arc m I → S),
      (∃ c : Fin m → I → S,
        (∀ e, (∀ p ∈ L, e ≠ p.2) → c e.1 e.2 = a e) ∧
        ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
          (((k j * MulAut.conj (y j)⁻¹) ^ q) (c j)) v) = κ v) ↔
      ∀ v, v = r v →
        vertex (fun j => σ j ^ q)
          (fun j i => correctedCycleComponent β σ y j i q)
          (eliminate (fun j => σ j ^ q)
            (fun j i => correctedCycleComponent β σ y j i q) κ L a) v = κ v := by
  obtain ⟨F,L,hF,hacyc,hreach,hL,hmem,hedge⟩ :=
    exists_actual_leafOrder σ r hr hconst
  refine ⟨L,hL,hmem,?_⟩
  intro κ a
  have hres := reconstruction (fun j => σ j ^ q)
    (fun j i => correctedCycleComponent β σ y j i q) κ L hL a
  have hroots : ∀ v, (∀ p ∈ L, v ≠ p.1) ↔ v = r v := by
    intro v
    have := hmem v
    simp only [← not_exists, not_and, ne_eq] at this ⊢
    aesop
  simp_rw [hroots] at hres
  rw [← hres]
  constructor
  · rintro ⟨c,hu,hc⟩
    exact ⟨fun e => c e.1 e.2,hu,fun v => (actual_vertex k σ β hcoord y c v).trans (hc v)⟩
  · rintro ⟨z,hu,hz⟩
    refine ⟨fun j i => z (j,i),hu,?_⟩
    intro v
    rw [← actual_vertex k σ β hcoord y (fun j i => z (j,i)) v]
    exact hz v

end Equation47
end NikolovSegal
