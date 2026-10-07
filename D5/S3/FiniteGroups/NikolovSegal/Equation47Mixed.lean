/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47Mixed
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47Mixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47TypeIIReconstruction
import D5.S3.FiniteGroups.NikolovSegal.Equation47TypeI

set_option autoImplicit false

/-! Part I Proposition10.2, the two cases of equation (47), on the actual
powered components. Type-II VALUE reconstruction is performed first, then
only the type-I witness variables are eliminated and their genuine selected
loop VALUES filled. The correction tuple y is fixed before every target. -/
namespace NikolovSegal.Equation47
open Equation47TypeII Equation47WordCoupling Equation47ValueNormalization
universe u
variable {S I : Type u} [Group S] [DecidableEq I] {m : ℕ}

private theorem root_apply (tau : Fin m → Equiv.Perm I) (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (j : Fin m) (v : I) : r (tau j v) = r v := by
  by_cases h : v = tau j v
  · exact congrArg r h.symm
  · exact (hconst v (tau j v) (show (qPowerGraph tau 1).Adj v (tau j v) from
      ⟨h,j,Or.inl (by simp)⟩).reachable).symm

private theorem vertex_local (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S) (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (a b : Arc m I → S) (v : I)
    (h : ∀ e, r e.2 = r v → a e = b e) : vertex tau alpha a v = vertex tau alpha b v := by
  unfold vertex
  congr 1
  funext j
  rw [h (j,v) rfl,h (j,(tau j).symm v) (by
    simpa only [Equiv.apply_symm_apply] using (root_apply tau r hconst j ((tau j).symm v)).symm)]

private theorem eliminate_preserves_region (tau : Fin m → Equiv.Perm I)
    (alpha : Fin m → I → MulAut S) (kappa : I → S) (r : I → I) (T : I → Prop)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (L : List (I × Arc m I)) (hL : LeafOrder tau L) (a : Arc m I → S)
    (ha : ∀ v, T (r v) → vertex tau alpha a v = kappa v) :
    ∀ e, T (r e.2) → eliminate tau alpha kappa L a e = a e := by
  classical
  induction L generalizing a with
  | nil => intros; rfl
  | cons p L ih =>
    have hp := hL.1 p (by simp)
    have htail : LeafOrder tau L := ⟨fun b hb => hL.1 b (by simp [hb]),hL.2.of_cons⟩
    have hsame : r p.2.2 = r p.1 := by
      rcases hp.2 with h | h
      · exact congrArg r h.symm
      · exact (root_apply tau r hconst p.2.1 p.2.2).symm.trans (congrArg r h.symm)
    let b := Function.update a p.2 (solve tau alpha a p kappa)
    have hba : ∀ e, T (r e.2) → b e = a e := by
      intro e he
      by_cases ht : T (r p.2.2)
      · have ht' : T (r p.1) := hsame ▸ ht
        have hs : solve tau alpha a p kappa = a p.2 := by
          apply (vertex_update_bijective tau alpha a p.2 p.1 hp.1 hp.2).1
          have hsolve : vertex tau alpha (Function.update a p.2 (solve tau alpha a p kappa)) p.1 = kappa p.1 := by
            simp only [solve,dif_pos hp]
            exact Classical.choose_spec ((vertex_update_bijective tau alpha a p.2 p.1 hp.1 hp.2).2 (kappa p.1))
          simpa only [Function.update_eq_self] using hsolve.trans (ha p.1 ht').symm
        simp only [b,hs,Function.update_eq_self]
      · apply Function.update_of_ne
        intro h
        exact ht (h ▸ he)
    have hb : ∀ v, T (r v) → vertex tau alpha b v = kappa v := by
      intro v hv
      rw [vertex_local tau alpha r hconst b a v (fun e he => hba e (he ▸ hv))]
      exact ha v hv
    intro e he
    exact (ih htail b hb e he).trans (hba e he)

private theorem simultaneous_loop_fill [Fintype I]
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (a : Arc m I → S) (K : I → Prop)
    (sel J : I → Finset (Fin m)) (kappa : I → S)
    (hsub : ∀ v, K v → sel v ⊆ J v)
    (hne : ∀ v, K v → (J v).Nonempty)
    (hJ : ∀ v, K v → ConsecutiveInterval (J v))
    (hfix : ∀ v, K v → ∀ j ∈ J v, tau j v = v)
    (ha : ∀ v, K v → ∀ j ∈ J v, a (j,v) = 1)
    (hscalar : ∀ v, K v → ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel v → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ * alpha j v (x j)) = t) :
    ∃ z : Arc m I → S, (∀ v, K v → vertex tau alpha z v = kappa v) ∧
      (∀ v, ¬ K v → vertex tau alpha z v = vertex tau alpha a v) := by
  classical
  let R := {v : I // K v}
  have hex : ∀ v : R, ∃ z : Arc m I → S, vertex tau alpha z v = kappa v ∧
      (∀ w : I, w ≠ v.val → vertex tau alpha z w = vertex tau alpha a w) ∧
      (∀ e, e.2 ≠ v.val ∨ e.1 ∉ sel v → z e = a e) := by
    intro v
    exact fill_typeI_root tau alpha a v (sel v) (J v) (hsub v v.2)
      (hne v v.2) (hJ v v.2) (hfix v v.2) (ha v v.2) (hscalar v v.2) (kappa v)
  let b : R → Arc m I → S := fun v => Classical.choose (hex v)
  have hb : ∀ v : R, vertex tau alpha (b v) v = kappa v ∧
      (∀ w : I, w ≠ v.val → vertex tau alpha (b v) w = vertex tau alpha a w) ∧
      (∀ e, e.2 ≠ v.val ∨ e.1 ∉ sel v → b v e = a e) :=
    fun v => Classical.choose_spec (hex v)
  let z : Arc m I → S := fun e => if h : K e.2 then b ⟨e.2,h⟩ e else a e
  have hz : ∀ e v, tau e.1 e.2 = v → e.2 ≠ v → z e = a e := by
    intro e v hv hne
    dsimp [z]
    split_ifs with h
    · apply (hb ⟨e.2,h⟩).2.2
      right
      intro hs
      exact hne ((hfix e.2 h e.1 (hsub e.2 h hs)).symm.trans hv)
    · rfl
  refine ⟨z,?_,?_⟩
  · intro v hv
    rw [← (hb ⟨v,hv⟩).1]
    unfold vertex
    congr 1
    funext j
    change (z (j,v))⁻¹ * alpha j ((tau j).symm v) (z (j,(tau j).symm v)) =
      (b ⟨v,hv⟩ (j,v))⁻¹ * alpha j ((tau j).symm v) (b ⟨v,hv⟩ (j,(tau j).symm v))
    have hneg : z (j,v) = b ⟨v,hv⟩ (j,v) := by simp only [z,dif_pos hv]
    rw [hneg]
    by_cases he : (tau j).symm v = v
    · rw [he,hneg]
    · rw [hz (j,(tau j).symm v) v (by simp) he,
        (hb ⟨v,hv⟩).2.2 (j,(tau j).symm v) (Or.inl he)]
  · intro v hv
    unfold vertex
    congr 1
    funext j
    have hneg : z (j,v) = a (j,v) := by simp only [z,dif_neg hv]
    rw [hneg]
    by_cases he : (tau j).symm v = v
    · rw [he,hneg]
    · rw [hz (j,(tau j).symm v) v (by simp) he]

/-- Genuine mixed reconstruction of (47). The only coverage hypotheses are
selected scalar PRODUCT coverage at type-I roots and the published twisted
PRODUCT input at the actual movement threshold. Neither branch assumes
whole-block/off-representative coverage. Opposite arcs retain independent
variables and automorphisms, and each powered component retains its root. -/
theorem actual_mixed_components_reconstruction [Fintype I] {q D : ℕ}
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (r : I → I) (typeI : I → Prop)
    (hr : ∀ v, (qPowerGraph sigma q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph sigma q).Reachable v w → r v = r w)
    (sel J : I → Finset (Fin m))
    (hsub : ∀ v, v = r v → typeI v → sel v ⊆ J v)
    (hne : ∀ v, v = r v → typeI v → (J v).Nonempty)
    (hJ : ∀ v, v = r v → typeI v → ConsecutiveInterval (J v))
    (hfix : ∀ v, v = r v → typeI v → ∀ j ∈ J v, (sigma j ^ q) v = v)
    (hscalar : ∀ v, v = r v → typeI v → ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel v → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ * correctedCycleComponent beta sigma y j v q (x j)) = t)
    (hn : ∀ v, v = r v → ¬ typeI v → 2 ≤ (Finset.univ.filter (fun w : I => r w = v)).card)
    (htype : ∀ v, v = r v → ¬ typeI v →
      (4+2*D) * (Finset.univ.filter (fun w : I => r w = v)).card ≤
      ∑ j : Fin m, (Finset.univ.filter (fun w : I => r w = v ∧ (sigma j ^ q) w ≠ w)).card)
    (htwisted : PartIITwistedProductInput S D) :
    ∀ kappa : I → S, ∃ c : Fin m → I → S, ∀ v,
      orderedProduct (fun j => (c j v)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v := by
  classical
  let tau := fun j => sigma j ^ q
  let alpha := fun j i => correctedCycleComponent beta sigma y j i q
  have hgraph : qPowerGraph tau 1 = qPowerGraph sigma q := by
    ext v w
    simp only [tau,qPowerGraph,pow_one]
  have hconst' : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w := by
    simpa only [hgraph] using hconst
  obtain ⟨F,L,hF,hacyc,hreach,hL,hroots,hedges⟩ := exists_actual_leafOrder sigma r hr hconst
  intro kappa
  obtain ⟨b,hbase,hb⟩ := actual_typeII_region_reconstruction k sigma beta hcoord y r
    (fun v => ¬ typeI v) hr hconst hn htype htwisted (fun _ _ => 1) kappa
  let a0 : Arc m I → S := fun e => if typeI (r e.2) then 1 else b e.1 e.2
  have ha0 : ∀ v, ¬ typeI (r v) → vertex tau alpha a0 v = kappa v := by
    intro v hv
    rw [vertex_local tau alpha r hconst' a0 (fun e => b e.1 e.2) v (by
      intro e he
      simp only [a0,he,if_neg hv]),actual_vertex k sigma beta hcoord y b v]
    exact hb v hv
  let a := eliminate tau alpha kappa L a0
  have haII : ∀ v, ¬ typeI (r v) → vertex tau alpha a v = kappa v := by
    intro v hv
    rw [vertex_local tau alpha r hconst' a a0 v (fun e he =>
      eliminate_preserves_region tau alpha kappa r (fun v => ¬ typeI v)
        hconst' L hL a0 ha0 e (he ▸ hv))]
    exact ha0 v hv
  let K := fun v => v = r v ∧ typeI v
  have haloops : ∀ v, K v → ∀ j ∈ J v, a (j,v) = 1 := by
    intro v hv j hj
    change eliminate tau alpha kappa L a0 (j,v) = 1
    rw [eliminate_loop tau alpha kappa L hL a0 (j,v) (hfix v hv.1 hv.2 j hj)]
    simp only [a0,← hv.1,if_pos hv.2]
  obtain ⟨z,hz,hother⟩ := simultaneous_loop_fill tau alpha a K sel J kappa
    (fun v hv => hsub v hv.1 hv.2) (fun v hv => hne v hv.1 hv.2)
    (fun v hv => hJ v hv.1 hv.2) (fun v hv => hfix v hv.1 hv.2)
    haloops (fun v hv => hscalar v hv.1 hv.2)
  refine ⟨fun j i => z (j,i),?_⟩
  intro v
  rw [← actual_vertex k sigma beta hcoord y (fun j i => z (j,i)) v]
  by_cases hv : K v
  · exact hz v hv
  · rw [hother v hv]
    by_cases hroot : v = r v
    · exact haII v (fun ht => hv ⟨hroot,hroot.symm ▸ ht⟩)
    · obtain ⟨p,hp,hpv⟩ := (hroots v).mpr hroot
      rw [← hpv]
      exact eliminate_solves tau alpha kappa L hL a0 p hp

end NikolovSegal.Equation47
