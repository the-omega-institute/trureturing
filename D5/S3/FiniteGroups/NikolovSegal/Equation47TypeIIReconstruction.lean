/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIReconstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47TypeIIReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ComponentBudget
import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueReconstruction
import D5.S3.FiniteGroups.NikolovSegal.CrossingKernelAPI

set_option autoImplicit false

/-! Actual Part I Proposition9.1 reconstruction after value normalization,
all forest links, the proved component colour/support bounds, and literal
Proposition8.4 extraction. The ONLY group-coverage input is the precise
PartII1.1/PartI1.9 scalar twisted PRODUCT theorem, explicitly unproved here.
-/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling Equation47Colours List
universe u
variable {S I : Type u} [Group S] [Fintype I] [DecidableEq I] {m D q : ℕ}

/-- Construct actual D-crossing certificates for the actual normalized
component residual from its genuine movement budget. No hextract premise. -/
theorem normalized_component_extraction
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root)
    (hn : 2 ≤ (Finset.univ.filter (fun v : I => r v = root)).card)
    (htype : (4+2*D) * (Finset.univ.filter (fun v : I => r v = root)).card ≤
      ∑ j : Fin m, (Finset.univ.filter (fun v : I => r v = root ∧ tau j v ≠ v)).card) :
    Nonempty (Extraction D (contractValueSystem kappa L
      (normalizedVertexWord tau alpha u) root)) := by
  let W := contractValueSystem kappa L (normalizedVertexWord tau alpha u) root
  let Y := valueResidualSupport tau L r root
  have hcount : ∀ e s, (signedVariables W).count (e,s) = if e ∈ Y then 1 else 0 := by
    intro e s
    simpa only [W,Y,valueResidualSupport,Finset.mem_filter,Finset.mem_univ,true_and] using
      normalized_value_residual_sign_count tau alpha u kappa L hL r hroots hconst root hroot e s
  have hcolour := normalized_component_residual_colour tau alpha u kappa L hL r hroots hconst root hroot
  have hbudget := normalized_component_typeII_residual_budget tau L hL r hroots hconst root hroot hn htype
  exact CrossingKernel.extraction_from_owner_counts Prod.fst _ D W Y (by intro e s; simpa only [List.count_eq_countP,_root_.beq_eq_decide] using hcount e s) hcolour (by
    change _ + 2*D ≤ (valueResidualSupport tau L r root).card
    omega)

/-- Consume the exact scalar twisted PRODUCT input after constructing all
crossings, with the actual target-dependent residual constants retained. -/
theorem normalized_component_typeII_solve
    (tau : Fin m → Equiv.Perm I) (alpha : Fin m → I → MulAut S)
    (u : ∀ j, ActualCycle (tau j) → S) (kappa : I → S)
    (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root)
    (hn : 2 ≤ (Finset.univ.filter (fun v : I => r v = root)).card)
    (htype : (4+2*D) * (Finset.univ.filter (fun v : I => r v = root)).card ≤
      ∑ j : Fin m, (Finset.univ.filter (fun v : I => r v = root ∧ tau j v ≠ v)).card)
    (hscalar : PartIITwistedProductInput S D) :
    ∃ z : Arc m I → S, wordValue (contractValueSystem kappa L
      (normalizedVertexWord tau alpha u) root) z = kappa root := by
  obtain ⟨P⟩ := normalized_component_extraction tau alpha u kappa L hL r hroots hconst root hroot hn htype
  exact solve_extracted_word P hscalar (fun _ => 1) (kappa root)

omit [Fintype I] in
private theorem value_congr_variables (W : List (Letter (Arc m I) S))
    (z a : Arc m I → S)
    (h : ∀ e g s, .var e g s ∈ W → z e = a e) : wordValue W z = wordValue W a := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    rw [show l::W = [l]++W from rfl,value_append,value_append,
      ih (fun e g s he => h e g s (by simp [he]))]
    congr 1
    cases l with
    | constant c => rfl
    | var e g s => rw [value_var,value_var,h e g s (by simp)]

/-- All true type-II powered components reconstruct simultaneously with
one SAME fixed pre-target y. Cycle scalar witnesses remain arbitrary; the
component assignments are joined on their disjoint actual variable support.
The published uniform finite-simple twisted input is the explicit gap. -/
theorem actual_typeII_region_reconstruction
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (r : I → I) (T : I → Prop)
    (hr : ∀ v, (qPowerGraph sigma q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph sigma q).Reachable v w → r v = r w)
    (hn : ∀ root, root = r root → T root → 2 ≤ (Finset.univ.filter (fun v : I => r v = root)).card)
    (htype : ∀ root, root = r root → T root →
      (4+2*D) * (Finset.univ.filter (fun v : I => r v = root)).card ≤
      ∑ j : Fin m, (Finset.univ.filter (fun v : I => r v = root ∧ (sigma j ^ q) v ≠ v)).card)
    (hscalar : PartIITwistedProductInput S D) :
    ∀ (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S),
      ∃ c : Fin m → I → S,
        (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
        ∀ v, T (r v) → orderedProduct (fun j => (c j v)⁻¹ *
          (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v := by
  classical
  let tau := fun j => sigma j ^ q
  let alpha := fun j i => correctedCycleComponent beta sigma y j i q
  have hgraph : qPowerGraph tau 1 = qPowerGraph sigma q := by
    ext v w
    simp only [tau,qPowerGraph,pow_one]
  have hconst' : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w := by
    simpa only [hgraph] using hconst
  obtain ⟨F,L,hF,hacyc,hreach,hL,hroots,hedges⟩ := exists_value_leafOrder tau r
    (by simpa only [hgraph] using hr) hconst'
  have hidem : ∀ v, r v = r (r v) := fun v => (hconst (r v) v (hr v)).symm
  intro u kappa
  let W := contractValueSystem kappa L (normalizedVertexWord tau alpha u)
  let R := {v : I // v = r v ∧ T v}
  have hsolve : ∀ v : R, ∃ z : Arc m I → S, wordValue (W v) z = kappa v := by
    intro v
    exact normalized_component_typeII_solve tau alpha u kappa L hL r hroots hconst'
      v v.2.1 (hn v v.2.1 v.2.2) (htype v v.2.1 v.2.2) hscalar
  let a : R → Arc m I → S := fun v => Classical.choose (hsolve v)
  let z : Arc m I → S := fun e => if h : T (r e.2) then a ⟨r e.2,hidem e.2,h⟩ e else 1
  have hz : ∀ root, root = r root → T root → wordValue (W root) z = kappa root := by
    intro root hroot hT
    rw [value_congr_variables (W root) z (a ⟨root,hroot,hT⟩) ?_]
    · exact Classical.choose_spec (hsolve ⟨root,hroot,hT⟩)
    · intro e g s he
      have hm : (e,s) ∈ signedVariables (W root) :=
        List.mem_filterMap.mpr ⟨.var e g s,he,rfl⟩
      have hc := List.count_pos_iff.mpr hm
      rw [normalized_value_residual_sign_count tau alpha u kappa L hL r hroots hconst' root hroot] at hc
      have hcomp : r e.2 = root := by
        split_ifs at hc with h
        · exact h.2.2
        · omega
      have hTe : T (r e.2) := hcomp ▸ hT
      have heq : (⟨r e.2,hidem e.2,hTe⟩ : R) = ⟨root,hroot,hT⟩ := Subtype.ext hcomp
      dsimp [z]
      rw [dif_pos hTe,heq]
  let b := extendValueSystem kappa L (normalizedVertexWord tau alpha u) z
  have hb : ∀ v, T (r v) → wordValue (normalizedVertexWord tau alpha u v) b = kappa v := by
    intro v hv
    by_cases hroot : v = r v
    · rw [← contractValueSystem_value]
      exact hz v hroot (hroot ▸ hv)
    · exact (normalized_value_forest_reconstruction tau alpha u kappa L hL r hroots).1 z |>.2.1 v hroot
  obtain ⟨c,hc,hx⟩ := (corrected_value_tuple_with_parameters_iff k sigma beta hcoord y
      (normalizedValues tau alpha u b) u).mpr (normalizedValues_cycle_constraints tau alpha u b)
  refine ⟨c,hc,?_⟩
  intro v hv
  rw [← hb v hv,normalizedVertexWord_value]
  congr 1
  funext j
  exact (hx j v).symm

/-- The all-type-II specialization retains every actual cycle-base witness.
The region theorem is also consumed by the mixed component reconstruction. -/
theorem actual_all_typeII_reconstruction
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (y : Fin m → I → S) (r : I → I)
    (hr : ∀ v, (qPowerGraph sigma q).Reachable (r v) v)
    (hconst : ∀ v w, (qPowerGraph sigma q).Reachable v w → r v = r w)
    (hn : ∀ root, root = r root → 2 ≤ (Finset.univ.filter (fun v : I => r v = root)).card)
    (htype : ∀ root, root = r root →
      (4+2*D) * (Finset.univ.filter (fun v : I => r v = root)).card ≤
      ∑ j : Fin m, (Finset.univ.filter (fun v : I => r v = root ∧ (sigma j ^ q) v ≠ v)).card)
    (hscalar : PartIITwistedProductInput S D) :
    ∀ (u : ∀ j, ActualCycle (sigma j ^ q) → S) (kappa : I → S),
      ∃ c : Fin m → I → S,
        (∀ j (C : ActualCycle (sigma j ^ q)), c j C.out = u j C) ∧
        ∀ v, orderedProduct (fun j => (c j v)⁻¹ *
          (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = kappa v := by
  intro u kappa
  obtain ⟨c,hc,hvalues⟩ := actual_typeII_region_reconstruction k sigma beta hcoord y r
    (fun _ => True) hr hconst (fun v hv _ => hn v hv) (fun v hv _ => htype v hv)
    hscalar u kappa
  exact ⟨c,hc,fun v => hvalues v trivial⟩

end NikolovSegal.Equation47ValueNormalization
