/- GID: D5/S3/FiniteGroups/NikolovSegal/Proposition102Assembly
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Proposition102Assembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional chosen-length centreless assembly from literal scalar and twisted PRODUCT inputs. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47Classification

set_option autoImplicit false

/-! Centerless chosen-length Proposition10.2 reduction, Part I pp228--232.
The real quantitative geometry, normalization, extraction and both coordinate
reconstructions are proved. ONLY the precise scalar/twisted PRODUCT inputs
remain hypotheses. Their uniform finite-simple existence is not asserted. -/
namespace NikolovSegal
open Equation47 Equation47TypeII Equation47WordCoupling
universe u

private theorem coordinate_product {S I : Type u} [Group S] {m : ℕ}
    (f : Fin m → I → S) (v : I) :
    (orderedProduct f) v = orderedProduct (fun j => f j v) := by
  simpa [orderedProduct,List.map_ofFn,Function.comp_def] using
    map_list_prod (Pi.evalMonoidHom (fun _ : I => S) v) (List.ofFn f)

/-- Genuine conditional Proposition10.2 assembly. The SAME global correction
is chosen from the real Hall-selected good cycles before all tuple targets.
Powered components are classified by actual movement, light representatives
are derived by averaging, and heavy components use constructed D crossings.
There is no coverage premise on a factor tuple or an eliminated residual. -/
theorem prescribed_coverage_from_published_products
    {S I : Type u} [Group S] [Fintype I] [DecidableEq I]
    {q M D m : ℕ} (hq : 0 < q) (hM : 0 < M)
    (hm : M * (4+2*D) * (q+(4+2*D)) ≤ m)
    (k : Fin m → MulAut (I → S)) (sigma : Fin m → Equiv.Perm I)
    (beta : Fin m → I → MulAut S)
    (hcoord : ∀ j z i, k j z (sigma j i) = beta j i (z i))
    (hscalar : ∀ b : Fin M → MulAut S, ∀ e : Fin M → ℕ, PartIIScalarProductInput q M b e)
    (htwisted : PartIITwistedProductInput S D) :
    PrescribedCommutatorCoverage (I → S) q m k := by
  classical
  let K := 4+2*D
  have hK : 0 < K := by dsimp [K]; omega
  let tau := fun j => sigma j ^ q
  have hgraph : qPowerGraph tau 1 = qPowerGraph sigma q := by
    ext v w
    simp only [tau,qPowerGraph,pow_one]
  obtain ⟨r,hr,hconst,hlight,hheavy⟩ := exists_quantitative_component_roots tau K hK
  let typeI := fun v => componentMovement tau r v < K * (componentVertices r v).card
  let R := {v : I // v = r v ∧ typeI v}
  letI : Fintype R := Fintype.ofFinite R
  let rep : R → I := Subtype.val
  let good := fun j x => tau j x = x
  have hperiod : ∀ j x, good j x → Function.IsPeriodicPt (sigma j) q x := by
    intro j x hx
    change (sigma j)^[q] x = x
    simpa only [good,tau,Equiv.Perm.coe_pow] using hx
  have hbad : ∀ a : R, (Finset.univ.filter (fun j : Fin m => ¬good j (rep a))).card < K := by
    intro a
    exact hlight a a.2.1 a.2.2
  obtain ⟨piece,Iset,hI,hinterval,hgood,y,hy⟩ := actual_selected_interval_with_support hq hK hM hm
    rep Subtype.val_injective good sigma hperiod hbad k beta hcoord
    (fun _ _ _ a => hscalar _ _)
  let sel : I → Finset (Fin m) := fun v => if h : v = r v ∧ typeI v then Iset ⟨v,h⟩ else ∅
  let J : I → Finset (Fin m) := fun v => if h : v = r v ∧ typeI v then
    prefixPiece good rep ⟨v,h⟩ (piece ⟨v,h⟩) else ∅
  have hsub : ∀ v, v = r v → typeI v → sel v ⊆ J v := by
    intro v hv ht
    simpa only [sel,J,dif_pos (show v = r v ∧ typeI v from ⟨hv,ht⟩)] using (hI ⟨v,hv,ht⟩).1
  have hne : ∀ v, v = r v → typeI v → (J v).Nonempty := by
    intro v hv ht
    have hi : (Iset ⟨v,hv,ht⟩).Nonempty := Finset.card_pos.mp (by rw [(hI _).2]; exact hM)
    have hh := hi.mono (hI ⟨v,hv,ht⟩).1
    simpa only [J,dif_pos (show v = r v ∧ typeI v from ⟨hv,ht⟩)] using hh
  have hJ : ∀ v, v = r v → typeI v → ConsecutiveInterval (J v) := by
    intro v hv ht
    simpa only [J,dif_pos (show v = r v ∧ typeI v from ⟨hv,ht⟩)] using hinterval ⟨v,hv,ht⟩
  have hfix : ∀ v, v = r v → typeI v → ∀ j ∈ J v, (sigma j ^ q) v = v := by
    intro v hv ht j hj
    have hj' : j ∈ prefixPiece good rep ⟨v,hv,ht⟩ (piece ⟨v,hv,ht⟩) := by
      simpa only [J,dif_pos (show v = r v ∧ typeI v from ⟨hv,ht⟩)] using hj
    exact hgood ⟨v,hv,ht⟩ j hj'
  have hrootScalar : ∀ v, v = r v → typeI v → ∀ t : S, ∃ x : Fin m → S,
      (∀ j, j ∉ sel v → x j = 1) ∧
      orderedProduct (fun j => (x j)⁻¹ * correctedCycleComponent beta sigma y j v q (x j)) = t := by
    intro v hv ht t
    obtain ⟨c,hc,hs⟩ := hy ⟨v,hv,ht⟩ t
    have hout : ∀ j, j ∉ sel v → c j = 1 := by
      intro j hj
      funext i
      apply hs j i
      left
      simpa only [sel,dif_pos (show v = r v ∧ typeI v from ⟨hv,ht⟩)] using hj
    refine ⟨fun j => c j v,fun j hj => congrFun (hout j hj) v,?_⟩
    have hc' : orderedProduct (fun j => (c j v)⁻¹ *
        (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) = t := by
      have hh := congrFun hc v
      rw [coordinate_product] at hh
      simpa only [rep,Subtype.coe_mk,if_pos rfl,ite_true] using hh
    have hterms : (fun j => (c j v)⁻¹ * correctedCycleComponent beta sigma y j v q (c j v)) =
        (fun j => (c j v)⁻¹ * (((k j * MulAut.conj (y j)⁻¹)^q) (c j)) v) := by
      funext j
      by_cases hj : j ∈ sel v
      · have hjfix := hfix v hv ht j (hsub v hv ht hj)
        have hcomponent := actual_corrected_q_power_coordinate k sigma beta hcoord y j v q (c j)
        simpa only [Equiv.Perm.coe_pow,hjfix] using congrArg (fun s => (c j v)⁻¹ * s) hcomponent.symm
      · have hcv : c j v = 1 := congrFun (hout j hj) v
        simp only [hcv,hout j hj,Pi.one_apply,map_one,inv_one,one_mul]
    exact (congrArg orderedProduct hterms).trans hc'
  have hn : ∀ v, v = r v → ¬typeI v → 2 ≤ (Finset.univ.filter (fun w : I => r w = v)).card := by
    exact hheavy
  have htype : ∀ v, v = r v → ¬typeI v →
      (4+2*D) * (Finset.univ.filter (fun w : I => r w = v)).card ≤
        ∑ j : Fin m, (Finset.univ.filter (fun w : I => r w = v ∧ (sigma j ^ q) w ≠ w)).card := by
    intro v hv ht
    exact Nat.le_of_not_gt ht
  refine ⟨y,?_⟩
  intro target
  obtain ⟨c,hc⟩ := actual_mixed_components_reconstruction k sigma beta hcoord y r typeI
    (by simpa only [hgraph] using hr) (by simpa only [hgraph] using hconst)
    sel J hsub hne hJ hfix hrootScalar hn htype htwisted target
  refine ⟨c,?_⟩
  funext v
  rw [coordinate_product]
  exact hc v

/-- Exact uniform quantifiers for the two genuinely unproved published
finite-simple PRODUCT kernels. This implication assembles the literal
supplier; it does not prove either quantified premise or assert an official
solution. D and M(q), C(q) precede every group and automorphism/divisor tuple. -/
theorem uniform_transitive_supplier_of_published_products
    (twisted : ∃ D : ℕ, 0 < D ∧ ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      ¬IsMulCommutative S → PartIITwistedProductInput S D)
    (scalar : ∀ q : ℕ, 0 < q → ∃ M C : ℕ, 0 < M ∧
      ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
        ¬IsMulCommutative S → C < Nat.card S →
        ∀ b : Fin M → MulAut S, ∀ e : Fin M → ℕ, PartIIScalarProductInput q M b e) :
    UniformTransitiveSimpleCommutatorSupplier.{u} := by
  intro q hq
  obtain ⟨D,hDpos,hD⟩ := twisted
  obtain ⟨M,C,hM,hscalar⟩ := scalar q hq
  let K := 4+2*D
  let m := M*K*(q+K)
  refine ⟨m,C,by dsimp [m,K]; positivity,?_⟩
  intro S _ _ _ hnS hcard I _ _ k sigma beta hcoord htrans
  classical
  letI : Fintype I := Fintype.ofFinite I
  exact prescribed_coverage_from_published_products hq hM (by rfl) k sigma beta hcoord
    (hscalar S hnS hcard) (hD S hnS)

end NikolovSegal
