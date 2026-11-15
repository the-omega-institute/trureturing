/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact SF and the connected/disconnected beta dichotomy for Heawood double lifts. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodActions
import D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
import D5.S3.Combinatorics.Graph.StarForming.CoverDensity

/-! The whole two-sheet theorem of HEAWOOD_DOUBLE_COVER_GAIN, at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The binary and cyclic labels are related by an explicit graph
isomorphism. Original six fifteen-sets are transported as actual selections. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
open StarFormingDissociationRefutation HeawoodSwitching HeawoodLift

private def cyclicMap : Fin 14 → Fin 14 := ![0,1,3,4,6,2,5,12,10,7,8,11,9,13]
private def cyclicInv : Fin 14 → Fin 14 := ![0,1,5,2,3,6,4,9,10,12,8,11,7,13]

/-- Explicitly distinguish the original cyclic labels from binary Fano labels. -/
def cyclicIso : HeawoodParameters.graph ≃g base where
  toFun := cyclicMap
  invFun := cyclicInv
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_rel_iff' := by decide +kernel

private theorem base_parameters : beta base 2=7 ∧ SF base 2=8 := by
  have h := Isomorphism.parameters cyclicIso
  rw [HeawoodParameters.beta_graph,HeawoodParameters.sf_graph] at h
  exact ⟨h.1.symm,h.2.symm⟩

theorem base_regular : ∀ v, DegreeCapacity.degree base v=3 := by decide +kernel
private theorem base_triangle_free : CoverPullback.TriangleFree base.Adj := by
  unfold CoverPullback.TriangleFree
  decide +kernel

private theorem fibers : ∀ v : Fin 14,
    (Finset.univ.filter (fun w : Fin 14 × F2 => w.1=v)).card=2 := by decide +kernel

/-- Every signing, including the zero class, has SF exactly sixteen. -/
theorem sf_all (s : Signing) : SF (graph s) 2=16 := by
  classical
  have hs (S : Finset (Fin 14)) (hm : IsMinimalStarForming base 2 S) :
      CoverPullback.HasSafeCertificates base.Adj (· ∈ S) := by
    apply CoverPullback.safe_certificates_of_boundary_triangle_free
      ((regular_minimal_iff base S).mpr hm)
    intro o a b _ _ _ hoa hob hab
    exact base_triangle_free o a b hoa hab (base.adj_symm hob)
  have hl := sf_mul_le_of_safe base (graph s) Prod.fst (BinaryLift.cover base (voltage s)) 2
    fibers hs
  rw [base_parameters.2] at hl
  have hr : ∀ v, DegreeCapacity.degree (graph s) v=3 := fun v =>
    (CoverDensity.degree_cover base (graph s) Prod.fst (BinaryLift.cover base (voltage s)) v).trans
      (base_regular v.1)
  have hu := DegreeCapacity.sf_regular_bound (graph s) 3 (by decide) hr
  norm_num [Fintype.card_prod,ZMod.card] at hu
  omega

def pack : (Fin 14 × F2) ≃ Fin 28 :=
  ((Equiv.refl (Fin 14)).prodCongr (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

private theorem six_adjacency : ∀ k : Fin 6, ∀ x y : Fin 14 × F2,
    HeawoodCertificates.adjacency (HeawoodCertificates.sixTwists k) (pack x) (pack y) ↔
      (base.Adj x.1 y.1 ∧ x.2+y.2=HeawoodActions.representative k (edgeIndex x.1 y.1)) := by
  decide +kernel

/-- The six supplier graphs are exactly the six binary voltage graphs. -/
def sixIso (k : Fin 6) : graph (HeawoodActions.representative k) ≃g
    HeawoodCertificates.sixGraph k where
  toEquiv := pack
  map_rel_iff' := by intro x y; exact six_adjacency k x y

/-- Connected binary Heawood lifts have beta fifteen or sixteen. -/
theorem connected_beta (s : Signing) (hs : (graph s).Preconnected) :
    15 ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16 := by
  obtain ⟨k,⟨e⟩⟩ := HeawoodActions.six_isomorphism s ((HeawoodLift.preconnected_iff s).mp hs)
  have h := Isomorphism.parameters (e.trans (sixIso k))
  rw [h.1]
  exact HeawoodCertificates.six_beta_bounds k

private def zeroEquiv : (Fin 14 × F2) ≃ (Fin 14 ⊕ Fin 14) where
  toFun x := if x.2=0 then .inl x.1 else .inr x.1
  invFun x := match x with | .inl v => (v,0) | .inr v => (v,1)
  left_inv x := by
    rcases x with ⟨v,a⟩
    have hc : ∀ a : F2, a=0 ∨ a=1 := by decide +kernel
    rcases hc a with rfl | rfl <;> simp
  right_inv x := by cases x <;> simp

private def zeroIso : graph 0 ≃g (base ⊕g base) where
  toEquiv := zeroEquiv
  map_rel_iff' := by
    intro x y
    have hc : ∀ a : F2, a=0 ∨ a=1 := by decide +kernel
    have htwo : (1 : F2)+1=0 := by decide +kernel
    rcases hc x.2 with hx | hx <;> rcases hc y.2 with hy | hy <;>
      simp [zeroEquiv,BinaryLift.graph,voltage,hx,hy,htwo]

/-- A disconnected lift has exactly the dissociation maximum of two base copies. -/
theorem disconnected_beta (s : Signing) (hs : ¬ (graph s).Preconnected) :
    beta (graph s) 2=14 := by
  have hp : phi s=0 := by simpa only [HeawoodLift.preconnected_iff,not_not] using hs
  obtain ⟨e⟩ := isomorphic_of_phi_eq s 0 (by simpa using hp)
  have h := (Isomorphism.parameters (e.trans zeroIso)).1
  rw [beta_sum,base_parameters.1] at h
  exact h

/-- The complete two-sheet dichotomy uses actual connectedness and finite maxima. -/
theorem parameters (s : Signing) :
    SF (graph s) 2=16 ∧
    (beta (graph s) 2=14 ↔ ¬ (graph s).Preconnected) ∧
    ((graph s).Preconnected →
      (beta (graph s) 2=15 ∨ beta (graph s) 2=16) ∧ SF (graph s) 2-beta (graph s) 2≤1) := by
  classical
  refine ⟨sf_all s,⟨?_,disconnected_beta s⟩,?_⟩
  · intro hb hc
    have h := (connected_beta s hc).1
    omega
  · intro hc
    have hb := connected_beta s hc
    rw [sf_all]
    omega

end D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
