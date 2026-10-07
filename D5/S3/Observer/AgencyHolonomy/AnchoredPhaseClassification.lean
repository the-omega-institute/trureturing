/- GID: D5/S3/Observer/AgencyHolonomy/AnchoredPhaseClassification
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/AnchoredPhaseClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete anchored Circle phase classification and independent realization. -/

import D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport
import D5.S3.Factorization.Galois.SparseCharacterSynchronization
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.AnchoredPhaseClassification

open D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport
open scoped Topology

universe u v

attribute [local instance] Classical.propDecidable

variable {V : Type u} {E : Type v} {s t : E → V} {T : Set E}

/-- The original indexed product of non-tree and non-root reference coordinates. -/
@[reducible] def Coordinates (T : Set E) (R : Set V) (r : V) :=
  ({e : E // e ∉ T} → Circle) × ({a : V // a ∈ R ∧ a ≠ r} → Circle)

/-- Exactly the vertex functions fixing every reference. -/
def anchoredGroup (R : Set V) : Subgroup (V → Circle) where
  carrier := {g | ∀ a ∈ R, g a = 1}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh a ha; simp [hg a ha, hh a ha]
  inv_mem' := by intro g hg a ha; simp [hg a ha]

/-- The anchored vertex group maps into edge fields by its coboundary. -/
noncomputable def coboundary (s t : E → V) (R : Set V) :
    anchoredGroup R →* (E → Circle) where
  toFun := fun g e => g.1 (t e) * (g.1 (s e))⁻¹
  map_one' := by ext e; simp
  map_mul' := by intros; ext e; simp [mul_comm, mul_left_comm, mul_assoc]

/-- Basic loop phases and the actual root-to-reference tree phases. -/
noncomputable def coordinates (ht : NamedSpanningTree s t T) (R : Set V) (r : V)
    (u : E → Circle) : Coordinates T R r :=
  (fun e => rootPhase ht r u (s e) * u e * (rootPhase ht r u (t e))⁻¹,
   fun a => rootPhase ht r u a)

/-- The continuous homomorphism evaluates exactly the actual phase coordinates. -/
noncomputable def coordinateHom (ht : NamedSpanningTree s t T) (R : Set V) (r : V) :
    (E → Circle) →ₜ* Coordinates T R r := by
  let hc := (selected_tree_transport ht r).2.2.2.1
  let hm := (selected_tree_transport ht r).2.2.2.2.1
  let ho := (selected_tree_transport ht r).2.2.2.2.2
  exact {
    toFun := coordinates ht R r
    map_one' := by
      apply Prod.ext <;> funext i <;> simp [coordinates, ho]
    map_mul' := by
      intro u w
      apply Prod.ext <;> funext i <;>
        simp [coordinates, hm, mul_comm, mul_left_comm, mul_assoc]
    continuous_toFun := by
      apply Continuous.prodMk
      · exact continuous_pi fun e => ((hc (s e)).mul (continuous_apply e.1)).mul
          ((hc (t e)).inv)
      · exact continuous_pi fun a => hc a }

/-- Extend the reference coordinates by one at the root and at all nonreferences. -/
noncomputable def sectionPotential (R : Set V) (r : V) (z : Coordinates T R r)
    (a : V) : Circle := by
  classical
  exact if h : a ∈ R ∧ a ≠ r then z.2 ⟨a,h⟩ else 1

/-- Extend the non-tree phases by one on precisely the selected tree. -/
noncomputable def sectionLoops (T : Set E) (R : Set V) (r : V)
    (z : Coordinates T R r) (e : E) : Circle := by
  classical
  exact if h : e ∈ T then 1 else z.1 ⟨e,h⟩

/-- One same original edge field realizes the entire coordinate tuple. -/
noncomputable def phaseSection (s t : E → V) (T : Set E) (R : Set V) (r : V)
    (z : Coordinates T R r) : E → Circle :=
  gauge s t (sectionPotential R r z) (sectionLoops T R r z)

/-- Full anchored classification on every finite named multigraph and every selected
spanning tree. The quotient is by the coboundary image, with its quotient group topology. -/
theorem anchored_phase_classification [Fintype V] [Fintype E]
    (ht : NamedSpanningTree s t T) (R : Set V) (r : V) (hr : r ∈ R) :
    let chi := coordinateHom ht R r
    let sigma := phaseSection s t T R r
    let N := (coboundary s t R).range
    let c := Fintype.card {e : E // e ∉ T}
    let a := Fintype.card {x : V // x ∈ R ∧ x ≠ r}
    let n := Fintype.card V
    let m := Fintype.card E
    let k := Fintype.card R
    (∀ g : anchoredGroup R, ∀ u : E → Circle, chi (gauge s t g.1 u) = chi u) ∧
    (∀ u w : E → Circle, chi u = chi w ↔
      ∃ g : anchoredGroup R, gauge s t g.1 u = w) ∧
    Function.RightInverse sigma chi ∧ Continuous sigma ∧
    (∀ z z' : Coordinates T R r, sigma (z * z') = sigma z * sigma z') ∧
    chi.toMonoidHom.ker = N ∧
    (∀ u w : E → Circle,
      (QuotientGroup.mk u : (E → Circle) ⧸ N) = QuotientGroup.mk w ↔
        ∃ g : anchoredGroup R, gauge s t g.1 u = w) ∧
    (∃ q : ((E → Circle) ⧸ N) ≃ₜ* Coordinates T R r,
      (∀ u, q (QuotientGroup.mk u) = chi u) ∧
      (∀ z, q.symm z = QuotientGroup.mk (sigma z))) ∧
    CompactSpace ((E → Circle) ⧸ N) ∧ T2Space ((E → Circle) ⧸ N) ∧
    IsTopologicalGroup ((E → Circle) ⧸ N) ∧ IsClosed (N : Set (E → Circle)) ∧
    Fintype.card T + 1 = n ∧ c + Fintype.card T = m ∧ a + 1 = k ∧
    c + a + n = m + k ∧ c + a = m + k - n ∧
    c = m + 1 - n ∧ c + a = c + k - 1 ∧
    Nonempty (Coordinates T R r ≃ₜ* (Fin (m + k - n) → Circle)) := by
  classical
  dsimp only
  rcases selected_tree_transport ht r with ⟨hroot, hedge, hcov, hcont, hmul, hone⟩
  let chi := coordinateHom ht R r
  let sigma := phaseSection s t T R r
  have chi_val (u : E → Circle) : chi u = coordinates ht R r u := rfl
  have invariant (g : anchoredGroup R) (u : E → Circle) :
      chi (gauge s t g.1 u) = chi u := by
    have gr := g.property r hr
    change coordinates ht R r (gauge s t g.1 u) = coordinates ht R r u
    apply Prod.ext
    · funext e
      simp [coordinates, hcov, gr, gauge,
        mul_comm, mul_left_comm, mul_assoc]
    · funext a
      simp [coordinates, hcov, gr, g.property a a.property.1]
  have fibers (u w : E → Circle) : chi u = chi w ↔
      ∃ g : anchoredGroup R, gauge s t g.1 u = w := by
    constructor
    · intro heq
      let g : V → Circle := fun v => rootPhase ht r w v * (rootPhase ht r u v)⁻¹
      have hg : g ∈ anchoredGroup R := by
        intro v hv
        by_cases hvr : v = r
        · subst v; simp [g, hroot]
        · have he := congrFun (congrArg Prod.snd heq) ⟨v,hv,hvr⟩
          change rootPhase ht r u v = rootPhase ht r w v at he
          simp [g, he]
      refine ⟨⟨g,hg⟩, ?_⟩
      funext e
      have hn : rootPhase ht r u (s e) * u e * (rootPhase ht r u (t e))⁻¹ =
          rootPhase ht r w (s e) * w e * (rootPhase ht r w (t e))⁻¹ := by
        by_cases he : e ∈ T
        · simp [hedge e he, mul_comm, mul_left_comm, mul_assoc]
        · exact congrFun (congrArg Prod.fst heq) ⟨e,he⟩
      calc
        gauge s t g u e = rootPhase ht r w (t e) *
            (rootPhase ht r u (s e) * u e * (rootPhase ht r u (t e))⁻¹) *
              (rootPhase ht r w (s e))⁻¹ := by
          simp [gauge, g, mul_comm, mul_left_comm, mul_assoc]
        _ = w e := by rw [hn]; simp [mul_comm, mul_left_comm, mul_assoc]
    · rintro ⟨g,rfl⟩; exact (invariant g u).symm
  have realization (z : Coordinates T R r) : chi (sigma z) = z := by
    have hbase (v : V) : rootPhase ht r (sectionLoops T R r z) v = 1 := by
      letI : Nontrivial Circle := ⟨⟨-(1 : Circle), 1, Circle.neg_ne_self 1⟩⟩
      let x : V → Additive Circle :=
        fun a => Additive.ofMul (rootPhase ht r (sectionLoops T R r z) a)
      have hx : x ∈
          (D5.S3.Factorization.Galois.SparseCharacterSynchronization.edgeDifference
            (treeSupport s t T) (Additive Circle)).ker := by
        rw [AddMonoidHom.mem_ker]
        funext p
        change x p.val.1 - x p.val.2 = 0
        apply sub_eq_zero.mpr
        have he : s(s (namedEdge p.property), t (namedEdge p.property)) =
            s(p.val.1, p.val.2) :=
          Classical.choose_spec (((SimpleGraph.fromEdgeSet_adj _).mp p.property).1)
        have hp : rootPhase ht r (sectionLoops T R r z) (t (namedEdge p.property)) =
            rootPhase ht r (sectionLoops T R r z) (s (namedEdge p.property)) := by
          simpa [sectionLoops, (namedEdge p.property).property] using
            hedge (namedEdge p.property) (namedEdge p.property).property
              (sectionLoops T R r z)
        change Additive.ofMul (rootPhase ht r (sectionLoops T R r z) p.val.1) =
          Additive.ofMul (rootPhase ht r (sectionLoops T R r z) p.val.2)
        apply congrArg Additive.ofMul
        rcases Sym2.eq_iff.mp he with ⟨hs, ht'⟩ | ⟨hs, ht'⟩
        · simpa only [hs, ht'] using hp.symm
        · simpa only [hs, ht'] using hp
      have hkernel :=
        (D5.S3.Factorization.Galois.SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff
          (treeSupport s t T) (Additive Circle)).mpr ht.isTree.connected.preconnected
      rw [hkernel] at hx
      obtain ⟨c, hc⟩ := hx
      have hv := congrArg (fun a : Additive Circle => a.toMul)
        ((congrFun hc v).symm.trans (congrFun hc r))
      change rootPhase ht r (sectionLoops T R r z) v =
        rootPhase ht r (sectionLoops T R r z) r at hv
      exact hv.trans (hroot (sectionLoops T R r z))
    have hs (v : V) : rootPhase ht r (sigma z) v = sectionPotential R r z v := by
      change rootPhase ht r (gauge s t (sectionPotential R r z) (sectionLoops T R r z)) v = _
      rw [hcov, hbase]
      simp [sectionPotential]
    change coordinates ht R r (sigma z) = z
    apply Prod.ext
    · funext e
      change rootPhase ht r (sigma z) (s e) * sigma z e *
        (rootPhase ht r (sigma z) (t e))⁻¹ = z.1 e
      rw [hs, hs]
      simp [sigma, phaseSection, gauge,
        sectionLoops, e.property, mul_comm, mul_left_comm]
    · funext v
      change rootPhase ht r (sigma z) v = z.2 v
      rw [hs]; simp [sectionPotential, v.property]
  have sigma_cont : Continuous sigma := by
    apply continuous_pi
    intro e
    change Continuous (fun z : Coordinates T R r =>
      sectionPotential R r z (t e) * sectionLoops T R r z e *
        (sectionPotential R r z (s e))⁻¹)
    unfold sectionPotential sectionLoops
    split_ifs <;> fun_prop
  have sigma_mul (z w : Coordinates T R r) : sigma (z*w) = sigma z * sigma w := by
    funext e
    change gauge s t (sectionPotential R r (z*w)) (sectionLoops T R r (z*w)) e =
      gauge s t (sectionPotential R r z) (sectionLoops T R r z) e *
      gauge s t (sectionPotential R r w) (sectionLoops T R r w) e
    simp only [gauge, sectionPotential, sectionLoops]
    split_ifs <;> simp [mul_comm, mul_left_comm, mul_assoc]
  have kernel : chi.toMonoidHom.ker = (coboundary s t R).range := by
    ext u
    change chi u = 1 ↔ ∃ g : anchoredGroup R, coboundary s t R g = u
    have ho : chi (1 : E → Circle) = 1 := map_one chi
    rw [← ho, fibers]
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨g⁻¹, ?_⟩
      funext e
      have h := congrFun hg e
      change g.1 (t e) * u e * (g.1 (s e))⁻¹ = 1 at h
      simp only [coboundary, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_inv,
        Pi.inv_apply, inv_inv]
      calc
        _ = (g.1 (t e))⁻¹ * (g.1 (t e) * u e * (g.1 (s e))⁻¹) *
            g.1 (s e) := by rw [h]; simp
        _ = u e := by simp [mul_assoc]
    · rintro ⟨g,rfl⟩
      refine ⟨g⁻¹, ?_⟩
      funext e; simp [gauge, coboundary, mul_comm, mul_assoc]
  have cosets (u w : E → Circle) :
      (QuotientGroup.mk u : (E → Circle) ⧸ (coboundary s t R).range) =
        QuotientGroup.mk w ↔ ∃ g : anchoredGroup R, gauge s t g.1 u = w := by
    rw [← kernel, QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv]
    rw [inv_mul_eq_one]
    change chi u = chi w ↔ _
    exact fibers u w
  have quotient_iso : ∃ q : ((E → Circle) ⧸ (coboundary s t R).range) ≃ₜ*
      Coordinates T R r,
      (∀ u, q (QuotientGroup.mk u) = chi u) ∧
      (∀ z, q.symm z = QuotientGroup.mk (sigma z)) := by
    rw [← kernel]
    let q := QuotientGroup.quotientKerEquivOfRightInverse chi.toMonoidHom sigma realization
    let qc : ((E → Circle) ⧸ chi.toMonoidHom.ker) ≃ₜ* Coordinates T R r := {
      q with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr chi.continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp sigma_cont }
    exact ⟨qc, fun _ => rfl, fun _ => rfl⟩
  have quotient_t2 : T2Space ((E → Circle) ⧸ (coboundary s t R).range) :=
    quotient_iso.choose.toHomeomorph.symm.t2Space
  have closed_image : IsClosed ((coboundary s t R).range : Set (E → Circle)) := by
    rw [← kernel]
    change IsClosed (chi ⁻¹' {1})
    exact isClosed_singleton.preimage chi.continuous
  have tree_count : Fintype.card T + 1 = Fintype.card V := by
    have hset : (treeSupport s t T).edgeSet = Set.range (fun e : T => s(s e,t e)) := by
      rw [treeSupport, SimpleGraph.edgeSet_fromEdgeSet]
      ext p
      constructor
      · exact fun h => h.1
      · rintro ⟨e,rfl⟩
        exact ⟨⟨e,rfl⟩, by simpa [Sym2.mk_isDiag_iff] using ht.nonloop e e.property⟩
    have he : Fintype.card T = Fintype.card (treeSupport s t T).edgeSet := by
      exact Fintype.card_congr
        ((Equiv.ofInjective _ ht.distinct).trans (Equiv.setCongr hset).symm)
    rw [he, ← SimpleGraph.edgeFinset_card]
    exact ht.isTree.card_edgeFinset
  have edge_count : Fintype.card {e : E // e ∉ T} + Fintype.card T = Fintype.card E := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  have anchor_count : Fintype.card {a : V // a ∈ R ∧ a ≠ r} + 1 = Fintype.card R := by
    let er : {a : V // a ∈ R ∧ a ≠ r} ≃ {a : R // a.1 ≠ r} := {
      toFun := fun a => ⟨⟨a.1,a.2.1⟩,a.2.2⟩
      invFun := fun a => ⟨a.1.1,a.1.2,a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Fintype.card_congr er]
    have ee : {a : R // a.1 = r} ≃ PUnit.{1} := {
      toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨⟨r,hr⟩,rfl⟩
      left_inv := by intro a; apply Subtype.ext; apply Subtype.ext; exact a.property.symm
      right_inv := by intro a; cases a; rfl }
    have hc := Fintype.card_congr ee
    have hle := Fintype.card_subtype_le (fun a : R => a.1 = r)
    rw [Fintype.card_subtype_compl]; simp only [Fintype.card_punit] at hc
    omega
  have dimension : Fintype.card {e : E // e ∉ T} +
      Fintype.card {a : V // a ∈ R ∧ a ≠ r} = Fintype.card E + Fintype.card R -
        Fintype.card V := by omega
  have reindex : Nonempty (Coordinates T R r ≃ₜ*
      (Fin (Fintype.card E + Fintype.card R - Fintype.card V) → Circle)) := by
    let I := {e : E // e ∉ T} ⊕ {a : V // a ∈ R ∧ a ≠ r}
    let ei : I ≃ Fin (Fintype.card E + Fintype.card R - Fintype.card V) :=
      Fintype.equivFinOfCardEq (by simpa [I, Fintype.card_sum] using dimension)
    let ec : Coordinates T R r ≃ (I → Circle) :=
      (Equiv.sumArrowEquivProdArrow _ _ _).symm
    let ef := ec.trans (Equiv.arrowCongr ei (Equiv.refl Circle))
    exact ⟨{
      ef with
      map_mul' := by intro z w; funext i; simp [ef, ec, Equiv.arrowCongr]; cases ei.symm i <;> rfl
      continuous_toFun := by
        apply continuous_pi
        intro i
        cases hi : ei.symm i with
        | inl j =>
          change Continuous (fun z : Coordinates T R r => ec z (ei.symm i))
          rw [hi]; exact (continuous_apply j).comp continuous_fst
        | inr j =>
          change Continuous (fun z : Coordinates T R r => ec z (ei.symm i))
          rw [hi]; exact (continuous_apply j).comp continuous_snd
      continuous_invFun := by
        apply Continuous.prodMk <;> apply continuous_pi <;> intro i <;>
          simp only [ne_eq, Equiv.arrowCongr_symm, Equiv.refl_symm, Function.comp_apply,
            Equiv.arrowCongr_apply, Equiv.coe_refl, Equiv.symm_symm, id_eq] <;> fun_prop }⟩
  refine ⟨invariant, fibers, realization, sigma_cont, sigma_mul, kernel, cosets,
    quotient_iso, inferInstance, quotient_t2, inferInstance, closed_image, tree_count,
    edge_count, anchor_count, ?_, dimension, ?_, ?_, reindex⟩
  all_goals omega

#print axioms anchored_phase_classification

end D5.S3.Observer.AgencyHolonomy.AnchoredPhaseClassification
