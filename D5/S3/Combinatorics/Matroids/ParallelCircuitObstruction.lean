/- GID: D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/ParallelCircuitObstruction
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Weighted joint restriction obstruction under parallel expansion. -/

module

public import D5.S3.Combinatorics.Matroids.ParallelCircuitCoordinates

/-! The obstruction of a block-ordered parallel expansion descends to its core. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.ParallelCircuitObstruction

open Finset
open Set (InjOn)
open scoped Matroid
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open CircuitCycleDecomposition (restrictionSign topCycles)
open CircuitPairInnerProduct (rationalAggregate castChain mem_rationalTopCycles_iff)
open JointCircuitGramCertificate (Circuit)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)
open RationalJointCircuitImage
open RationalTopCycleResidues (rational_cycle_residues_lift)
open ParallelCircuitCoordinates

set_option autoImplicit false

variable {V I : Type*} [Fintype V] [LinearOrder V] [Fintype I] [LinearOrder I]
variable {M : Matroid I} {p : V → I}

omit [Fintype V] [Fintype I] in
private lemma lift_image {s : I → V} (hs : Function.RightInverse s p) (F : Finset I) :
    (F.image s).image p = F := by
  rw [Finset.image_image, hs.id, Finset.image_id]

omit [Fintype V] [Fintype I] [LinearOrder I] in
private lemma lift_injOn {s : I → V} (hs : Function.RightInverse s p) (F : Finset I) :
    InjOn p (↑(F.image s) : Set V) := by
  rw [Finset.coe_image]
  rintro _ ⟨a, _, rfl⟩ _ ⟨b, _, rfl⟩ hab
  rw [hs a, hs b] at hab
  rw [hab]

omit [Fintype I] [LinearOrder I] in
private lemma residue_boundary (z : rationalIntegralReadoutCycles (M.comap p)) (R : Finset V) :
    ∑ x ∈ univ \ R, insertionSign R x • rationalResidue (z.val (insert x R)) = 0 := by
  simp only [← map_zsmul, ← map_sum, zsmul_eq_mul, z.prop.1.2 R, map_zero]

omit [Fintype V] [Fintype I] [LinearOrder I] in
private lemma residue_readout (z : Finset V → ℚ) (C T : Finset V)
    (hT : ((M.comap p) ／ (C : Set V)).IsBase (T : Set V)) :
    rationalResidue (rationalAggregate (M.comap p) C z T) =
      ∑ x ∈ C, restrictionSign C x T • rationalResidue (z (T ∪ C.erase x)) := by
  simp only [rationalAggregate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hT, map_sum,
    ← map_zsmul, zsmul_eq_mul]

omit [Fintype V] [LinearOrder V] [Fintype I] [LinearOrder I] in
private lemma pair_image (a b : V) (h : p a = p b) :
    p '' ({a, b} : Set V) = {p a} := by simp [h]

omit [Fintype V] [Fintype I] in
private lemma pair_base (hsurj : Function.Surjective p) {a b : V}
    (h : p a = p b) (hn : M.IsNonloop (p a))
    (R : Finset V) (hR : InjOn p (R : Set V)) (hout : p a ∉ R.image p)
    (hbase : (M.comap p).IsBase (↑(insert a R) : Set V)) :
    ((M.comap p) ／ ({a, b} : Set V)).IsBase (R : Set V) := by
  have hC : ({a, b} : Set V) ⊆ (M.comap p).E := by
    simp [Set.insert_subset_iff, ← h, hn.mem_ground]
  have hdis : Disjoint (p '' (R : Set V)) ({p a} : Set I) := by
    simpa [← Finset.coe_image] using hout
  have hb := ((isBase_comap_iff hsurj).mp hbase).1
  have hcore : M.IsBase (p '' (R : Set V) ∪ {p a}) := by
    simpa [Finset.coe_insert, Set.image_insert_eq, Set.union_singleton] using hb
  rw [comap_contract_isBase_iff hsurj hC, pair_image a b h,
    (Matroid.indep_singleton.mpr hn).contract_isBase_iff]
  exact ⟨⟨hcore, hdis⟩, hR⟩

omit [Fintype I] in
private lemma residues_constant (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a))
    (z : rationalIntegralReadoutCycles (M.comap p)) (B D : Finset V)
    (hB : (M.comap p).IsBase (B : Set V)) (hD : InjOn p (D : Set V))
    (himage : B.image p = D.image p) :
    rationalResidue (z.val B) = rationalResidue (z.val D) := by
  apply transversal_coeff_eq (fun F => rationalResidue (z.val F)) B D
    ((isBase_comap_iff hsurj).mp hB).2 hD himage
  intro a b R hab hR hout hnew
  by_cases heq : a = b
  · rw [heq]
  have ha : a ∉ R := fun ha => hout (mem_image_of_mem p ha)
  have hinj : InjOn p (↑(insert a R) : Set V) := by
    rw [Finset.coe_insert, Set.injOn_insert ha]
    exact ⟨hR, by simpa only [← Finset.coe_image, Finset.mem_coe] using hout⟩
  have hb : (M.comap p).IsBase (↑(insert a R) : Set V) := by
    refine (isBase_comap_iff hsurj).mpr ⟨?_, hinj⟩
    rw [← Finset.coe_image, hnew, ← himage, Finset.coe_image]
    exact ((isBase_comap_iff hsurj).mp hB).1
  have hC : (M.comap p).IsCircuit (↑({a, b} : Finset V) : Set V) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using parallel_pair a b (hn a) heq hab
  have hT : ((M.comap p) ／ (↑({a, b} : Finset V) : Set V)).IsBase (R : Set V) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      pair_base hsurj hab (hn a) R hR hout hb
  apply (signed_readout_of_parallel_pair horder heq hab R hR hout
    (fun F => rationalResidue (z.val F))).mp
  rw [← residue_readout z.val {a, b} R hT]
  exact z.prop.2 ⟨{a, b}, hC⟩ R

omit [Fintype I] in
private lemma pullback_residue (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a))
    {s : I → V} (hs : Function.RightInverse s p)
    (z : rationalIntegralReadoutCycles (M.comap p)) (F : Finset V) :
    pullbackChain p (fun G => rationalResidue (z.val (G.image s))) F =
      rationalResidue (z.val F) := by
  by_cases hF : (M.comap p).IsBase (F : Set V)
  · have hinj := ((isBase_comap_iff hsurj).mp hF).2
    rw [pullbackChain, ite_eq_left hinj]
    exact (residues_constant hsurj horder hn z F ((F.image p).image s) hF
      (lift_injOn hs _) (lift_image hs _).symm).symm
  · rw [z.prop.1.1 F hF, map_zero]
    by_cases hinj : InjOn p (F : Set V)
    · rw [pullbackChain, ite_eq_left hinj, z.prop.1.1, map_zero]
      intro hbase
      apply hF
      refine (isBase_comap_iff hsurj).mpr ⟨?_, hinj⟩
      rw [← Finset.coe_image, ← lift_image hs (F.image p), Finset.coe_image]
      exact ((isBase_comap_iff hsurj).mp hbase).1
    · rw [pullbackChain, ite_eq_right hinj]

/-- The augmented boundary with each insertion weighted by its fiber size. -/
def weightedBoundary (p : V → I) (f : Finset I → RationalResidue)
    (R : Finset I) : RationalResidue :=
  ∑ i ∈ univ \ R, insertionSign R i • ((univ.filter (fun x => p x = i)).card • f (insert i R))

/-- The signed deletion sum for a circuit and a contracted basis. -/
def circuitReadout (f : Finset I → RationalResidue) (C T : Finset I) :
    RationalResidue :=
  ∑ i ∈ C, restrictionSign C i T • f (T ∪ C.erase i)

/-- Residue chains on core bases with zero weighted boundary and zero signed
circuit readouts. The weight for each insertion is the size of its class. -/
def weightedCircuitResidues (M : Matroid I) (p : V → I) :
    Submodule ℤ (Finset I → RationalResidue) where
  carrier := {f | (∀ F : Finset I, ¬ M.IsBase (F : Set I) → f F = 0) ∧
    (∀ R, weightedBoundary p f R = 0) ∧
    ∀ (C : Circuit M) (T : Finset I), (M ／ (C.val : Set I)).IsBase (T : Set I) →
      circuitReadout f C.val T = 0}
  zero_mem' := by simp [weightedBoundary, circuitReadout]
  add_mem' := by
    intro f g hf hg
    refine ⟨fun F hF => by simp [hf.1 F hF, hg.1 F hF], fun R => ?_, fun C T hT => ?_⟩
    · change weightedBoundary p (f + g) R = 0
      have ha : weightedBoundary p f R = 0 := hf.2.1 R
      have hb : weightedBoundary p g R = 0 := hg.2.1 R
      unfold weightedBoundary at ha hb ⊢
      simp only [Pi.add_apply, smul_add, sum_add_distrib, ha, hb, add_zero]
    · change circuitReadout (f + g) C.val T = 0
      have ha : circuitReadout f C.val T = 0 := hf.2.2 C T hT
      have hb : circuitReadout g C.val T = 0 := hg.2.2 C T hT
      unfold circuitReadout at ha hb ⊢
      simp only [Pi.add_apply, smul_add, sum_add_distrib, ha, hb, add_zero]
  smul_mem' n f hf := by
    refine ⟨fun F hF => by simp [hf.1 F hF], fun R => ?_, fun C T hT => ?_⟩
    · change weightedBoundary p (n • f) R = 0
      unfold weightedBoundary
      simp only [Pi.smul_apply]
      simp_rw [smul_comm (_ : ℕ) n, smul_comm (insertionSign R _) n, ← smul_sum]
      exact (congrArg (n • ·) (hf.2.1 R)).trans (smul_zero _)
    · change circuitReadout (n • f) C.val T = 0
      unfold circuitReadout
      simp only [Pi.smul_apply]
      simp_rw [smul_comm (restrictionSign _ _ _) n, ← smul_sum]
      exact (congrArg (n • ·) (hf.2.2 C T hT)).trans (smul_zero _)

omit [Fintype V] [LinearOrder V] [Fintype I] in
private lemma image_disjoint {C T : Finset V}
    (hT : (M ／ (p '' (C : Set V))).IsBase (p '' (T : Set V))) :
    Disjoint (C.image p) (T.image p) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have ha' : a ∈ p '' (C : Set V) := by simpa only [← Finset.coe_image, Finset.mem_coe] using ha
  have hb' : a ∈ p '' (T : Set V) := by simpa only [← Finset.coe_image, Finset.mem_coe] using hb
  exact (hT.subset_ground hb').2 ha'

omit [Fintype V] [Fintype I] in
private lemma transversal_readout (horder : ∀ ⦃a b⦄, p a < p b → a < b)
    (f : Finset I → RationalResidue) (C T : Finset V)
    (hC : InjOn p (C : Set V)) (hT : InjOn p (T : Set V))
    (hd : Disjoint (C.image p) (T.image p)) :
    (∑ x ∈ C, restrictionSign C x T • pullbackChain p f (T ∪ C.erase x)) =
      circuitReadout f (C.image p) (T.image p) := by
  rw [circuitReadout, ← signed_readout_on_transversal horder C T hC hT hd f]
  apply sum_congr rfl
  intro x _
  have hinj : InjOn p (↑(T ∪ C.erase x) : Set V) := by
    rw [Finset.coe_union]
    have hsep : Disjoint (T : Set V) (↑(C.erase x) : Set V) := by
      apply Set.disjoint_left.mpr
      intro a ha hb
      exact Finset.disjoint_left.mp hd (mem_image_of_mem p (mem_of_mem_erase hb))
        (mem_image_of_mem p ha)
    refine (Set.injOn_union hsep).mpr
      ⟨hT, hC.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _)), ?_⟩
    intro a ha b hb heq
    have ha' := mem_image_of_mem p ha
    have hb' := mem_image_of_mem p (mem_of_mem_erase hb)
    exact (Finset.disjoint_left.mp hd hb' (heq ▸ ha')).elim
  rw [pullbackChain, ite_eq_left hinj]

private lemma sections_mem (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a))
    {s : I → V} (hs : Function.RightInverse s p)
    (z : rationalIntegralReadoutCycles (M.comap p)) :
    (fun G => rationalResidue (z.val (G.image s))) ∈ weightedCircuitResidues M p := by
  let f (G : Finset I) := rationalResidue (z.val (G.image s))
  have hres (F : Finset V) : pullbackChain p f F = rationalResidue (z.val F) :=
    pullback_residue hsurj horder hn hs z F
  refine ⟨fun F hF => ?_, fun R => ?_, fun C T hT => ?_⟩
  · apply (show rationalResidue (z.val (F.image s)) = 0 from ?_)
    rw [z.prop.1.1, map_zero]
    intro hbase
    apply hF
    simpa only [← Finset.coe_image, lift_image hs] using
      ((isBase_comap_iff hsurj).mp hbase).1
  · change weightedBoundary p f R = 0
    rw [← lift_image hs R, weightedBoundary,
      ← pullbackChain_boundary horder f (R.image s) (lift_injOn hs R)]
    simp only [hres, residue_boundary z]
  · let K := C.val.image s
    let U := T.image s
    have hKimage : K.image p = C.val := lift_image hs _
    have hUimage : U.image p = T := lift_image hs _
    have hC' : M.IsCircuit (p '' (K : Set V)) := by
      simpa only [← Finset.coe_image, hKimage] using C.prop
    have hK := comap_isCircuit_of_injOn (lift_injOn hs C.val) hC'
    have hT' : (M ／ (p '' (K : Set V))).IsBase (p '' (U : Set V)) := by
      simpa only [← Finset.coe_image, hKimage, hUimage] using hT
    have hU := (comap_contract_isBase_iff hsurj hK.subset_ground).mpr
      ⟨hT', lift_injOn hs T⟩
    change circuitReadout f C.val T = 0
    rw [← hKimage, ← hUimage,
      ← transversal_readout horder f K U (lift_injOn hs C.val) (lift_injOn hs T)
        (image_disjoint hT')]
    simp only [hres, ← residue_readout z.val K U hU]
    exact z.prop.2 ⟨K, hK⟩ U

private lemma lift_readouts (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a))
    (f : weightedCircuitResidues M p) :
    ∃ z : rationalIntegralReadoutCycles (M.comap p),
      ∀ F, rationalResidue (z.val F) = pullbackChain p f.val F := by
  have hsupp (F : Finset V) (hF : ¬ (M.comap p).IsBase (F : Set V)) :
      pullbackChain p f.val F = 0 := by
    by_cases hj : InjOn p (F : Set V)
    · rw [pullbackChain, ite_eq_left hj]
      apply f.prop.1
      intro h
      exact hF ((isBase_comap_iff hsurj).mpr ⟨by simpa only [Finset.coe_image] using h, hj⟩)
    · rw [pullbackChain, ite_eq_right hj]
  have hboundary (R : Finset V) :
      ∑ x ∈ univ \ R, insertionSign R x • pullbackChain p f.val (insert x R) = 0 := by
    by_cases hj : InjOn p (R : Set V)
    · rw [pullbackChain_boundary horder f.val R hj]
      exact f.prop.2.1 _
    · exact pullbackChain_boundary_of_not_injOn f.val R hj
  obtain ⟨q, hq⟩ := rational_cycle_residues_lift (M.comap p) _ hsupp hboundary
  refine ⟨⟨q.val, q.prop, fun C T => ?_⟩, hq⟩
  classical
  by_cases hT : ((M.comap p) ／ (C.val : Set V)).IsBase (T : Set V)
  · rw [residue_readout q.val C.val T hT]
    simp only [hq]
    obtain ⟨hcore, hTinj⟩ := (comap_contract_isBase_iff hsurj C.prop.subset_ground).mp hT
    rcases comap_circuit_cases C.prop hn with ⟨a, b, hab, heq, hpair⟩ | ⟨hCinj, hC⟩
    · have hCfin : C.val = {a, b} := Finset.coe_inj.mp (by simpa using hpair)
      have hout : p a ∉ T.image p := by
        rw [hpair, pair_image a b heq] at hcore
        intro h
        have hp : p a ∈ p '' (T : Set V) := by
          simpa only [← Finset.coe_image, Finset.mem_coe] using h
        exact (hcore.subset_ground hp).2 (Set.mem_singleton _)
      have hout' : p b ∉ T.image p := by rwa [← heq]
      have hinj (x : V) (hx : p x ∉ T.image p) : InjOn p (↑(insert x T) : Set V) := by
        have hxT : x ∉ T := fun h => hx (mem_image_of_mem p h)
        rw [Finset.coe_insert, Set.injOn_insert hxT]
        exact ⟨hTinj, by simpa only [← Finset.coe_image, Finset.mem_coe] using hx⟩
      rw [hCfin]
      apply (signed_readout_of_parallel_pair horder hab heq T hTinj hout
        (pullbackChain p f.val)).mpr
      rw [pullbackChain, ite_eq_left (hinj a hout), pullbackChain, ite_eq_left (hinj b hout'),
        Finset.image_insert, Finset.image_insert, heq]
    · rw [transversal_readout horder f.val C.val T hCinj hTinj (image_disjoint hcore)]
      have hC' : M.IsCircuit (↑(C.val.image p) : Set I) := by
        simpa only [Finset.coe_image] using hC
      exact f.prop.2.2 ⟨C.val.image p, hC'⟩ (T.image p)
        (by simpa only [Finset.coe_image] using hcore)
  · simp only [rationalAggregate, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hT, map_zero]

private noncomputable def sectionReadout (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a)) :
    rationalIntegralReadoutCycles (M.comap p) →ₗ[ℤ] weightedCircuitResidues M p where
  toFun z := ⟨fun F => rationalResidue (z.val (F.image (Function.surjInv hsurj))),
    sections_mem hsurj horder hn (Function.rightInverse_surjInv hsurj) z⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rationalResidue.map_add _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => rationalResidue.map_zsmul _ _)

private lemma sectionReadout_surj (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a)) :
    Function.Surjective (sectionReadout hsurj horder hn) := by
  intro f
  obtain ⟨z, hz⟩ := lift_readouts hsurj horder hn f
  refine ⟨z, Subtype.ext (funext fun F => ?_)⟩
  let s := Function.surjInv hsurj
  have hs : Function.RightInverse s p := Function.rightInverse_surjInv hsurj
  change rationalResidue (z.val (F.image s)) = f.val F
  rw [hz, pullbackChain, ite_eq_left (lift_injOn hs F), lift_image hs F]

private lemma sectionReadout_ker (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a)) :
    (sectionReadout hsurj horder hn).ker = (integralCycleInRational (M.comap p)).range := by
  ext z
  change sectionReadout hsurj horder hn z = 0 ↔
    z ∈ (integralCycleInRational (M.comap p)).range
  constructor
  · intro hz
    let f := (sectionReadout hsurj horder hn z).val
    have hzero : f = 0 := congrArg Subtype.val hz
    have hintegral (F : Finset V) : ∃ n : ℤ, (n : ℚ) = z.val F := by
      apply rationalResidue_eq_zero.mp
      rw [← pullback_residue hsurj horder hn (Function.rightInverse_surjInv hsurj) z F]
      change pullbackChain p f F = 0
      rw [hzero, pullbackChain]
      split <;> rfl
    choose x hx using hintegral
    have hx' : castChain x = z.val := funext hx
    let integral : topCycles (M.comap p) :=
      ⟨x, mem_rationalTopCycles_iff.mp (hx'.symm ▸ z.prop.1)⟩
    exact ⟨integral, Subtype.ext hx'⟩
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    funext F
    exact rationalResidue_eq_zero.mpr ⟨x.val _, rfl⟩

/-- Modulo integral cycles, the rational cycles with integral readouts are
exactly the core residue chains satisfying the weighted and circuit equations.
The comparison sends each transverse coefficient to its original residue. -/
theorem parallel_rational_residue_comparison (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a)) :
    ∃ comparison : (rationalIntegralReadoutCycles (M.comap p) ⧸
      (integralCycleInRational (M.comap p)).range) ≃ₗ[ℤ] weightedCircuitResidues M p,
      ∀ (z : rationalIntegralReadoutCycles (M.comap p)) (F : Finset V),
        pullbackChain p (comparison (Submodule.Quotient.mk z)).val F =
          rationalResidue (z.val F) := by
  let f := sectionReadout hsurj horder hn
  refine ⟨(Submodule.quotEquivOfEq _ _ (sectionReadout_ker hsurj horder hn).symm).trans
    (f.quotKerEquivOfSurjective (sectionReadout_surj hsurj horder hn)), ?_⟩
  intro z F
  change pullbackChain p (f z).val F = rationalResidue (z.val F)
  exact pullback_residue hsurj horder hn (Function.rightInverse_surjInv hsurj) z F

/-- Parallel expansion replaces the joint restriction obstruction by residue
chains on the core, with class-size weights only in the boundary equations.
On a saturated readout, its class is sent to the residues of its rational lift. -/
theorem parallel_lifting_obstruction [Nonempty V] (hsurj : Function.Surjective p)
    (horder : ∀ ⦃a b⦄, p a < p b → a < b) (hn : ∀ a, M.IsNonloop (p a)) :
    ∃ comparison : (JointSaturatedImage (M.comap p) ⧸ JointImageInSaturation (M.comap p)) ≃ₗ[ℤ]
      weightedCircuitResidues M p,
      ∀ (z : rationalIntegralReadoutCycles (M.comap p)) (y : JointSaturatedImage (M.comap p)),
        (∀ C T, ((y.val C).val T : ℚ) = rationalAggregate (M.comap p) C.val z.val T) →
        ∀ F, pullbackChain p (comparison (Submodule.Quotient.mk y)).val F =
          rationalResidue (z.val F) := by
  obtain ⟨e⟩ := ‹Nonempty V›
  have he : e ∈ (M.comap p).E := (hn e).mem_ground
  obtain ⟨readouts, hreadouts, hintegral, _⟩ := rationalJointRestriction_equiv (M.comap p) he
  have hmap :
      (integralCycleInRational (M.comap p)).range.map readouts.toLinearMap =
        JointImageInSaturation (M.comap p) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (hintegral x).symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨integralCycleInRational (M.comap p) x, ⟨x, rfl⟩,
        Subtype.ext ((hintegral x).trans hx)⟩
  let quotReadouts := Submodule.Quotient.equiv _ _ readouts hmap
  obtain ⟨comparison, hcomparison⟩ := parallel_rational_residue_comparison hsurj horder hn
  refine ⟨quotReadouts.symm.trans comparison, fun z y hy F => ?_⟩
  have hyz : y = readouts z := by
    apply Subtype.ext
    funext C
    apply Subtype.ext
    funext T
    exact Int.cast_injective ((hy C T).trans (hreadouts z C T).symm)
  rw [hyz]
  change pullbackChain p (comparison
    (quotReadouts.symm (quotReadouts (Submodule.Quotient.mk z)))).val F = _
  rw [LinearEquiv.symm_apply_apply]
  exact hcomparison z F

end D5.S3.Combinatorics.Matroids.ParallelCircuitObstruction
