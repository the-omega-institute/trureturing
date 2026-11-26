/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9PrimeLaurentBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9PrimeLaurentBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Real.Basic]
   utility: none
   digest: Distinct prime weights detect an integer Laurent row potential when the neighbor directions partition the axes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentDirectionTypes
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactTransport
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

/-!
# A prime-weight kernel gives a Laurent row identity

The unsigned interior block is the weighted Huang block in balanced switching
coordinates. The two-step expansion of its defect uses ordered paths.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PrimeLaurentBridge

open scoped BigOperators Matrix Classical
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
local notation "bitFlip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions regular_directions flip_injective)
open BalancedCubeGirth (adjacent_exists_flip)
open Q9IsotropicHuang (parity)
open Q9PureExteriorLink (exteriorDirections)
open Q9BoundaryGram (Interior)
open Q9WeightedSaturation (Rows biadjacency defect)
open Q9LaurentGainPartition
open Q9TriplePartitions (IsTriplePartition neighborPartition)
open private paritySide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private unsigned from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
open private mem_twoStepPaths flip_parity pathEnd_reverse from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition

variable {C : Finset (Q 9)} {b : Bool}

private def rowEquiv : Side C b ≃ Rows C b where
  toFun x := ⟨⟨x.val, x.property.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property.2⟩⟩
  invFun x := ⟨x.val.val, x.val.property, (Finset.mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem back_mem {x : Q 9} (hx : x ∈ C) (i : Fin 9) :
    i ∈ directions C (bitFlip x i) :=
  (mem_directions C _ _).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx)

/-- The second axes of the actual non-backtracking paths list the exterior
axes once each when the neighbor triples partition the coordinate set. -/
private def secondAxisEquiv
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (x : Side C b) (h : IsTriplePartition (neighborPartition C x.val)) :
    PathAt C x.val ≃ ↥(exteriorDirections C x.val) := by
  classical
  let block (i : Fin 9) := directions C (bitFlip x.val i)
  let P := neighborPartition C x.val
  have hP : P = (directions C x.val).image block := rfl
  have hinj : Set.InjOn block (↑(directions C x.val) : Set (Fin 9)) := by
    apply Finset.injOn_of_card_image_eq
    rw [← hP, h.card_eq, regular_directions C hC x.property.1]
  have hcover : P.biUnion id = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hd : (P : Set (Finset (Fin 9))).PairwiseDisjoint id :=
      fun _ hA _ hB hne => h.disjoint_blocks hA hB hne
    rw [Finset.card_biUnion hd]
    calc
      ∑ A ∈ P, (id A).card = ∑ _A ∈ P, 3 :=
        Finset.sum_congr rfl (fun A hA => h.block_card A hA)
      _ = Fintype.card (Fin 9) := by
        have hcard : P.card = 3 := h.card_eq
        simp [hcard]
  have block_mem {i : Fin 9} (hi : i ∈ directions C x.val) : block i ∈ P := by
    rw [hP]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have unique {i j k : Fin 9} (hi : i ∈ directions C x.val) (hj : j ∈ directions C x.val)
      (hki : k ∈ block i) (hkj : k ∈ block j) : i = j := by
    apply hinj hi hj
    by_contra hne
    exact (Finset.disjoint_left.mp
      (h.disjoint_blocks (block_mem hi) (block_mem hj) hne)) hki hkj
  let second (p : PathAt C x.val) : ↥(exteriorDirections C x.val) :=
    ⟨p.val.2, by
      obtain ⟨hi, hj, hne⟩ := mem_twoStepPaths.mp p.property
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, fun hjx => hne (unique hi hjx hj ?_)⟩
      exact back_mem x.property.1 p.val.2⟩
  refine Equiv.ofBijective second ⟨?_, ?_⟩
  · intro p q hpq
    have hj : p.val.2 = q.val.2 := congrArg Subtype.val hpq
    obtain ⟨hpi, hpj, _⟩ := mem_twoStepPaths.mp p.property
    obtain ⟨hqi, hqj, _⟩ := mem_twoStepPaths.mp q.property
    exact Subtype.ext (Prod.ext (unique hpi hqi hpj (hj.symm ▸ hqj)) hj)
  · intro j
    have hj : j.val ∈ P.biUnion id := hcover.symm ▸ Finset.mem_univ _
    obtain ⟨A, hA, hjA⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hP ▸ hA)
    have hne : i ≠ j.val := fun he => (Finset.mem_sdiff.mp j.property).2 (he ▸ hi)
    exact ⟨⟨(i, j.val), mem_twoStepPaths.mpr ⟨hi, hjA, hne⟩⟩, Subtype.ext rfl⟩

private theorem unsigned_flip (w : Fin 9 → ℝ) (z : Q 9) (i : Fin 9) :
    unsigned w z (bitFlip z i) = w i := by
  unfold unsigned
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact ite_eq_right (fun e => hji (flip_injective z e))
  · simp

private theorem unsigned_symm (w : Fin 9 → ℝ) (z v : Q 9) :
    unsigned w z v = unsigned w v z := by
  unfold unsigned
  apply Finset.sum_congr rfl
  intro i _
  have he : bitFlip z i = v ↔ bitFlip v i = z := by
    constructor <;> intro h <;> rw [← h, BalancedCriticalSpectrum.flip_flip]
  rw [if_congr he rfl rfl]

private theorem sum_unsigned (w : Fin 9 → ℝ) (z : Q 9) {ι : Type*} [Fintype ι]
    (vertex : ι → Q 9) (hv : Function.Injective vertex) (hC : ∀ a, vertex a ∈ C)
    (e : ↥(directions C z) → ι) (he : ∀ i, vertex (e i) = bitFlip z i.val) (g : ι → ℝ) :
    ∑ a, unsigned w z (vertex a) * g a = ∑ i, w i.val * g (e i) := by
  classical
  symm
  refine Fintype.sum_of_injective e (fun i j hij => Subtype.ext (flip_injective z (by
    rw [← he i, ← he j, hij]))) _ _ ?_ (fun i => by rw [he, unsigned_flip])
  intro a ha
  have hzero : unsigned w z (vertex a) = 0 := by
    unfold unsigned
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro hi
    have hd : i ∈ directions C z := (mem_directions C _ _).mpr (hi.symm ▸ hC a)
    exact ha ⟨⟨i, hd⟩, hv ((he ⟨i, hd⟩).trans hi)⟩
  rw [hzero, zero_mul]

private def middle (x : Side C b) (i : ↥(directions C x.val)) : Interior C b :=
  ⟨⟨bitFlip x.val i.val, by
      change parity (bitFlip x.val i.val) ≠ b
      rw [flip_parity, x.property.2]
      cases b <;> decide⟩,
    (mem_directions C _ _).mp i.property⟩

private def nextRow (v : Interior C b) (j : ↥(directions C v.val.val)) : Side C b :=
  ⟨bitFlip v.val.val j.val, (mem_directions C _ _).mp j.property, by
    rw [flip_parity]
    exact Bool.not_eq_iff.mpr v.val.property⟩

private abbrev TwoSteps (x : Side C b) :=
  Σ i : ↥(directions C x.val), ↥(directions C (bitFlip x.val i.val))

private def splitSteps (x : Side C b) :
    TwoSteps x ≃ (↥(directions C x.val) ⊕ PathAt C x.val) where
  toFun ij := if h : ij.1.val = ij.2.val then Sum.inl ij.1 else
    Sum.inr ⟨(ij.1.val, ij.2.val), mem_twoStepPaths.mpr ⟨ij.1.property, ij.2.property, h⟩⟩
  invFun := Sum.elim (fun i => ⟨i, ⟨i.val, back_mem x.property.1 i.val⟩⟩)
    (fun p =>
      let hp := mem_twoStepPaths.mp p.property
      ⟨⟨p.val.1, hp.1⟩, ⟨p.val.2, hp.2.1⟩⟩)
  left_inv := by
    rintro ⟨i, j⟩
    dsimp only
    split
    · rename_i h
      exact Sigma.subtype_ext rfl h
    · rfl
  right_inv := by
    rintro (i | p)
    · simp
    · simp [(mem_twoStepPaths.mp p.property).2.2]

private theorem gram_row (w : Fin 9 → ℝ) (f : Rows C b → ℝ) (x : Side C b) :
    ((defect w (biadjacency w C b)).mulVec f) (rowEquiv x) =
      (∑ j ∈ exteriorDirections C x.val, w j ^ 2) * f (rowEquiv x) -
        ∑ p : PathAt C x.val, w p.val.1 * w p.val.2 * f (rowEquiv (pathEnd x p)) := by
  classical
  let M := biadjacency w C b
  have hinner (v : Interior C b) : (Mᵀ *ᵥ f) v =
      ∑ j : ↥(directions C v.val.val), w j.val * f (rowEquiv (nextRow v j)) := by
    change (∑ y : Rows C b, unsigned w y.val.val v.val.val * f y) = _
    simp_rw [unsigned_symm w _ v.val.val]
    exact sum_unsigned w v.val.val (fun y : Rows C b => y.val.val)
      (fun _ _ h => Subtype.ext (Subtype.ext h)) (fun y => y.val.property)
      (fun j => rowEquiv (nextRow v j)) (fun _ => rfl) f
  have houter : (M *ᵥ (Mᵀ *ᵥ f)) (rowEquiv x) =
      ∑ i : ↥(directions C x.val), w i.val *
        ∑ j : ↥(directions C (bitFlip x.val i.val)),
          w j.val * f (rowEquiv (nextRow (middle x i) j)) := by
    change (∑ v : Interior C b, unsigned w x.val v.val.val * (Mᵀ *ᵥ f) v) = _
    rw [sum_unsigned w x.val (fun v : Interior C b => v.val.val)
      (fun _ _ h => Subtype.ext (Subtype.ext h)) (fun v => v.property)
      (middle x) (fun _ => rfl)]
    exact Finset.sum_congr rfl (fun i _ => congrArg (w i.val * ·) (hinner (middle x i)))
  let term (ij : TwoSteps x) :=
    w ij.1.val * (w ij.2.val * f (rowEquiv (nextRow (middle x ij.1) ij.2)))
  have hsplit :
      (∑ ij, term ij) =
        (∑ i : ↥(directions C x.val), w i.val ^ 2) * f (rowEquiv x) +
          ∑ p : PathAt C x.val, w p.val.1 * w p.val.2 * f (rowEquiv (pathEnd x p)) := by
    rw [← (splitSteps x).symm.sum_comp term, Fintype.sum_sum_type, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have hend : nextRow (middle x i) ⟨i.val, back_mem x.property.1 i.val⟩ = x :=
        Subtype.ext (BalancedCriticalSpectrum.flip_flip _ _)
      change w i.val *
        (w i.val * f (rowEquiv (nextRow (middle x i) ⟨i.val, back_mem x.property.1 i.val⟩))) = _
      rw [hend]
      ring
    · apply Finset.sum_congr rfl
      intro p _
      change w p.val.1 * (w p.val.2 * f (rowEquiv (pathEnd x p))) = _
      ring
  have hfull : (∑ j ∈ exteriorDirections C x.val, w j ^ 2) +
      (∑ j : ↥(directions C x.val), w j.val ^ 2) = ∑ j, w j ^ 2 := by
    rw [Finset.sum_coe_sort (directions C x.val) (fun j => w j ^ 2)]
    exact Finset.sum_sdiff (Finset.subset_univ _)
  change ((defect w M).mulVec f) (rowEquiv x) = _
  rw [defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  change (∑ j, w j ^ 2) * f (rowEquiv x) - (M *ᵥ (Mᵀ *ᵥ f)) (rowEquiv x) = _
  have hsum : (M *ᵥ (Mᵀ *ᵥ f)) (rowEquiv x) = ∑ ij, term ij := by
    rw [houter]
    simpa only [term, Finset.mul_sum] using (Fintype.sum_sigma term).symm
  rw [hsum, hsplit, ← hfull]
  ring

private abbrev DirectedPaths (C : Finset (Q 9)) (b : Bool) := Σ x : Side C b, PathAt C x.val

private def reversal : DirectedPaths C b ≃ DirectedPaths C b :=
  Function.Involutive.toPerm (f := fun e => ⟨pathEnd e.1 e.2, reversePath e.1 e.2⟩)
    (fun e => Sigma.subtype_ext (pathEnd_reverse e.1 e.2) rfl)

private def contacts : PrimeContactTransport.ContactGraph (Side C b) (DirectedPaths C b) 9 where
  source := Sigma.fst
  target e := pathEnd e.1 e.2
  leftAxis e := e.2.val.2
  rightAxis e := e.2.val.1
  sign _ := 1
  distinctColumns e := by
    intro he
    have he' : e.1.val = bitFlip (bitFlip e.1.val e.2.val.1) e.2.val.2 := congrArg Subtype.val he
    have h := flip_injective (bitFlip e.1.val e.2.val.1)
      ((BalancedCriticalSpectrum.flip_flip _ _).trans he')
    exact (mem_twoStepPaths.mp e.2.property).2.2 h
  distinctAxes e := (mem_twoStepPaths.mp e.2.property).2.2.symm
  sign_unit _ := Or.inl rfl

private theorem contacts_connected
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected) (x y : Side C b) :
    Relation.ReflTransGen (contacts (C := C) (b := b)).Adj x y := by
  refine Q9ProjectedWalk.projected_of_connected (C := C) (b := b) id hc ?_ x y
  intro u v z huz hzv
  obtain ⟨i, hi⟩ := adjacent_exists_flip (show (hypercube 9).Adj u.val z.val from huz)
  obtain ⟨j, hj⟩ := adjacent_exists_flip (show (hypercube 9).Adj z.val v.val from hzv)
  by_cases he : i = j
  · subst j
    have huv : u = v := Subtype.ext (by rw [hj, hi, BalancedCriticalSpectrum.flip_flip])
    subst v
    exact .refl
  · let p : PathAt C u.val :=
      ⟨(i, j), mem_twoStepPaths.mpr
        ⟨(mem_directions C _ _).mpr (hi ▸ z.property),
          (mem_directions C _ _).mpr (by rw [← hi, ← hj]; exact v.property.1), he⟩⟩
    have hend : pathEnd u p = v := by
      apply Subtype.ext
      change bitFlip (bitFlip u.val i) j = v.val
      rw [← hi, hj]
    exact .single ⟨⟨u, p⟩, Or.inl ⟨rfl, hend⟩⟩

private theorem quadratic_eq_sum_squares
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hpart : ∀ x : Side C b, IsTriplePartition (neighborPartition C x.val))
    (w : Fin 9 → ℝ) (f : Rows C b → ℝ) :
    2 * (∑ x : Side C b, f (rowEquiv x) *
      ((defect w (biadjacency w C b)).mulVec f) (rowEquiv x)) =
      ∑ e : DirectedPaths C b,
        (w e.2.val.2 * f (rowEquiv e.1) -
          w e.2.val.1 * f (rowEquiv (pathEnd e.1 e.2))) ^ 2 := by
  classical
  let left (e : DirectedPaths C b) := w e.2.val.2 * f (rowEquiv e.1)
  let right (e : DirectedPaths C b) := w e.2.val.1 * f (rowEquiv (pathEnd e.1 e.2))
  have hreverse : (∑ e, right e ^ 2) = ∑ e, left e ^ 2 :=
    Fintype.sum_equiv reversal _ _ (fun _ => rfl)
  have hrow (x : Side C b) : f (rowEquiv x) *
      ((defect w (biadjacency w C b)).mulVec f) (rowEquiv x) =
        ∑ p : PathAt C x.val, (left ⟨x, p⟩ ^ 2 - left ⟨x, p⟩ * right ⟨x, p⟩) := by
    rw [gram_row]
    have hdiag : (∑ j ∈ exteriorDirections C x.val, w j ^ 2) =
        ∑ p : PathAt C x.val, w p.val.2 ^ 2 := by
      rw [← Finset.sum_coe_sort]
      exact (Fintype.sum_equiv (secondAxisEquiv hC x (hpart x)) _ _ (fun _ => rfl)).symm
    rw [hdiag]
    simp only [mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro p _ <;> dsimp [left, right] <;> ring
  simp_rw [hrow]
  rw [← Fintype.sum_sigma (fun e => left e ^ 2 - left e * right e)]
  change 2 * (∑ e, (left e ^ 2 - left e * right e)) = ∑ e, (left e - right e) ^ 2
  have hsquare (e : DirectedPaths C b) :
      (left e - right e) ^ 2 = left e ^ 2 + right e ^ 2 - 2 * (left e * right e) := by ring
  simp_rw [hsquare, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hreverse]
  ring

private theorem laurentIdentity_of_potential
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hpart : ∀ x : Side C b, IsTriplePartition (neighborPartition C x.val))
    {a : Side C b → Exponent} {s : Side C b → ℤ}
    (h : (contacts (C := C) (b := b)).Potential a s) : LaurentIdentity a := by
  classical
  intro x
  let e := secondAxisEquiv hC x (hpart x)
  have hexp (p : PathAt C x.val) : pathExponent a x p = squareExponent (e p).val := by
    have hg := (h.2 ⟨x, p⟩).1
    change a (pathEnd x p) = a x + axis p.val.2 - axis p.val.1 at hg
    funext k
    have hk := congrFun hg k
    change a (pathEnd x p) k = a x k + axis p.val.2 k - axis p.val.1 k at hk
    change a (pathEnd x p) k - a x k + axis p.val.1 k + axis p.val.2 k =
      axis p.val.2 k + axis p.val.2 k
    omega
  apply congrArg monomialSum
  unfold pathExponents missingExponents
  calc
    _ = (Finset.univ : Finset (PathAt C x.val)).val.map (fun p => squareExponent (e p).val) :=
      Multiset.map_congr rfl (fun p _ => hexp p)
    _ = ((Finset.univ : Finset (PathAt C x.val)).val.map e).map
        (fun j => squareExponent j.val) := by rw [Multiset.map_map]; rfl
    _ = _ := by
      rw [Multiset.map_univ_val_equiv]
      change (exteriorDirections C x.val).val.attach.map (fun j => squareExponent j.val) = _
      exact Multiset.attach_map_val' _ _

/-- On a connected cubic support with actual direction partitions on the
selected parity, one nonzero switched defect kernel at distinct primes
determines an integer Laurent identity on that parity. -/
theorem exists_laurentIdentity_of_prime_defect_kernel
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hpart : ∀ x : Side C b, IsTriplePartition (neighborPartition C x.val))
    (p : Fin 9 → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (f : Rows C b → ℝ) (hf : f ≠ 0)
    (hker : (defect (fun i => (p i : ℝ)) (biadjacency (fun i => (p i : ℝ)) C b)).mulVec f = 0) :
    ∃ a : Side C b → Exponent, LaurentIdentity a := by
  classical
  let w : Fin 9 → ℝ := fun i => p i
  let z : Side C b → ℝ := f ∘ rowEquiv
  have hz : ∃ x, z x ≠ 0 := by
    by_contra! h
    apply hf
    funext y
    simpa [z] using h (rowEquiv.symm y)
  obtain ⟨root, hroot⟩ := hz
  have hsos := quadratic_eq_sum_squares hC hpart w f
  rw [hker] at hsos
  have hzero : (∑ e : DirectedPaths C b,
    (w e.2.val.2 * z e.1 - w e.2.val.1 * z (pathEnd e.1 e.2)) ^ 2) = 0 := by
    simpa [z] using hsos.symm
  have hcontact : (contacts (C := C) (b := b)).Kernel w z := by
    intro e
    have he := (Fintype.sum_eq_zero_iff_of_nonneg (fun e : DirectedPaths C b =>
      sq_nonneg (w e.2.val.2 * z e.1 - w e.2.val.1 * z (pathEnd e.1 e.2)))).mp hzero
    have hsquare : (w e.2.val.2 * z e.1 - w e.2.val.1 * z (pathEnd e.1 e.2)) ^ 2 = 0 :=
      congrFun he e
    have hdiff : w e.2.val.2 * z e.1 - w e.2.val.1 * z (pathEnd e.1 e.2) = 0 := by
      rwa [pow_two, mul_self_eq_zero] at hsquare
    simpa [contacts] using (sub_eq_zero.mp hdiff).symm
  obtain ⟨a, s, ha⟩ := PrimeContactTransport.potential_of_real_prime_kernel contacts p hp hinj
    z root hroot (contacts_connected hc root) hcontact
  exact ⟨a, laurentIdentity_of_potential hC hpart ha⟩

private theorem exists_defect_kernel_of_laurentIdentity
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hpart : ∀ x : Side C b, IsTriplePartition (neighborPartition C x.val))
    (root : Side C b) {a : Side C b → Exponent} (ha : LaurentIdentity a)
    (w : Fin 9 → ℝ) (hw : ∀ i, w i ≠ 0) :
    ∃ f : Rows C b → ℝ, f ≠ 0 ∧ (defect w (biadjacency w C b)).mulVec f = 0 := by
  let s : Side C b → ℤ := fun _ => 1
  have hpot : (contacts (C := C) (b := b)).Potential a s := by
    refine ⟨fun _ => Or.inl rfl, fun e => ⟨?_, ?_⟩⟩
    · have hg := (path_exponent_and_gain ha e.1 e.2).2.2
      change a (pathEnd e.1 e.2) = a e.1 + axis e.2.val.2 - axis e.2.val.1
      funext i
      have hi := congrFun hg i
      simp only [Pi.add_apply, Pi.sub_apply] at hi ⊢
      omega
    · change (1 : ℤ) = 1 * 1
      simp
  let z := PrimeContactTransport.signedLaurent w a s
  obtain ⟨hnz, hker⟩ := PrimeContactTransport.laurent_kernel_of_potential contacts a s hpot w hw
  refine ⟨z ∘ rowEquiv.symm, ?_, ?_⟩
  · intro he
    exact hnz root (by simpa [Function.comp_def] using congrFun he (rowEquiv root))
  · funext r
    obtain ⟨x, rfl⟩ := rowEquiv.surjective r
    rw [gram_row]
    have hdiag : (∑ j ∈ exteriorDirections C x.val, w j ^ 2) =
        ∑ q : PathAt C x.val, w q.val.2 ^ 2 := by
      rw [← Finset.sum_coe_sort]
      exact (Fintype.sum_equiv (secondAxisEquiv hC x (hpart x)) _ _ (fun _ => rfl)).symm
    rw [hdiag, Finset.sum_mul]
    apply sub_eq_zero.mpr
    apply Finset.sum_congr rfl
    intro q _
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    have he : w q.val.1 * z (pathEnd x q) = w q.val.2 * z x := by
      simpa [contacts] using hker ⟨x, q⟩
    calc
      w q.val.2 ^ 2 * z x = w q.val.2 * (w q.val.2 * z x) := by ring
      _ = w q.val.2 * (w q.val.1 * z (pathEnd x q)) := by rw [he]
      _ = _ := by ring

/-- Under the actual partition hypothesis, one prime specialization detects
existence of the Laurent identity on a connected support with a selected row. -/
theorem prime_defect_kernel_iff_laurentIdentity
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected) (root : Side C b)
    (hpart : ∀ x : Side C b, IsTriplePartition (neighborPartition C x.val))
    (p : Fin 9 → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) :
    (∃ f : Rows C b → ℝ, f ≠ 0 ∧
      (defect (fun i => (p i : ℝ)) (biadjacency (fun i => (p i : ℝ)) C b)).mulVec f = 0) ↔
      ∃ a : Side C b → Exponent, LaurentIdentity a := by
  constructor
  · rintro ⟨f, hf, hker⟩
    exact exists_laurentIdentity_of_prime_defect_kernel hC hc hpart p hp hinj f hf hker
  · rintro ⟨a, ha⟩
    exact exists_defect_kernel_of_laurentIdentity hC hpart root ha (fun i => (p i : ℝ))
      (fun i => by exact_mod_cast (hp i).ne_zero)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PrimeLaurentBridge
