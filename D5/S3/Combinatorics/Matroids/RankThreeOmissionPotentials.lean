/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Point potentials determine the cyclic factors of rank-three lifting obstructions. -/

import D5.S3.Combinatorics.Matroids.RankThreeOmissionCoordinates
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.Tactic.LinearCombination

namespace D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials

open Finset Set.powersetCard

open Function Matrix
open scoped Matroid
open SparsePavingCircuitCoordinates ParallelCircuitObstruction UniformCircuitBasis
open RationalJointCircuitImage (RationalResidue)
open RankTwoCircuitInvariantFactors (ResidueTorsion residueTorsion_equiv_zmod gcd_torsion_iff)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

private def affineLines : Fin 12 → Fin 3 → Fin 9 :=
  ![![0,1,2], ![0,3,6], ![0,4,8], ![0,5,7], ![1,3,8], ![1,4,7],
    ![1,5,6], ![2,3,7], ![2,4,6], ![2,5,8], ![3,4,5], ![6,7,8]]

private def affineFormula (a b : ZMod 3) : Fin 9 → ZMod 3 :=
  ![0, b, -b, a, a + b, a - b, -a, -a + b, -a - b]

private def lineConstraint (u : Fin 9 → ZMod 3) (i : Fin 12) : Prop :=
  u (affineLines i 0) + u (affineLines i 1) + u (affineLines i 2) = 0

/-- A zero-at-the-origin potential with zero sums on the twelve affine lines
is determined by its two coordinate slopes. -/
private theorem affine_plane_potential_coordinates (u : Fin 9 → ZMod 3) :
    (u 0 = 0 ∧ ∀ i, lineConstraint u i) ↔
      u = affineFormula (u 3) (u 1) := by
  have hthree : (3 : ZMod 3) = 0 := by decide
  constructor
  · rintro ⟨h0, h⟩
    have h012 : u 0 + u 1 + u 2 = 0 := h 0
    have h036 : u 0 + u 3 + u 6 = 0 := h 1
    have h048 : u 0 + u 4 + u 8 = 0 := h 2
    have h138 : u 1 + u 3 + u 8 = 0 := h 4
    have h147 : u 1 + u 4 + u 7 = 0 := h 5
    have h345 : u 3 + u 4 + u 5 = 0 := h 10
    have h2 : u 2 = -u 1 := by linear_combination h012 - h0
    have h6 : u 6 = -u 3 := by linear_combination h036 - h0
    have h8 : u 8 = -u 3 - u 1 := by linear_combination h138
    have h4 : u 4 = u 3 + u 1 := by linear_combination h048 - h138 - h0
    have h5 : u 5 = u 3 - u 1 := by
      linear_combination h345 - h4 - u 3 * hthree
    have h7 : u 7 = -u 3 + u 1 := by
      linear_combination h147 - h4 - u 1 * hthree
    funext i
    fin_cases i <;> first | assumption | rfl
  · intro h
    rw [h]
    refine ⟨rfl, fun i => ?_⟩
    fin_cases i <;> simp [lineConstraint, affineLines, affineFormula] <;> ring_nf <;> simp [hthree]

private theorem affine_plane_potential_card :
    Nat.card {u : Fin 9 → ZMod 3 // u 0 = 0 ∧ ∀ i, lineConstraint u i} = 9 := by
  classical
  let e : {u : Fin 9 → ZMod 3 // u 0 = 0 ∧ ∀ i, lineConstraint u i} ≃
      ZMod 3 × ZMod 3 :=
    { toFun := fun u => (u.val 3, u.val 1)
      invFun := fun s => ⟨affineFormula s.1 s.2,
        (affine_plane_potential_coordinates _).mpr rfl⟩
      left_inv := fun u => Subtype.ext ((affine_plane_potential_coordinates u.val).mp u.prop).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]

private theorem affine_triangle_injective :
    ∀ t, Function.Injective (affineLines t) := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem affine_pair_unique :
    ∀ t s i j, i ≠ j → covers (affineLines t) i j → covers (affineLines s) i j → t = s := by
  unfold covers
  decide

set_option maxRecDepth 8192 in
private theorem affine_pair_covered :
    ∀ i j : Fin 9, i ≠ j → ∃ t a b, affineLines t a = i ∧ affineLines t b = j := by decide

private theorem affine_compatible_iff (u : Fin 9 → ZMod 3) :
    IsOmissionPotential affineLines 0 u ↔ u 0 = 0 ∧ ∀ i, lineConstraint u i := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.2.2⟩
  · rintro ⟨h0, hline⟩
    have h012 : u 0 + u 1 + u 2 = 0 := hline 0
    have h345 : u 3 + u 4 + u 5 = 0 := hline 10
    have h678 : u 6 + u 7 + u 8 = 0 := hline 11
    refine ⟨h0, ?_, ?_, ?_, hline⟩
    · simp [Fin.sum_univ_succ]
      linear_combination h012 + h345 + h678
    · intro i
      rw [nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
    · intro i j huncovered
      by_cases h : i = j
      · exact congrArg u h
      · exact (huncovered (affine_pair_covered i j h)).elim

/-- The cokernel of a matrix over a finite residue ring has the same size
as the kernel of its transpose. This uses the perfect character pairing. -/
private theorem transpose_kernel_card_eq_cokernel {m n : Type*} [Fintype m] [Fintype n]
    (q : ℕ) [NeZero q] (A : Matrix m n (ZMod q)) :
    Nat.card {y : m → ZMod q // A.transpose.mulVec y = 0} =
      Nat.card ((m → ZMod q) ⧸ LinearMap.range A.mulVecLin) := by
  classical
  let P := LinearMap.range A.mulVecLin
  let Q := (m → ZMod q) ⧸ P
  let dot := dotProductEquiv (ZMod q) m
  let χ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hχ : Injective χ := ZMod.injective_stdAddChar
  let pull (y : m → ZMod q) : AddChar (m → ZMod q) ℂ :=
    χ.compAddMonoidHom (dot y).toAddMonoidHom
  have hpull : Bijective pull := by
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    refine ⟨?_, rfl⟩
    intro y z h
    have he := AddChar.compAddMonoidHom_injective_right χ hχ h
    apply dot.injective
    exact LinearMap.ext fun x => congrArg (fun f : (m → ZMod q) →+ ZMod q => f x) he
  have transport (y : m → ZMod q) (x : n → ZMod q) :
      dot y (A.mulVec x) = dotProduct (A.transpose.mulVec y) x := by
    change dotProduct y (A.mulVec x) = _
    rw [dotProduct_mulVec, mulVec_transpose]
  have vanishes (y : m → ZMod q) (hy : A.transpose.mulVec y = 0) :
      P ≤ LinearMap.ker (dot y) := by
    rintro z ⟨x, rfl⟩
    change dot y (A.mulVec x) = 0
    rw [transport, hy, zero_dotProduct]
  let forward (y : {y : m → ZMod q // A.transpose.mulVec y = 0}) : AddChar Q ℂ :=
    χ.compAddMonoidHom (P.liftQ (dot y.val) (vanishes y.val y.prop)).toAddMonoidHom
  have eval (y : {y : m → ZMod q // A.transpose.mulVec y = 0}) (z : m → ZMod q) :
      forward y (P.mkQ z) = pull y.val z := rfl
  have hforward : Bijective forward := by
    constructor
    · intro y z h
      apply Subtype.ext
      apply hpull.injective
      ext x
      rw [← eval, ← eval, h]
    · intro ψ
      obtain ⟨y, hy⟩ := hpull.surjective (ψ.compAddMonoidHom P.mkQ.toAddMonoidHom)
      have hy' (x : n → ZMod q) : dotProduct (A.transpose.mulVec y) x = 0 := by
        have hmem : A.mulVec x ∈ P := ⟨x, rfl⟩
        have hzero : P.mkQ (A.mulVec x) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hmem
        have h := DFunLike.congr_fun hy (A.mulVec x)
        change χ (dot y (A.mulVec x)) = ψ (P.mkQ (A.mulVec x)) at h
        apply hχ
        rw [← transport, h, hzero, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one]
      have hk : A.transpose.mulVec y = 0 := by
        funext i
        simpa only [dotProduct_single_one, Pi.zero_apply] using hy' (Pi.single i 1)
      let v : {y : m → ZMod q // A.transpose.mulVec y = 0} := ⟨y, hk⟩
      refine ⟨v, ?_⟩
      ext x
      obtain ⟨z, rfl⟩ := P.mkQ_surjective x
      rw [eval, show v.val = y from rfl, hy]
      rfl
  have hcard : Nat.card (AddChar Q ℂ) = Nat.card Q := by
    let _ : Fintype Q := Fintype.ofFinite Q
    simp only [Nat.card_eq_fintype_card, AddChar.card_eq]
  exact (Nat.card_congr (Equiv.ofBijective forward hforward)).trans hcard

/-- Counting the image in two ways relates the primal and transpose kernels. -/
private theorem primal_kernel_card_mul {m n : Type*} [Fintype m] [Fintype n]
    (q : ℕ) [NeZero q] (A : Matrix m n (ZMod q)) :
    Nat.card {x : n → ZMod q // A.mulVec x = 0} * q ^ Fintype.card m =
      q ^ Fintype.card n * Nat.card {y : m → ZMod q // A.transpose.mulVec y = 0} := by
  let f := A.mulVecLin
  have hX : Nat.card (n → ZMod q) = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
      Nat.card_congr f.quotKerEquivRange.toEquiv]
  have hY : Nat.card (m → ZMod q) = Nat.card (LinearMap.range f) *
      Nat.card {y : m → ZMod q // A.transpose.mulVec y = 0} := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range f),
      ← transpose_kernel_card_eq_cokernel q A]
  have cardM : Nat.card (m → ZMod q) = q ^ Fintype.card m := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card]
  have cardN : Nat.card (n → ZMod q) = q ^ Fintype.card n := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card]
  rw [← cardM, ← cardN, hY, hX]
  change Nat.card (LinearMap.ker f) * (_ * _) = _
  exact (Nat.mul_assoc _ _ _).symm

private theorem map_reducedMatrix_mulVec {I T R S : Type*}
    [Fintype I] [LinearOrder I] [CommRing R] [CommRing S]
    (points : T → Fin 3 → I) (root anchor : I) (f : R →+ S)
    (x : RemainingPair root anchor → R) :
    f ∘ (reducedMatrix points root anchor).mulVec x =
      (reducedMatrix points root anchor).mulVec (f ∘ x) := by
  funext t
  change f (∑ ij, (reducedMatrix points root anchor) t ij * x ij) =
    ∑ ij, (reducedMatrix points root anchor) t ij * f (x ij)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← reducedMatrix_intCast (R := R), ← reducedMatrix_intCast (R := S)]
  simpa only [zsmul_eq_mul] using f.map_zsmul
    ((reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) ℤ) t ij) (x ij)

private theorem affine_lines_increasing : ∀ t, StrictMono (affineLines t) := by decide

private def affineTriangle (t : Fin 12) : Fin 3 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono (affineLines t) (affine_lines_increasing t)

/-- The twelve affine lines on the nine points, numbered in row-major order. -/
def affineOmissions : Set (Finset (Fin 9)) :=
  Set.range fun t => (ofFinEmbEquiv (affineTriangle t)).val

private theorem zmod_torsion_embedding (q s : ℕ) (hq : 0 < q) :
    ∃ f : ZMod (q.gcd s) →+ ZMod q, Injective f ∧
      ∀ y : ZMod q, s • y = 0 ↔ y ∈ Set.range f := by
  obtain ⟨eqQ⟩ := residueTorsion_equiv_zmod q hq.ne'
  obtain ⟨eqG⟩ := residueTorsion_equiv_zmod (q.gcd s) (Nat.gcd_pos_of_pos_left s hq).ne'
  have incl : ResidueTorsion (q.gcd s) ≤ ResidueTorsion q :=
    fun x hx => ((gcd_torsion_iff q s x).mp hx).1
  let e := eqQ.toLinearMap.comp ((Submodule.inclusion incl).comp eqG.symm.toLinearMap)
  refine ⟨e.toAddMonoidHom, eqQ.injective.comp
    ((Submodule.inclusion_injective incl).comp eqG.symm.injective), fun y => ?_⟩
  constructor
  · intro hy
    let u := eqQ.symm y
    have hu : (s : ℤ) • u = 0 := by
      apply eqQ.injective
      rw [map_zsmul, LinearEquiv.apply_symm_apply, map_zero, natCast_zsmul, hy]
    have hg := (gcd_torsion_iff q s u.val).mpr
      ⟨u.prop, congrArg (fun x : ResidueTorsion q => x.val) hu⟩
    let v : ResidueTorsion (q.gcd s) := ⟨u.val, hg⟩
    refine ⟨eqG v, ?_⟩
    change eqQ (Submodule.inclusion incl (eqG.symm (eqG v))) = _
    rw [LinearEquiv.symm_apply_apply]
    exact eqQ.apply_symm_apply y
  · rintro ⟨x, rfl⟩
    let v := eqG.symm x
    have hk := ((gcd_torsion_iff q s v.val).mp v.prop).2
    rw [← natCast_zsmul]
    change (s : ℤ) • eqQ (Submodule.inclusion incl v) = 0
    rw [← map_zsmul, ← eqQ.map_zero]
    exact congrArg eqQ (Subtype.ext (by exact hk))

private theorem omissionPotential_card_of_torsion {I T : Type*} [Fintype I]
    (points : T → Fin 3 → I) (anchor : I) (q : ℕ) (hq : 0 < q) :
    Nat.card {u : I → ZMod q // IsOmissionPotential points anchor u} =
      Nat.card {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} := by
  obtain ⟨f, hf, hrange⟩ := zmod_torsion_embedding q 3 hq
  have preserves (u : I → ZMod (q.gcd 3)) :
      IsOmissionPotential points anchor (f ∘ u) ↔ IsOmissionPotential points anchor u := by
    simp only [IsOmissionPotential, Function.comp_apply, ← map_sum, ← map_nsmul, ← map_add,
      ← f.map_zero, hf.eq_iff]
  let e : {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} ≃
      {u : I → ZMod q // IsOmissionPotential points anchor u} := by
    refine Equiv.ofBijective (fun u => ⟨f ∘ u.val, (preserves _).mpr u.prop⟩) ?_
    constructor
    · intro u v h
      apply Subtype.ext
      funext i
      exact hf (congrFun (congrArg Subtype.val h) i)
    · intro u
      have h (i : I) : u.val i ∈ Set.range f := (hrange _).mp (u.prop.2.2.1 i)
      choose v hv using h
      have he : f ∘ v = u.val := funext hv
      exact ⟨⟨v, (preserves v).mp (he.symm ▸ u.prop)⟩, Subtype.ext he⟩
  exact Nat.card_congr e.symm

/-- At every divisor of the number of points, the cardinality of the reduced
kernel is determined by the corresponding ternary potential count. -/
private theorem rank_three_kernel_card_by_potential {I T : Type*}
    [Fintype I] [LinearOrder I] [Fintype T]
    (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j →
      (∃ a b, points t a = i ∧ points t b = j) →
      (∃ a b, points s a = i ∧ points s b = j) → t = s)
    (root anchor : I) (hne : anchor ≠ root) (q : ℕ) [NeZero q]
    (hqn : q ∣ Fintype.card I) :
    Nat.card {x : RemainingPair root anchor → ZMod q //
        (reducedMatrix points root anchor).mulVec x = 0} * q ^ Fintype.card T =
      q ^ Fintype.card (RemainingPair root anchor) *
        Nat.card {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} := by
  have annihilates (x : ZMod q) : Fintype.card I • x = 0 := by
    rw [nsmul_eq_mul, (ZMod.natCast_eq_zero_iff _ _).mpr hqn, zero_mul]
  let E : {u : I → ZMod q // IsOmissionPotential points anchor u} ≃
      {c : T → ZMod q // IsReducedRelation points root anchor c} :=
    Equiv.ofBijective _ (potential_to_relations_bijective points hinj hdis
      root anchor hne annihilates).bijective
  let F : {c : T → ZMod q // (reducedMatrix points root anchor).transpose.mulVec c = 0} ≃
      {c : T → ZMod q // IsReducedRelation points root anchor c} :=
    Equiv.subtypeEquivRight (reduced_transpose_kernel_iff points hinj root anchor)
  rw [primal_kernel_card_mul q, Nat.card_congr (F.trans E.symm),
    omissionPotential_card_of_torsion points anchor q (NeZero.pos q)]

private theorem remainingPair_card {I : Type*} [Fintype I] [LinearOrder I]
    (root anchor : I) (hne : anchor ≠ root) :
    Fintype.card (RemainingPair root anchor) = (Fintype.card I - 2).choose 2 := by
  classical
  let S := ((univ : Finset I).erase root).erase anchor
  let U := {s : Set.powersetCard I 2 // root ∉ s.val ∧ anchor ∉ s.val}
  have contained (s : Finset I) : s ⊆ S ↔ root ∉ s ∧ anchor ∉ s := by
    simp only [S, subset_erase, subset_univ, true_and]
  let e : U ≃ (S.powersetCard 2 : Finset (Finset I)) :=
    { toFun := fun s => ⟨s.val.val, mem_powersetCard.mpr
        ⟨(contained _).mpr s.prop, s.val.prop⟩⟩
      invFun := fun s =>
        let h := mem_powersetCard.mp s.prop
        ⟨⟨s.val, h.2⟩, (contained _).mp h.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr ((pairIndexEquiv root anchor).trans e), Fintype.card_coe,
    card_powersetCard, card_erase_of_mem (mem_erase.mpr ⟨hne, mem_univ _⟩),
    card_erase_of_mem (mem_univ _), card_univ, Nat.sub_sub]

private theorem reduced_kernel_torsion_card {I T : Type*} [Fintype I] [LinearOrder I]
    (points : T → Fin 3 → I) (root anchor : I) (n q : ℕ) (hn : 0 < n) (hqn : q ∣ n) :
    let K := (reducedMatrix points root anchor :
      Matrix T (RemainingPair root anchor) (ZMod n)).mulVecLin.ker.restrictScalars ℤ
    Nat.card {x : K // q • x = 0} =
      Nat.card {x : RemainingPair root anchor → ZMod q //
        (reducedMatrix points root anchor).mulVec x = 0} := by
  intro K
  have hEmbed := zmod_torsion_embedding n q hn
  rw [Nat.gcd_eq_right hqn] at hEmbed
  obtain ⟨f, hf, hrange⟩ := hEmbed
  have preserves (x : RemainingPair root anchor → ZMod q) :
      (reducedMatrix points root anchor).mulVec (f ∘ x) = 0 ↔
        (reducedMatrix points root anchor).mulVec x = 0 := by
    rw [← map_reducedMatrix_mulVec points root anchor f x]
    constructor
    · intro h
      funext t
      apply hf
      exact (congrFun h t).trans f.map_zero.symm
    · intro h
      funext t
      rw [h]
      exact f.map_zero
  let e : {x : RemainingPair root anchor → ZMod q //
      (reducedMatrix points root anchor).mulVec x = 0} ≃ {x : K // q • x = 0} := by
    let into (x : RemainingPair root anchor → ZMod q) (hx : _) : K :=
      ⟨f ∘ x, (preserves _).mpr hx⟩
    refine Equiv.ofBijective (fun x => ⟨into x.val x.prop, Subtype.ext ?_⟩) ?_
    · funext i
      exact (hrange _).mpr ⟨x.val i, rfl⟩
    constructor
    · intro x y h
      apply Subtype.ext
      funext i
      exact hf (congrArg (fun u : {x : K // q • x = 0} => u.val.val i) h)
    · intro y
      have hy (i : RemainingPair root anchor) : q • y.val.val i = 0 :=
        congrArg (fun x : K => x.val i) y.prop
      choose x hx using fun i => (hrange _).mp (hy i)
      have he : f ∘ x = y.val.val := funext hx
      have mem := (preserves x).mp (he.symm ▸ y.val.prop)
      exact ⟨⟨x, mem⟩, Subtype.ext (Subtype.ext he)⟩
  exact Nat.card_congr e.symm

private theorem sparse_triangle_unique_pair {I T : Type*} [LinearOrder I]
    (triangles : T → Fin 3 ↪o I) (ht : Injective triangles)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (t s : T) (i j : I) (hij : i ≠ j)
    (hi : covers (triangles t) i j) (hj : covers (triangles s) i j) : t = s := by
  let H := (ofFinEmbEquiv (triangles t)).val
  let J := (ofFinEmbEquiv (triangles s)).val
  have HJ : H = J := by
    by_contra hne
    have hs := hsparse (show H ∈ Set.range _ from ⟨t, rfl⟩)
      (show J ∈ Set.range _ from ⟨s, rfl⟩) hne
    have covered (b : T) (h : covers (triangles b) i j) :
        i ∈ (ofFinEmbEquiv (triangles b)).val ∧ j ∈ (ofFinEmbEquiv (triangles b)).val := by
      obtain ⟨x, y, hx, hy⟩ := h
      exact ⟨(mem_ofFinEmbEquiv_iff_mem_range _ _).mpr ⟨x, hx⟩,
        (mem_ofFinEmbEquiv_iff_mem_range _ _).mpr ⟨y, hy⟩⟩
    have hc := Finset.one_lt_card_iff.mpr
      ⟨i, j, mem_inter.mpr ⟨(covered t hi).1, (covered s hj).1⟩,
        mem_inter.mpr ⟨(covered t hi).2, (covered s hj).2⟩, hij⟩
    change 1 < (H ∩ J).card at hc
    omega
  exact ht (ofFinEmbEquiv.injective (Subtype.ext HJ))

/-- The point potentials count the elements of the integral obstruction
killed by any divisor of the ground-set size. -/
theorem rank_three_lifting_obstruction_torsion_card {I T : Type*}
    [Fintype I] [LinearOrder I] [Fintype T]
    (M : Matroid I) (triangles : T → Fin 3 ↪o I) (ht : Injective triangles)
    (anchor : I) (hn : 3 < Fintype.card I)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (hbase : ∀ B : Finset I, M.IsBase (B : Set I) ↔
      B.card = 3 ∧ B ∉ Set.range fun t => (ofFinEmbEquiv (triangles t)).val)
    (q : ℕ) [NeZero q] (hqn : q ∣ Fintype.card I) :
    let G := JointSaturatedImage (M.comap (id : I → I)) ⧸
      JointImageInSaturation (M.comap (id : I → I))
    Nat.card {x : G // q • x = 0} * q ^ Fintype.card T =
      q ^ ((Fintype.card I - 2).choose 2) *
        Nat.card {u : I → ZMod (q.gcd 3) //
          IsOmissionPotential (fun t => triangles t) anchor u} := by
  intro G
  obtain ⟨root, hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega) anchor
  have hne := hne.symm
  let points (t : T) : Fin 3 → I := triangles t
  obtain ⟨equiv⟩ := rank_three_lifting_obstruction_equiv_kernel M triangles root anchor
    hne hn hsparse hbase
  have transform := equiv.toEquiv.subtypeEquiv
    (p := fun x : G => q • x = 0) (q := fun y => q • y = 0) (fun x => by
      change q • x = 0 ↔ q • equiv x = 0
      have hmap : equiv (q • x) = q • equiv x := by
        simpa only [natCast_zsmul] using equiv.map_smul (q : ℤ) x
      rw [← hmap, ← equiv.map_zero, equiv.injective.eq_iff])
  rw [Nat.card_congr transform, reduced_kernel_torsion_card points root anchor
    (Fintype.card I) q (by omega) hqn, ← remainingPair_card root anchor hne]
  exact rank_three_kernel_card_by_potential points (fun t => (triangles t).injective)
    (sparse_triangle_unique_pair triangles ht hsparse) root anchor hne q hqn

private theorem int_cast_matrix_rigidity {m n : Type*} [Fintype m]
    (A : Matrix n m ℤ) (q : ℕ) (hq : 3 < q)
    (hkill : ∀ x : m → ZMod q, (A.map (Int.castRingHom (ZMod q))).mulVec x = 0 →
      ∀ i, 3 • x i = 0) :
    ∀ x : m → ℤ, A.mulVec x = 0 → x = 0 := by
  classical
  let qZ : ℤ := q
  let g := Int.gcd qZ 3
  have gpos : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by decide)
  obtain ⟨d, e, hde, hqde, h3de⟩ := Int.exists_gcd_one gpos
  have gnz : (g : ℤ) ≠ 0 := by exact_mod_cast gpos.ne'
  have gbound : (g : ℤ) ≤ 3 := Int.le_of_dvd (by decide) (Int.gcd_dvd_right qZ 3)
  have dpos : 1 < d := by
    have hq' : 3 < qZ := by
      change 3 < (q : ℤ)
      exact_mod_cast hq
    nlinarith
  have divisibility (x : m → ℤ) (hx : A.mulVec x = 0) (i : m) : d ∣ x i := by
    let cast := Int.castRingHom (ZMod q)
    have hm : (A.map cast).mulVec (cast ∘ x) = 0 := by
      funext j
      rw [← RingHom.map_mulVec, hx]
      exact cast.map_zero
    have h := hkill (cast ∘ x) hm i
    rw [nsmul_eq_mul] at h
    have h' : ((3 * x i : ℤ) : ZMod q) = 0 := by
      simpa [cast, Int.cast_mul, Function.comp_def] using h
    have hdiv : qZ ∣ 3 * x i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
    have hdiv' : d * (g : ℤ) ∣ e * x i * (g : ℤ) := by
      convert hdiv using 1
      · exact hqde.symm
      · rw [mul_right_comm, ← h3de]
    exact Int.dvd_of_dvd_mul_right_of_gcd_one (Int.dvd_of_mul_dvd_mul_right gnz hdiv') hde
  intro x hx
  funext i
  by_contra hi
  have existsPositive : ∃ a : ℕ, ∃ v : m → ℤ, A.mulVec v = 0 ∧
      v i ≠ 0 ∧ (v i).natAbs = a := ⟨_, x, hx, hi, rfl⟩
  obtain ⟨v, hv, hvi, hmin⟩ := Nat.find_spec existsPositive
  choose w hw using divisibility v hv
  have veq : v = d • w := funext hw
  have hscaled : d • A.mulVec w = 0 := by rwa [veq, Matrix.mulVec_smul] at hv
  have wker : A.mulVec w = 0 := by
    funext j
    have h := congrFun hscaled j
    change d * A.mulVec w j = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (by omega)
  have wi : w i ≠ 0 := by
    intro zero
    exact hvi (by rw [hw, zero, mul_zero])
  have less : (w i).natAbs < Nat.find existsPositive := by
    rw [← hmin, hw, Int.natAbs_mul]
    have habs : 1 < d.natAbs := by omega
    have hwpos : 0 < (w i).natAbs := Int.natAbs_pos.mpr wi
    nlinarith
  exact (Nat.find_min existsPositive less) ⟨w, wker, wi, rfl⟩

private theorem smith_kernel_split {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) (hA : Injective A.transpose.mulVecLin) (q : ℕ) :
    Fintype.card m ≤ Fintype.card n ∧ ∃ d : Fin (Fintype.card m) → ℤ,
      Nonempty (↥((A.map (Int.castRingHom (ZMod q))).mulVecLin.ker.restrictScalars ℤ) ≃ₗ[ℤ]
        (Fin (Fintype.card n - Fintype.card m) → ZMod q) ×
          ((i : Fin (Fintype.card m)) → Submodule.torsionBy ℤ (ZMod q) (d i))) := by
  classical
  let f := A.transpose.mulVecLin
  let b := Pi.basisFun ℤ n
  let c := Pi.basisFun ℤ m
  obtain ⟨r, S⟩ := (LinearMap.range f).smithNormalForm b
  have rcard : r = Fintype.card m := by
    let br := c.map (LinearEquiv.ofInjective f hA)
    simpa only [Fintype.card_fin] using Fintype.card_congr (S.bN.indexEquiv br)
  subst r
  let d := S.a
  let D (i : Fin (Fintype.card m)) := Submodule.torsionBy ℤ (ZMod q) (d i)
  refine ⟨by simpa using Fintype.card_le_of_injective S.f S.f.injective, d, ?_⟩
  let cast := Int.castRingHom (ZMod q)
  let K := (A.map cast).mulVecLin.ker.restrictScalars ℤ
  let P : Submodule ℤ (n → ZMod q) :=
    ⨅ i, (D i).comap (LinearMap.proj (R := ℤ) (φ := fun _ : n => ZMod q) (S.f i))
  let coord : (n → ZMod q) ≃ₗ[ℤ] (n → ZMod q) :=
    (b.constr ℤ).trans (S.bM.constr ℤ).symm
  have read (x : n → ZMod q) (i : m) :
      (A.map cast).mulVec x i = (b.constr ℤ x) (f (c i)) := by
    have col : f (c i) = fun j => A i j := by
      simp [f, c, Pi.basisFun_apply, Matrix.mulVec_single_one]
      rfl
    have expand : (fun j => A i j) = ∑ j, A i j • b j := by
      funext k
      simp [b, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, mul_ite]
    rw [col]
    conv => rhs; arg 2; rw [expand]
    rw [map_sum]
    change (∑ j, cast (A i j) * x j) = _
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, Module.Basis.constr_basis]
    rw [zsmul_eq_mul]
    rfl
  have ann (x : n → ZMod q) : x ∈ K ↔ ∀ y : f.range, (b.constr ℤ x) y.val = 0 := by
    change (A.map cast).mulVec x = 0 ↔ _
    constructor
    · intro h y
      obtain ⟨z, hz⟩ := y.prop
      have hz' : (b.constr ℤ x).comp f = 0 := c.ext fun i => by
        exact (read x i).symm.trans (congrFun h i)
      rw [← hz]
      exact congrFun (congrArg DFunLike.coe hz') z
    · intro h
      funext i
      rw [read]
      exact h ⟨f (c i), ⟨c i, rfl⟩⟩
  have diag (x : n → ZMod q) : x ∈ K ↔ coord x ∈ P := by
    rw [ann]
    have eqn (i : Fin (Fintype.card m)) :
        (b.constr ℤ x) (S.bN i : f.range).val = d i • coord x (S.f i) := by
      rw [S.snf, map_zsmul]
      rfl
    have constraints : coord x ∈ P ↔ ∀ i, d i • coord x (S.f i) = 0 := by
      simp only [P, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply,
        Submodule.mem_torsionBy_iff, D]
    rw [constraints]
    constructor
    · intro h i
      rw [← eqn]
      exact h (S.bN i)
    · intro h y
      have hzero : (b.constr ℤ x).comp f.range.subtype = 0 := S.bN.ext fun i => by
        exact (eqn i).trans (h i)
      exact congrFun (congrArg DFunLike.coe hzero) y
  let e := coord.ofSubmodules K P (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    change coord.symm x ∈ K ↔ x ∈ P
    rw [diag, LinearEquiv.apply_symm_apply])
  let U := {j : n // j ∉ Set.range S.f}
  have accepts (x : n → ZMod q) : x ∈ P ↔ ∀ i, x (S.f i) ∈ D i := by
    simp only [P, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply]
  let separate : P →ₗ[ℤ] (U → ZMod q) × ((i : Fin (Fintype.card m)) → D i) :=
    { toFun := fun x => (fun j => x.val j, fun i => ⟨x.val (S.f i), (accepts _).mp x.prop i⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have bijective : Bijective separate := by
    constructor
    · intro x y h
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ Set.range S.f
      · obtain ⟨i, rfl⟩ := hj
        exact congrArg (fun v => (v.2 i).val) h
      · exact congrArg (fun v => v.1 ⟨j, hj⟩) h
    · intro y
      let x (j : n) : ZMod q :=
        if hj : j ∈ Set.range S.f then (y.2 hj.choose).val else y.1 ⟨j, hj⟩
      have some (i : Fin (Fintype.card m)) : x (S.f i) = (y.2 i).val := by
        have h : S.f i ∈ Set.range S.f := ⟨i, rfl⟩
        dsimp only [x]
        rw [dif_pos h, S.f.injective h.choose_spec]
      refine ⟨⟨x, (accepts _).mpr (fun i => (some i).symm ▸ (y.2 i).prop)⟩, Prod.ext ?_ ?_⟩
      · funext j
        exact dif_neg j.prop
      · funext i
        exact Subtype.ext (some i)
  have ucard : Fintype.card U = Fintype.card n - Fintype.card m := by
    rw [Fintype.card_subtype_compl, ← Fintype.card_congr (Equiv.ofInjective S.f S.f.injective),
      Fintype.card_fin]
  let free := LinearEquiv.piCongrLeft' ℤ (fun _ : U => ZMod q) (Fintype.equivFinOfCardEq ucard)
  exact ⟨e.trans ((LinearEquiv.ofBijective separate bijective).trans
    (free.prodCongr (LinearEquiv.refl ℤ _)))⟩

private theorem zmod_torsion_card (n q : ℕ) (hn : 0 < n) (hq : q ∣ n) :
    Nat.card {x : ZMod n // q • x = 0} = q := by
  have h := zmod_torsion_embedding n q hn
  rw [Nat.gcd_eq_right hq] at h
  obtain ⟨f, hf, hrange⟩ := h
  let e : ZMod q ≃ {x : ZMod n // q • x = 0} :=
    Equiv.ofBijective (fun x => ⟨f x, (hrange _).mpr ⟨x, rfl⟩⟩)
      ⟨fun _ _ hx => hf (congrArg Subtype.val hx), fun y => by
        obtain ⟨x, hx⟩ := (hrange _).mp y.prop
        exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e, Nat.card_zmod]

private theorem free_prod_torsion_card {G D : Type*} [AddCommGroup G] [AddCommGroup D]
    (n r q : ℕ) (hn : 0 < n) (hq : q ∣ n)
    (e : G ≃+ (Fin r → ZMod n) × D) :
    Nat.card {x : G // q • x = 0} = q ^ r * Nat.card {y : D // q • y = 0} := by
  let transfer : {x : G // q • x = 0} ≃ {x : (Fin r → ZMod n) × D // q • x = 0} :=
    e.toEquiv.subtypeEquiv (fun x => by
      change q • x = 0 ↔ q • e x = 0
      rw [← map_nsmul, ← e.map_zero, e.injective.eq_iff])
  let split : {x : (Fin r → ZMod n) × D // q • x = 0} ≃
      {f : Fin r → ZMod n // ∀ i, q • f i = 0} × {y : D // q • y = 0} :=
    (Equiv.subtypeEquivRight (fun x => by
      rcases x with ⟨f, y⟩
      change ((q • f, q • y) : (Fin r → ZMod n) × D) = (0, 0) ↔ _
      simp only [Prod.mk.injEq, funext_iff, Pi.smul_apply, Pi.zero_apply])).trans
      (@Equiv.subtypeProdEquivProd _ _ (fun f : Fin r → ZMod n => ∀ i, q • f i = 0)
        (fun y : D => q • y = 0))
  let pointwise : {f : Fin r → ZMod n // ∀ i, q • f i = 0} ≃
      (Fin r → {x : ZMod n // q • x = 0}) :=
    @Equiv.subtypePiEquivPi (Fin r) (fun _ => ZMod n) (fun _ x => q • x = 0)
  rw [Nat.card_congr (transfer.trans split), Nat.card_prod,
    Nat.card_congr pointwise, Nat.card_fun,
    zmod_torsion_card n q hn hq, Nat.card_fin]

/-- The integral lifting obstruction is the sum of the free residue coordinates
and a ternary vector space of the same size as the normalized point potentials. -/
theorem rank_three_lifting_obstruction_cyclic_factors {I T : Type*}
    [Fintype I] [LinearOrder I] [Fintype T]
    (M : Matroid I) (triangles : T → Fin 3 ↪o I) (ht : Injective triangles)
    (anchor : I) (hn : 3 < Fintype.card I)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (hbase : ∀ B : Finset I, M.IsBase (B : Set I) ↔
      B.card = 3 ∧ B ∉ Set.range fun t => (ofFinEmbEquiv (triangles t)).val) :
    let n := Fintype.card I
    let r := (n - 2).choose 2 - Fintype.card T
    let G := JointSaturatedImage (M.comap (id : I → I)) ⧸
      JointImageInSaturation (M.comap (id : I → I))
    ∃ d, Nat.card {u : I → ZMod (n.gcd 3) //
        IsOmissionPotential (fun t => triangles t) anchor u} = 3 ^ d ∧
      Nonempty (G ≃ₗ[ℤ] (Fin r → ZMod n) × (Fin d → ZMod 3)) := by
  classical
  intro n r G
  obtain ⟨root, hrne⟩ := Fintype.exists_ne_of_one_lt_card (by omega) anchor
  have hne := hrne.symm
  let b := (n - 2).choose 2
  let m := Fintype.card T
  let g := n.gcd 3
  have hnpos : 0 < n := by omega
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left 3 hnpos
  let _ : NeZero n := ⟨hnpos.ne'⟩
  let _ : NeZero g := ⟨hgpos.ne'⟩
  let points (t : T) : Fin 3 → I := triangles t
  let A : Matrix T (RemainingPair root anchor) ℤ := reducedMatrix points root anchor
  have castA : A.map (Int.castRingHom (ZMod n)) =
      (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) (ZMod n)) := by
    ext i j
    exact reducedMatrix_intCast points root anchor i j
  have castT : A.transpose.map (Int.castRingHom (ZMod n)) =
      (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) (ZMod n)).transpose := by
    ext j i
    exact reducedMatrix_intCast points root anchor i j
  have nKills (x : ZMod n) : n • x = 0 := by
    rw [nsmul_eq_mul, (ZMod.natCast_eq_zero_iff n n).mpr (dvd_refl _), zero_mul]
  have hA : Injective A.transpose.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply int_cast_matrix_rigidity A.transpose n hn _ x hx
    intro c hc
    rw [castT] at hc
    have rel := (reduced_transpose_kernel_iff points (fun t => (triangles t).injective)
      root anchor c).mp hc
    exact (triangle_relation_potential points (fun t => (triangles t).injective)
      (sparse_triangle_unique_pair triangles ht hsparse) root anchor hne nKills c rel).1
  obtain ⟨mb, coeff, ⟨split⟩⟩ := smith_kernel_split A hA n
  rw [remainingPair_card root anchor hne] at mb
  change m ≤ b at mb
  rw [castA, remainingPair_card root anchor hne] at split
  let D := (i : Fin m) → Submodule.torsionBy ℤ (ZMod n) (coeff i)
  obtain ⟨kernel⟩ := rank_three_lifting_obstruction_equiv_kernel M triangles root anchor
    hne hn hsparse hbase
  let e : G ≃ₗ[ℤ] (Fin r → ZMod n) × D := kernel.trans split
  let N := Nat.card {u : I → ZMod g // IsOmissionPotential points anchor u}
  have residual (q : ℕ) [NeZero q] (hq : q ∣ n) (hg : q.gcd 3 = g) :
      Nat.card {y : D // q • y = 0} = N := by
    have h := rank_three_lifting_obstruction_torsion_card M triangles ht anchor hn
      hsparse hbase q hq
    change Nat.card {x : G // q • x = 0} * q ^ m =
      q ^ b * Nat.card {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} at h
    rw [hg, free_prod_torsion_card n r q hnpos hq e.toAddEquiv, mul_right_comm] at h
    change q ^ r * q ^ m * _ = q ^ b * N at h
    have hr : r + m = b := Nat.sub_add_cancel mb
    rw [← pow_add, hr] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (NeZero.pos q)) h
  have nKillsD (x : D) : n • x = 0 := by
    funext i
    exact Subtype.ext (nKills (x i).val)
  have total : Nat.card D = N := by
    rw [← Nat.card_congr (Equiv.subtypeUnivEquiv nKillsD)]
    exact residual n (dvd_refl _) rfl
  have gSus : Nat.card {x : D // g • x = 0} = N :=
    residual g (Nat.gcd_dvd_left n 3) (Nat.gcd_eq_left (Nat.gcd_dvd_right n 3))
  have covers : Surjective (Subtype.val : {x : D // g • x = 0} → D) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨Subtype.val_injective, gSus.trans total.symm⟩).2
  have threeKills (x : D) : 3 • x = 0 := by
    obtain ⟨y, rfl⟩ := covers x
    obtain ⟨a, ha⟩ := Nat.gcd_dvd_right n 3
    change 3 = g * a at ha
    rw [ha, mul_nsmul, y.prop, nsmul_zero]
  let _ : Module (ZMod 3) D := AddCommGroup.zmodModule threeKills
  let s := Module.finrank (ZMod 3) D
  let ternary : D ≃ₗ[ℤ] (Fin s → ZMod 3) :=
    (Module.finBasis (ZMod 3) D).equivFun.toAddEquiv.toIntLinearEquiv
  refine ⟨s, ?_, ⟨e.trans ((LinearEquiv.refl ℤ _).prodCongr ternary)⟩⟩
  change N = 3 ^ s
  rw [← total, Nat.card_congr ternary.toEquiv, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

/-- The actual integral lifting obstruction on the affine plane has nine
cyclic factors of order nine and two of order three. -/
theorem affine_plane_lifting_obstruction_cyclic_factors (M : Matroid (Fin 9))
    (hbase : ∀ B : Finset (Fin 9), M.IsBase (B : Set (Fin 9)) ↔
      B.card = 3 ∧ B ∉ affineOmissions) :
    Nonempty ((JointSaturatedImage (M.comap (id : Fin 9 → Fin 9)) ⧸
      JointImageInSaturation (M.comap (id : Fin 9 → Fin 9))) ≃ₗ[ℤ]
        (Fin 9 → ZMod 9) × (Fin 2 → ZMod 3)) := by
  have sparse : affineOmissions.Pairwise (fun H J => (H ∩ J).card + 2 ≤ 3) := by
    rintro _ ⟨t, rfl⟩ _ ⟨s, rfl⟩ hne
    by_contra! bad
    have hcard : 1 < ((ofFinEmbEquiv (affineTriangle t)).val ∩
      (ofFinEmbEquiv (affineTriangle s)).val).card := by omega
    obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp hcard
    have cover (r : Fin 12) (hi : i ∈ (ofFinEmbEquiv (affineTriangle r)).val)
        (hj : j ∈ (ofFinEmbEquiv (affineTriangle r)).val) :
        covers (affineLines r) i j := by
      obtain ⟨a, ha⟩ := (mem_ofFinEmbEquiv_iff_mem_range (affineTriangle r) i).mp hi
      obtain ⟨b, hb⟩ := (mem_ofFinEmbEquiv_iff_mem_range (affineTriangle r) j).mp hj
      exact ⟨a, b, ha, hb⟩
    have h := affine_pair_unique t s i j hij
      (cover t (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hj).1)
      (cover s (Finset.mem_inter.mp hi).2 (Finset.mem_inter.mp hj).2)
    exact hne (congrArg (fun r => (ofFinEmbEquiv (affineTriangle r)).val) h)
  have ht : Injective affineTriangle := by
    intro t s h
    have h₀ := congrArg (fun e : Fin 3 ↪o Fin 9 => e 0) h
    have h₁ := congrArg (fun e : Fin 3 ↪o Fin 9 => e 1) h
    exact affine_pair_unique t s (affineLines t 0) (affineLines t 1)
      ((affine_triangle_injective t).ne (by decide)) ⟨0, 1, rfl, rfl⟩
      ⟨0, 1, h₀.symm, h₁.symm⟩
  obtain ⟨d, hd, E⟩ := rank_three_lifting_obstruction_cyclic_factors M affineTriangle ht
    0 (by decide) sparse hbase
  change Nat.card {u : Fin 9 → ZMod 3 // IsOmissionPotential affineLines 0 u} = 3 ^ d at hd
  rw [Nat.card_congr (Equiv.subtypeEquivRight affine_compatible_iff),
    affine_plane_potential_card] at hd
  have htwo : d = 2 := Nat.pow_right_injective (by decide : 2 ≤ 3) hd.symm
  subst d
  exact E


end D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials
