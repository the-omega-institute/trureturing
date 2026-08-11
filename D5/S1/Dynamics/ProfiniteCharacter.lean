/- GID: D5/S1/Dynamics/ProfiniteCharacter
   generality: I
   mirror-B: D5/B/S1/Dynamics/ProfiniteCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continuous profinite-integer characters factor through one finite residue coordinate. -/

import D5.S1.Dynamics.ProfiniteIntegers

namespace D5.S1.Dynamics.ProfiniteCharacter

open D5.S1.Dynamics
open Filter Function Real Set

private instance : Zero ProfiniteIntegers :=
  ⟨⟨0, by intro m n h; simp⟩⟩

private instance : Add ProfiniteIntegers :=
  ⟨fun x y => ⟨x.1 + y.1, by
    intro m n h
    simp only [Pi.add_apply, map_add, x.2 h, y.2 h]⟩⟩

private instance : Neg ProfiniteIntegers :=
  ⟨fun x => ⟨-x.1, by
    intro m n h
    simp only [Pi.neg_apply, map_neg, x.2 h]⟩⟩

private instance : AddCommGroup ProfiniteIntegers where
  add := (· + ·)
  add_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  zero := 0
  zero_add _ := Subtype.ext (zero_add _)
  add_zero _ := Subtype.ext (add_zero _)
  neg := Neg.neg
  neg_add_cancel _ := Subtype.ext (neg_add_cancel _)
  add_comm _ _ := Subtype.ext (add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Projection to the residue modulo `m + 1`. -/
def residueProjection (m : ℕ) : ProfiniteIntegers →ₜ+ ZMod (m + 1) where
  toFun x := x.1 m
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun :=
    (continuous_apply m).comp continuous_subtype_val

private theorem residueProjection_surjective (m : ℕ) :
    Surjective (residueProjection m) := by
  intro r
  refine ⟨ProfiniteIntegers.natEmbedding r.val, ?_⟩
  change (r.val : ZMod (m + 1)) = r
  exact ZMod.natCast_zmod_val r

private def commonModulus (indices : Finset ℕ) : ℕ :=
  indices.prod (fun m => m + 1)

private theorem commonModulus_pos (indices : Finset ℕ) :
    0 < commonModulus indices := by
  exact Finset.prod_pos fun m _ => Nat.zero_lt_succ m

private def commonIndex (indices : Finset ℕ) : ℕ :=
  commonModulus indices - 1

private theorem commonIndex_succ (indices : Finset ℕ) :
    commonIndex indices + 1 = commonModulus indices := by
  exact Nat.sub_add_cancel (commonModulus_pos indices)

private theorem divides_commonIndex {indices : Finset ℕ} {m : ℕ}
    (hm : m ∈ indices) : m + 1 ∣ commonIndex indices + 1 := by
  rw [commonIndex_succ]
  exact Finset.dvd_prod_of_mem (fun k : ℕ => k + 1) hm

private theorem exists_coordinate_kernel_subset {neighborhood : Set ProfiniteIntegers}
    (hneighborhood : neighborhood ∈ nhds (0 : ProfiniteIntegers)) :
    ∃ m : ℕ, (residueProjection m).toAddMonoidHom.ker ≤ neighborhood := by
  change neighborhood ∈ @nhds ProfiniteIntegers
    (TopologicalSpace.induced Subtype.val
      (inferInstance : TopologicalSpace ResidueFamily)) 0 at hneighborhood
  rw [mem_nhds_induced] at hneighborhood
  rcases hneighborhood with ⟨ambient, hambient, hsubset⟩
  classical
  simp only [nhds_pi, Filter.mem_pi'] at hambient
  rcases hambient with ⟨indices, coordinateSets, hzero, hcoordinateSets⟩
  refine ⟨commonIndex indices, ?_⟩
  intro x hx
  apply hsubset
  apply hcoordinateSets
  intro m hm
  have hcompat := x.2 (divides_commonIndex hm)
  have hcoordinate : x.1 m = 0 := by
    change x.1 (commonIndex indices) = 0 at hx
    rw [hx] at hcompat
    simpa using hcompat.symm
  rw [hcoordinate]
  exact mem_of_mem_nhds (hzero m)

private theorem exists_coordinate_kernel_le_character_kernel
    (chi : ProfiniteIntegers →ₜ+ UnitAddCircle) :
    ∃ m : ℕ,
      (residueProjection m).toAddMonoidHom.ker ≤ chi.toAddMonoidHom.ker := by
  let neighborhood : Set ProfiniteIntegers :=
    {x | AddCircle.toCircle (chi x) ∈ Circle.centeredArc (Real.pi / 2)}
  have hopen : IsOpen neighborhood := by
    exact Circle.isOpen_centeredArc (Real.pi / 2) |>.preimage
      (AddCircle.continuous_toCircle.comp chi.continuous_toFun)
  have hzero : (0 : ProfiniteIntegers) ∈ neighborhood := by
    change AddCircle.toCircle (chi (0 : ProfiniteIntegers)) ∈
      Circle.centeredArc (Real.pi / 2)
    rw [show chi (0 : ProfiniteIntegers) = 0 by simp, AddCircle.toCircle_zero]
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  rcases exists_coordinate_kernel_subset (hopen.mem_nhds hzero) with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro x hx
  rw [AddMonoidHom.mem_ker]
  apply AddCircle.injective_toCircle one_ne_zero
  simp only [AddCircle.toCircle_zero]
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n hn
  have hnx : n • x ∈ (residueProjection m).toAddMonoidHom.ker := by
    rw [AddMonoidHom.mem_ker, map_nsmul, AddMonoidHom.mem_ker.mp hx, nsmul_zero]
  have hmem := hm hnx
  change AddCircle.toCircle (chi (n • x)) ∈
    Circle.centeredArc (Real.pi / 2) at hmem
  rw [map_nsmul, AddCircle.toCircle_nsmul] at hmem
  exact hmem

private theorem finite_character_classification {N : ℕ} [NeZero N]
    (chi : ZMod N →+ UnitAddCircle) :
    ∃ k : ZMod N, ∀ x : ZMod N, chi x = ZMod.toAddCircle (k * x) := by
  have htorsion : N • chi (1 : ZMod N) = 0 := by
    rw [← map_nsmul]
    simp
  rcases (AddCircle.nsmul_eq_zero_iff (NeZero.pos N)).mp htorsion with
    ⟨k, hkN, hk⟩
  have hone : chi (1 : ZMod N) = ZMod.toAddCircle (k : ZMod N) := by
    rw [ZMod.toAddCircle_natCast]
    simpa using hk.symm
  refine ⟨(k : ZMod N), ?_⟩
  intro x
  rcases ZMod.intCast_surjective x with ⟨a, rfl⟩
  calc
    chi (a : ZMod N) = a • chi (1 : ZMod N) := by
      rw [← map_zsmul]
      simp
    _ = a • ZMod.toAddCircle (k : ZMod N) := by rw [hone]
    _ = ZMod.toAddCircle (a • (k : ZMod N)) := by rw [map_zsmul]
    _ = ZMod.toAddCircle ((k : ZMod N) * (a : ZMod N)) := by
      congr 1
      simp [zsmul_eq_mul, mul_comm]

/-- Every continuous character of the compatible-residue profinite integers
is already a character of one finite residue coordinate. -/
theorem continuous_character_factors_through_residue
    (chi : ProfiniteIntegers →ₜ+ UnitAddCircle) :
    ∃ (m : ℕ) (k : ZMod (m + 1)),
      ∀ x : ProfiniteIntegers,
        chi x = ZMod.toAddCircle (k * (residueProjection m x)) := by
  rcases exists_coordinate_kernel_le_character_kernel chi with ⟨m, hker⟩
  let finiteCharacter : ZMod (m + 1) →+ UnitAddCircle :=
    (residueProjection m).toAddMonoidHom.liftOfSurjective
      (residueProjection_surjective m) ⟨chi.toAddMonoidHom, hker⟩
  have hfactor (x : ProfiniteIntegers) :
      finiteCharacter (residueProjection m x) = chi x := by
    exact AddMonoidHom.liftOfRightInverse_comp_apply
      (residueProjection m).toAddMonoidHom
      (Function.surjInv (residueProjection_surjective m))
      (Function.rightInverse_surjInv (residueProjection_surjective m))
      ⟨chi.toAddMonoidHom, hker⟩ x
  rcases finite_character_classification finiteCharacter with ⟨k, hk⟩
  refine ⟨m, k, fun x => ?_⟩
  exact (hfactor x).symm.trans (hk (residueProjection m x))

end D5.S1.Dynamics.ProfiniteCharacter
