/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pDerivedAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pDerivedAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The rational derived action gives charge inversion and real cubic fixed rank sixteen. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import D5.S3.VertexAlgebra.Lattice.Automorphisms.ReducibleActionWeightTwo
import D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.PureCubicFixedRank
import Mathlib.RepresentationTheory.Irreducible
import OmegaBuild.Commands

/-!
Nebe, arXiv:1212.0865, Theorem 3.6, proof (B), gives the rational
irreducibility of the derived action of `SL₂(23) × C₃`. Proposition 4.8
gives the allowed fixed ranks for the order-three isometries of P48p.
The corresponding group, representation, and rank data are explicit premises.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pDerivedAction

open Automorphisms.ReducibleActionWeightTwo (realChargeRepresentation)
open LatticeGeneratingFieldLocality (LatticeData Charge unitCharge)
open PureCubicFixedRank (pure_cubic_fixed_ranks_eq_sixteen)
open D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound (rank_map_algebraMap)

open private realMixingMatrix from
  D5.S3.VertexAlgebra.Lattice.Automorphisms.ReducibleActionWeightTwo

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 23)
local notation "fixedCartan(" D ", " charge ", " g ")" =>
  LinearMap.ker (realChargeRepresentation D (charge g) - 1)

private theorem central_fixed_ker_eq_bot
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ G V) [ρ.IsIrreducible] (hFaithful : Function.Injective ρ)
    {z : G} (hz : z ∈ Subgroup.center G) (hzOne : z ≠ 1) :
    LinearMap.ker (ρ z - 1) = ⊥ := by
  let f : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := ρ z - 1
      isIntertwining' := fun g => by
        change (ρ z - 1) * ρ g = ρ g * (ρ z - 1)
        rw [sub_mul, mul_sub, one_mul, mul_one, ← map_mul, ← map_mul,
          Subgroup.mem_center_iff.mp hz g] }
  have hProper : f.ker ≠ ⊤ := by
    intro h
    have hTop : LinearMap.ker (ρ z - 1) = ⊤ :=
      congrArg (Subrepresentation.toSubmodule (ρ := ρ)) h
    exact hzOne (hFaithful ((sub_eq_zero.mp (LinearMap.ker_eq_top.mp hTop)).trans
      (map_one ρ).symm))
  exact congrArg (Subrepresentation.toSubmodule (ρ := ρ))
    ((eq_bot_or_eq_top f.ker).resolve_right hProper)

private theorem eq_zero_of_mul_eq_zero_of_ker_eq_bot
    {V : Type*} [AddCommGroup V] [Module ℚ V] {F T : Module.End ℚ V}
    (h : LinearMap.ker F = ⊥) (hProduct : F * T = 0) : T = 0 := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ker_eq_bot.mp h
  simpa only [Module.End.mul_apply, LinearMap.zero_apply, map_zero] using
    congrArg (fun E : Module.End ℚ V => E v) hProduct

private theorem fixed_rank_eq_of_matrix_cast {n : ℕ}
    (A : Module.End ℚ (Fin n → ℚ)) (B : Module.End ℝ (Fin n → ℝ))
    (h : (LinearMap.toMatrix' A).map (algebraMap ℚ ℝ) = LinearMap.toMatrix' B) :
    Module.finrank ℚ (LinearMap.ker (A - 1)) = Module.finrank ℝ (LinearMap.ker (B - 1)) := by
  have hMatrix : (LinearMap.toMatrix' (A - 1)).map (algebraMap ℚ ℝ) =
      LinearMap.toMatrix' (B - 1) := by
    change (algebraMap ℚ ℝ).mapMatrix (LinearMap.toMatrixAlgEquiv' (A - 1)) =
      LinearMap.toMatrixAlgEquiv' (B - 1)
    simp only [map_sub, map_one]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M - 1) h
  have matrix_rank {K : Type} [Field K] (F : Module.End K (Fin n → K)) :
      (LinearMap.toMatrix' F).rank = Module.finrank K (LinearMap.range F) := by
    have hLinear : (LinearMap.toMatrix' F).mulVecLin = F :=
      (Matrix.toLin'_apply' (LinearMap.toMatrix' F)).symm.trans (Matrix.toLin'_toMatrix' F)
    exact congrArg
      (fun T : Module.End K (Fin n → K) => Module.finrank K (LinearMap.range T)) hLinear
  have hRank : Module.finrank ℝ (LinearMap.range (B - 1)) =
      Module.finrank ℚ (LinearMap.range (A - 1)) := calc
    _ = (LinearMap.toMatrix' (B - 1)).rank := (matrix_rank (K := ℝ) (B - 1)).symm
    _ = ((LinearMap.toMatrix' (A - 1)).map (algebraMap ℚ ℝ)).rank :=
      congrArg Matrix.rank hMatrix.symm
    _ = (LinearMap.toMatrix' (A - 1)).rank := rank_map_algebraMap (LinearMap.toMatrix' (A - 1))
    _ = _ := matrix_rank (K := ℚ) (A - 1)
  have hQ := LinearMap.finrank_range_add_finrank_ker (A - 1)
  have hR := LinearMap.finrank_range_add_finrank_ker (B - 1)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hQ hR
  omega

/-- A faithful, irreducible rational derived action gives the negation and cubic
rank premises of the P48p extension obstruction. Each of the three elements
in the coset of a pure cubic has order three and real fixed rank sixteen. -/
theorem p48p_derived_action_charge_inversion_and_cubic_rank
    (D : LatticeData) (hRank : D.rank = 48)
    {H : Type*} [Group H] (N L : Subgroup H) (hNL : N ≤ L)
    (φ : N →* SL23) (hφ : Function.Injective φ)
    (charge : H →* Multiplicative (AddAut (Charge D))) (hCharge : Function.Injective charge)
    (ρ : Representation ℚ L (Fin D.rank → ℚ)) [ρ.IsIrreducible]
    (hρ : ∀ (g : L) (a : Charge D), ρ g (fun i => (a i : ℚ)) =
      fun i => ((charge (g : H)).toAdd a i : ℚ))
    (s : N) (hs : orderOf s = 2) (hsImage : φ s = -(1 : SL23))
    (hsCentral : Subgroup.inclusion hNL s ∈ Subgroup.center L)
    (c : L) (hc : orderOf c = 3) (hcCentral : c ∈ Subgroup.center L)
    (hcOutside : (c : H) ∉ N)
    (hAllowed : ∀ g : L, orderOf g = 3 →
      Module.finrank ℝ (fixedCartan(D, charge, (g : H))) = 0 ∨
      Module.finrank ℝ (fixedCartan(D, charge, (g : H))) = 16) :
    (∀ n : N, φ n = -(1 : SL23) → ∀ a : Charge D, (charge (n : H)).toAdd a = -a) ∧
      ∀ a : N, orderOf a = 3 →
        ∀ g ∈ ({Subgroup.inclusion hNL a, Subgroup.inclusion hNL a * c,
          Subgroup.inclusion hNL a * c ^ 2} : Set L),
          orderOf g = 3 ∧ Module.finrank ℝ (fixedCartan(D, charge, (g : H))) = 16 ∧
          fixedCartan(D, charge, (g : H)) ≠ ⊥ ∧ fixedCartan(D, charge, (g : H)) ≠ ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hFaithful : Function.Injective ρ := by
    intro x y hxy
    apply Subtype.ext
    apply hCharge
    apply AddEquiv.ext
    intro a
    funext i
    have h := congrFun (congrArg (fun T : Module.End ℚ (Fin D.rank → ℚ) =>
      T (fun j => (a j : ℚ))) hxy) i
    change ρ x (fun j => (a j : ℚ)) i = ρ y (fun j => (a j : ℚ)) i at h
    rw [hρ, hρ] at h
    exact Int.cast_injective (α := ℚ) h
  let S := ρ (Subgroup.inclusion hNL s)
  let C := ρ c
  have hsOrder := (orderOf_injective (Subgroup.inclusion hNL)
    (Subgroup.inclusion_injective hNL) s).trans hs
  have hSCases := orderOf_eq_prime_iff (p := 2) |>.mp hsOrder
  have hCCases := orderOf_eq_prime_iff (p := 3) |>.mp hc
  have hSsq : S ^ 2 = 1 := by
    dsimp [S]
    rw [← map_pow, hSCases.1, map_one]
  have hCcube : C ^ 3 = 1 := by
    dsimp [C]
    rw [← map_pow, hCCases.1, map_one]
  have hSneg : S = -1 := by
    apply eq_neg_of_add_eq_zero_left
    apply eq_zero_of_mul_eq_zero_of_ker_eq_bot
      (central_fixed_ker_eq_bot ρ hFaithful hsCentral hSCases.2)
    change (S - 1) * (S + 1) = 0
    simp only [mul_add, sub_mul, mul_one, one_mul, ← pow_two, hSsq]
    abel
  have hCnorm : 1 + C + C ^ 2 = 0 := by
    apply eq_zero_of_mul_eq_zero_of_ker_eq_bot
      (central_fixed_ker_eq_bot ρ hFaithful hcCentral hCCases.2)
    calc
      (C - 1) * (1 + C + C ^ 2) = C ^ 3 - 1 := by
        simp only [mul_add, sub_mul, mul_one, one_mul, ← pow_two, ← pow_succ']
        abel
      _ = 0 := sub_eq_zero.mpr hCcube
  refine ⟨?_, ?_⟩
  · intro n hn a
    rw [hφ (hn.trans hsImage.symm)]
    funext i
    have h := congrFun (hρ (Subgroup.inclusion hNL s) a) i
    change S (fun j => (a j : ℚ)) i = ((charge (s : H)).toAdd a i : ℚ) at h
    rw [hSneg] at h
    change -(a i : ℚ) = ((charge (s : H)).toAdd a i : ℚ) at h
    exact_mod_cast h.symm
  · intro a ha
    let aL := Subgroup.inclusion hNL a
    have haOrder : orderOf aL = 3 :=
      (orderOf_injective (Subgroup.inclusion hNL) (Subgroup.inclusion_injective hNL) a).trans ha
    have haCube := (orderOf_eq_prime_iff (p := 3)).mp haOrder |>.1
    have hComm : Commute aL c := Subgroup.mem_center_iff.mp hcCentral aL
    have hcSqOutside : ((c ^ 2 : L) : H) ∉ N := by
      intro h
      have hcFour : (c ^ 2) ^ 2 = c := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_succ, hCCases.1, one_mul]
      apply hcOutside
      rw [← hcFour]
      exact N.pow_mem h 2
    have hTwistOrder (b : L) (hCube : b ^ 3 = 1) (hCommute : Commute aL b)
        (hOutside : (b : H) ∉ N) : orderOf (aL * b) = 3 := by
      apply (orderOf_eq_prime_iff (p := 3)).mpr
      refine ⟨by rw [hCommute.mul_pow, haCube, hCube, one_mul], ?_⟩
      intro h
      have hProduct : (a : H) * (b : H) = 1 := congrArg L.subtype h
      exact hOutside ((eq_inv_of_mul_eq_one_right hProduct).symm ▸ N.inv_mem a.property)
    have hCosetOrder : ∀ g ∈ ({aL, aL * c, aL * c ^ 2} : Set L), orderOf g = 3 := by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact haOrder
      · exact hTwistOrder c hCCases.1 hComm hcOutside
      · exact hTwistOrder (c ^ 2) (by rw [pow_right_comm, hCCases.1, one_pow])
          (hComm.pow_right 2) hcSqOutside
    have hRankCast (g : L) : Module.finrank ℚ (LinearMap.ker (ρ g - 1)) =
        Module.finrank ℝ (fixedCartan(D, charge, (g : H))) := by
      apply fixed_rank_eq_of_matrix_cast
      change (LinearMap.toMatrix' (ρ g)).map (algebraMap ℚ ℝ) =
        LinearMap.toMatrix' (Matrix.toLin' (realMixingMatrix D (charge (g : H)).toAdd))
      rw [LinearMap.toMatrix'_toLin']
      ext i j
      have hUnit : (fun k => (unitCharge D j k : ℚ)) = Pi.single j 1 := by
        ext k
        simp [unitCharge, Pi.single_apply, eq_comm]
      have h := congrFun (hρ g (unitCharge D j)) i
      simpa [Matrix.map_apply, LinearMap.toMatrix'_apply, realMixingMatrix, ← hUnit] using
        congrArg (algebraMap ℚ ℝ) h
    have hRankQ : Module.finrank ℚ (Fin D.rank → ℚ) = 48 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hRank]
    have hRankR : Module.finrank ℝ (Fin D.rank → ℝ) = 48 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hRank]
    have hAllowedQ (g : L) (hg : g ∈ ({aL, aL * c, aL * c ^ 2} : Set L)) :
        Module.finrank ℚ (LinearMap.ker (ρ g - 1)) = 0 ∨
        Module.finrank ℚ (LinearMap.ker (ρ g - 1)) = 16 := by
      rw [hRankCast]
      exact hAllowed g (hCosetOrder g hg)
    have hCosetRanks := pure_cubic_fixed_ranks_eq_sixteen (ρ aL) C
      (by rw [← map_pow, haCube, map_one]) hCcube (hComm.map ρ) hCnorm hRankQ (by
        intro T hT
        have hImage : ρ '' ({aL, aL * c, aL * c ^ 2} : Set L) =
            ({ρ aL, ρ aL * C, ρ aL * C ^ 2} : Set (Module.End ℚ (Fin D.rank → ℚ))) := by
          simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_pow, C]
        rw [← hImage] at hT
        obtain ⟨g, hg, rfl⟩ := hT
        exact hAllowedQ g hg)
    intro g hg
    have hRealRank : Module.finrank ℝ (fixedCartan(D, charge, (g : H))) = 16 := by
      rw [← hRankCast]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hCosetRanks.1
      · rw [show ρ (aL * c) = ρ aL * C from map_mul ρ _ _]
        exact hCosetRanks.2.1
      · rw [show ρ (aL * c ^ 2) = ρ aL * C ^ 2 by rw [map_mul, map_pow]]
        exact hCosetRanks.2.2
    refine ⟨hCosetOrder g hg, hRealRank, ?_, ?_⟩
    · intro h
      rw [h, finrank_bot] at hRealRank
      omega
    · intro h
      rw [h, finrank_top, hRankR] at hRealRank
      omega

#print axioms p48p_derived_action_charge_inversion_and_cubic_rank

end D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pDerivedAction
