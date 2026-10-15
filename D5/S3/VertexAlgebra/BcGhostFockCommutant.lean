/- GID: D5/S3/VertexAlgebra/BcGhostFockCommutant
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostFockCommutant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed infinite ghost Fock annihilator kernel and full mode commutant are scalar. -/

/-
proof_shape: annihilator_kernel: content
proof_shape: mode_commutant_scalar: content
escape_witness: Deletion at an occupied site selects exactly the coefficient of
  its original finite subset. Its sign is a unit over every commutative ring,
  so the common deletion kernel consists precisely of vacuum multiples.
  Commutation puts the vacuum image in that kernel; creation cyclicity then
  propagates its scalar to the entire infinite finite-support carrier.
admission_basis: escape-witness
utility: none; the carrier ranges over all finite subsets of the natural sites
  and the coefficient ring is an arbitrary commutative ring.
-/

import D5.S3.VertexAlgebra.BcGhostFockSupport

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostFockCommutant

open BcGhostFockSupport

noncomputable section

variable {K : Type*} [CommRing K]

private theorem annihilate_vacuum (i : ℕ) :
    annihilate i (vacuum : Fock K) = 0 := by
  simp [vacuum, annihilate, Finsupp.linearCombination_single, annihilateBasis]

private theorem annihilate_coefficient (v : Fock K) (S : Finset ℕ) (i : ℕ)
    (hi : i ∈ S) : (annihilate i v) (S.erase i) = sign i S * v S := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw, mul_add]
  | single U a =>
      by_cases hiU : i ∈ U
      · by_cases hUS : U = S
        · subst U
          simp [annihilate, Finsupp.linearCombination_single, annihilateBasis, hi,
            Finsupp.smul_single, mul_comm]
        · have hne : U.erase i ≠ S.erase i := by
            intro h
            apply hUS
            calc
              U = insert i (U.erase i) := (Finset.insert_erase hiU).symm
              _ = insert i (S.erase i) := congrArg (insert i) h
              _ = S := Finset.insert_erase hi
          simp [annihilate, Finsupp.linearCombination_single, annihilateBasis, hiU,
            Finsupp.smul_single, Ne.symm hUS, Ne.symm hne]
      · have hUS : U ≠ S := by intro h; subst U; exact hiU hi
        simp [annihilate, Finsupp.linearCombination_single, annihilateBasis, hiU,
          Ne.symm hUS]

/-- Over any commutative ring, the simultaneous kernel of all signed deletion
operators on the infinite algebraic Fock space is exactly the vacuum line. -/
theorem annihilator_kernel (v : Fock K) :
    (∀ i : ℕ, annihilate i v = 0) ↔ v = v ∅ • vacuum := by
  classical
  constructor
  · intro hv
    apply Finsupp.ext
    intro S
    by_cases hS : S = ∅
    · subst S
      simp [vacuum]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hcoef : sign (K := K) i S * v S = 0 := by
        rw [← annihilate_coefficient v S i hi, hv i]
        rfl
      have hsign : sign (K := K) i S * sign i S = 1 := by
        rcases neg_one_pow_eq_or K (S.filter fun s => s < i).card with h | h <;>
          simp [sign, h]
      have hzero : v S = 0 := by
        calc
          v S = (sign (K := K) i S * sign i S) * v S := by rw [hsign, one_mul]
          _ = sign i S * (sign i S * v S) := mul_assoc _ _ _
          _ = 0 := by rw [hcoef, mul_zero]
      simp [vacuum, hzero, hS]
  · intro hv i
    rw [hv, map_smul, annihilate_vacuum, smul_zero]

/-- Every linear endomorphism commuting with every actual integer b-mode and
c-mode is the scalar read from the empty-subset coefficient of its vacuum image.
No field, characteristic restriction, truncation or irreducibility premise is used. -/
theorem mode_commutant_scalar (T : Module.End K (Fock K))
    (hb : ∀ m : ℤ, T.comp (b m) = (b m).comp T)
    (hc : ∀ n : ℤ, T.comp (c n) = (c n).comp T) :
    T = (T vacuum) ∅ • LinearMap.id := by
  classical
  have hdel (i : ℕ) : T.comp (annihilate i) = (annihilate i).comp T := by
    by_cases heven : i % 2 = 0
    · have hmode : c (K := K) ((i / 2 : ℕ) + 2) = annihilate i := by
        have hbranch : ¬ ((i / 2 : ℕ) + 2 : ℤ) ≤ 1 := by omega
        have hind : 2 * (((i / 2 : ℕ) + 2 : ℤ) - 2).toNat = i := by omega
        simp only [c, if_neg hbranch, hind]
      rw [← hmode]
      exact hc _
    · have hmode : b (K := K) ((i / 2 : ℕ) - 1) = annihilate i := by
        have hbranch : ¬ ((i / 2 : ℕ) - 1 : ℤ) ≤ -2 := by omega
        have hind : 2 * (((i / 2 : ℕ) - 1 : ℤ) + 1).toNat + 1 = i := by omega
        simp only [b, if_neg hbranch, hind]
      rw [← hmode]
      exact hb _
  have hvac : T vacuum = (T vacuum) ∅ • vacuum := by
    apply (annihilator_kernel _).mp
    intro i
    have h := congrArg (fun A : Module.End K (Fock K) => A vacuum) (hdel i)
    simpa only [LinearMap.comp_apply, annihilate_vacuum, map_zero] using h.symm
  let W : Submodule K (Fock K) := LinearMap.ker (T - (T vacuum) ∅ • LinearMap.id)
  have hW : W = ⊤ := by
    apply creation_cyclic W
    · change T vacuum - (T vacuum) ∅ • vacuum = 0
      exact sub_eq_zero.mpr hvac
    · intro m hm v hv
      change T (b m v) - (T vacuum) ∅ • b m v = 0
      have hTv : T v = (T vacuum) ∅ • v := by
        exact sub_eq_zero.mp (show T v - (T vacuum) ∅ • v = 0 from hv)
      have hcomm := congrArg (fun A : Module.End K (Fock K) => A v) (hb m)
      exact sub_eq_zero.mpr (by
        simpa only [LinearMap.comp_apply, hTv, map_smul] using hcomm)
    · intro n hn v hv
      change T (c n v) - (T vacuum) ∅ • c n v = 0
      have hTv : T v = (T vacuum) ∅ • v := by
        exact sub_eq_zero.mp (show T v - (T vacuum) ∅ • v = 0 from hv)
      have hcomm := congrArg (fun A : Module.End K (Fock K) => A v) (hc n)
      exact sub_eq_zero.mpr (by
        simpa only [LinearMap.comp_apply, hTv, map_smul] using hcomm)
  apply LinearMap.ext
  intro v
  have hv : v ∈ W := by rw [hW]; trivial
  exact sub_eq_zero.mp (show T v - (T vacuum) ∅ • v = 0 from hv)

#print axioms annihilator_kernel
#print axioms mode_commutant_scalar

end

end D5.S3.VertexAlgebra.BcGhostFockCommutant
