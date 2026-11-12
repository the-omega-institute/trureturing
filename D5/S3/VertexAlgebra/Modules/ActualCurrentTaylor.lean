/-
SOURCE_ONLY_UNCOMPILED. No elaboration, kernel, or classification claim.

Actual-current application of the sealed AlgebraicHeisenbergFock candidate.
The sole extra representation premise is pointwise local nilpotence of the
ORIGINAL positive basis currents. No grading or spectral premise is used.

The finite commuting-sum argument is proved below, before constructing
WeylData. In particular nilpotence of an inverse-Gram row is not inferred
by treating local nilpotence as closed under arbitrary sums.

Classical Taylor/Fock argument: the sealed AlgebraicHeisenbergFock source.
Actual mixed-Jacobi/current adapter: the sealed FullJacobiCurrentTransport.
Those sources retain their recorded Apache-2.0 and upstream attribution.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport
import D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Modules.ActualCurrentTaylor

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open FullJacobiCurrentTransport
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

universe u v
variable {K : Type v} [Field K] [CharZero K]
variable {M : Type u} [AddCommGroup M] [Module K M]

/-- A scalar multiple preserves a given pointwise nilpotence exponent. -/
theorem scalar_power_apply (c : K) (A : Module.End K M) (n : ℕ) (v : M) :
    ((c • A) ^ n) v = c ^ n • (A ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.smul_apply,
      map_smul, smul_smul, pow_succ', pow_succ', Module.End.mul_apply]

/-- Pointwise, commuting binary-sum nilpotence. Exponents concern the same
input v; neither endomorphism is required to be globally nilpotent. -/
theorem commuting_add_power_kills (A B : Module.End K M) (h : Commute A B)
    (m n : ℕ) (v : M) (hm : (A ^ m) v = 0) (hn : (B ^ n) v = 0) :
    ((A + B) ^ (m + n)) v = 0 := by
  rw [h.add_pow, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hz : (A ^ k * B ^ (m + n - k)) v = 0 := by
    by_cases hm' : m ≤ k
    · have ha := Module.End.pow_map_zero_of_le hm' hm
      rw [(h.pow_pow k (m + n - k)).eq, Module.End.mul_apply, ha, map_zero]
    · have hb : n ≤ m + n - k := by omega
      rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hb hn, map_zero]
  simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  simpa only [Module.End.mul_apply, nsmul_zero] using congrArg
    (fun z : M => (m + n).choose k • z) hz

/-- A genuine finite commuting-sum bound. The harmless extra 1 covers
the empty family, arbitrary zero exponents, and v=0 uniformly. -/
theorem finite_commuting_sum_power_kills {ι : Type*} (s : Finset ι)
    (A : ι → Module.End K M) (N : ι → ℕ) (v : M)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, Commute (A i) (A j))
    (hkill : ∀ i ∈ s, (A i ^ N i) v = 0) :
    ((∑ i ∈ s, A i) ^ (1 + ∑ i ∈ s, N i)) v = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs := ih
      (fun a ha b hb => hcomm a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_insert_of_mem hb))
      (fun a ha => hkill a (Finset.mem_insert_of_mem ha))
    have hc : Commute (A i) (∑ j ∈ s, A j) := by
      apply Commute.sum_right
      intro j hj
      exact hcomm i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
    have hv := commuting_add_power_kills (A i) (∑ j ∈ s, A j) hc
      (N i) (1 + ∑ j ∈ s, N j) v
      (hkill i (Finset.mem_insert_self _ _)) hs
    simpa only [Finset.sum_insert hi,
      show 1 + (N i + ∑ j ∈ s, N j) = N i + (1 + ∑ j ∈ s, N j) by omega]
      using hv

variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Explicit allowed prerequisite, in the original current notation. -/
def OriginalPositiveNilpotence (J : FullJacobiLatticeModule D M) : Prop :=
  ∀ (i : Fin D.rank) (r : ℕ) (v : M),
    ∃ N : ℕ, (current J i ((r : ℤ) + 1) ^ N) v = 0

variable (J : FullJacobiLatticeModule D M)
variable (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

/-- Concrete exponent for a normalized row, using exponents chosen ONLY
for the finitely many original currents on this input. -/
theorem normalized_row_bound (i : Fin D.rank) (r : ℕ) (v : M)
    (N : Fin D.rank → ℕ)
    (hN : ∀ j, (current J j ((r : ℤ) + 1) ^ N j) v = 0) :
    (annihilation J H i r ^ (1 + ∑ j, N j)) v = 0 := by
  classical
  let c : Fin D.rank → ℂ := fun j => (r + 1 : ℂ)⁻¹ * H i j
  have hrow : annihilation J H i r = ∑ j, c j • current J j ((r : ℤ) + 1) := by
    simp only [annihilation, rowMode, Finset.smul_sum, smul_smul, c]
  rw [hrow]
  apply finite_commuting_sum_power_kills
  · intro j hj k hk
    have hc : Commute (current J j ((r : ℤ) + 1))
        (current J k ((r : ℤ) + 1)) := by
      apply sub_eq_zero.mp
      simpa [show (r : ℤ) + 1 + ((r : ℤ) + 1) ≠ 0 by omega]
        using module_current_heisenberg J j k ((r : ℤ) + 1) ((r : ℤ) + 1)
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul]
    rw [mul_comm (c j) (c k), WeylData.commute_apply _ _ hc w]
  · intro j hj
    rw [scalar_power_apply, hN j, smul_zero]

include hNil in
theorem normalized_locally_nilpotent (i : Fin D.rank) (r : ℕ) (v : M) :
    ∃ N : ℕ, (annihilation J H i r ^ N) v = 0 := by
  classical
  let N : Fin D.rank → ℕ := fun j => Classical.choose (hNil j r v)
  exact ⟨1 + ∑ j, N j, normalized_row_bound J H i r v N
    (fun j => Classical.choose_spec (hNil j r v))⟩

/-- Ungraded actual Weyl data. HG is used for DX. Local nilpotence is
derived above; finite active support comes from actual field truncation. -/
def actualWeyl (hHG : H * gramComplex D = 1) :
    WeylData ℂ (Index D) M where
  X x := creation J x.1 x.2
  D x := annihilation J H x.1 x.2
  xx x y := normalized_XX J x.1 y.1 x.2 y.2
  dd x y := normalized_DD J H x.1 y.1 x.2 y.2
  dx x y v := by
    have h := LinearMap.congr_fun (normalized_DX J H hHG x.1 y.1 x.2 y.2) v
    dsimp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have he : annihilation J H x.1 x.2 (creation J y.1 y.2 v) -
        creation J y.1 y.2 (annihilation J H x.1 x.2 v) =
          if x = y then v else 0 := by
      by_cases hf : x.2 = y.2 <;> by_cases hi : x.1 = y.1 <;>
        simpa [hf, hi, Prod.ext_iff] using h
    by_cases hxy : x = y
    · simpa only [if_pos hxy, add_comm] using sub_eq_iff_eq_add.mp he
    · simpa only [if_neg hxy, zero_add, add_zero] using sub_eq_iff_eq_add.mp he
  nilpotent x v := normalized_locally_nilpotent J hNil H x.1 x.2 v
  active_finite v := finite_active_support J H v

/-- Actual positive-current vacuum, with no zero-current or Zhu condition. -/
def Omega : Submodule ℂ M :=
  ⨅ x : Index D, LinearMap.ker (current J x.1 ((x.2 : ℤ) + 1))

@[simp] theorem mem_Omega (v : M) :
    v ∈ Omega J ↔ ∀ i : Fin D.rank, ∀ r : ℕ, current J i ((r : ℤ) + 1) v = 0 := by
  simp [Omega, LinearMap.mem_ker, Prod.forall]

/-- GH, separately from HG, identifies the two actual common kernels. -/
theorem actualWeyl_vacuum_eq (hHG : H * gramComplex D = 1)
    (hGH : gramComplex D * H = 1) :
    (actualWeyl J hNil H hHG).vacuum = Omega J := by
  ext v
  rw [WeylData.mem_vacuum, mem_Omega]
  change (∀ x : Index D, annihilation J H x.1 x.2 v = 0) ↔ _
  rw [Prod.forall]
  rw [normalized_vacuum_iff J H hGH v]
  constructor
  · intro hv i r
    exact hv i ((r : ℤ) + 1) (by omega)
  · intro hv i n hn
    let r := (n - 1).toNat
    have he : n = (r : ℤ) + 1 := by dsimp [r]; omega
    simpa only [he] using hv i r

variable (hHG : H * gramComplex D = 1)
variable (hGH : gramComplex D * H = 1)

/-- The actual Taylor projection, inherited from the supplied finite proof. -/
def Pi : Module.End ℂ M := (actualWeyl J hNil H hHG).vacuumProjection

include hGH in
theorem Pi_mem (v : M) : Pi J hNil H hHG v ∈ Omega J := by
  rw [← actualWeyl_vacuum_eq J hNil H hHG hGH]
  exact (actualWeyl J hNil H hHG).vacuumProjection_mem v

include hGH in
theorem Pi_fixes (v : M) (hv : v ∈ Omega J) : Pi J hNil H hHG v = v := by
  apply (actualWeyl J hNil H hHG).vacuumProjection_eq_self
  rwa [actualWeyl_vacuum_eq J hNil H hHG hGH]

theorem Pi_creation (i : Fin D.rank) (r : ℕ) (v : M) :
    Pi J hNil H hHG (creation J i r v) = 0 :=
  (actualWeyl J hNil H hHG).vacuumProjection_X (i, r) v

/-- Naturality of the ACTUAL finite Taylor projector, proved using a
common finite active set for v and T v. No nilpotence cutoff is assumed
to be preserved by arbitrary T. -/
theorem commute_Pi (T : Module.End ℂ M)
    (hX : ∀ x : Index D, Commute T (creation J x.1 x.2))
    (hD : ∀ x : Index D, Commute T (annihilation J H x.1 x.2)) :
    Commute T (Pi J hNil H hHG) := by
  let W := actualWeyl J hNil H hHG
  apply LinearMap.ext
  intro v
  let s := W.active v ∪ W.active (T v)
  change T (W.vacuumProjection v) = W.vacuumProjection (T v)
  rw [W.vacuumProjection_eq s v Finset.subset_union_left,
    W.vacuumProjection_eq s (T v) Finset.subset_union_right]
  have hc : Commute T (W.finiteProjection s) := by
    apply Finset.noncommProd_commute
    intro i hi
    exact W.commute_projection i T (hX i) (hD i)
  exact WeylData.commute_apply _ _ hc v

theorem zero_current_commutes_current (i j : Fin D.rank) (n : ℤ) :
    Commute (current J i 0) (current J j n) := by
  apply sub_eq_zero.mp
  simpa using module_current_heisenberg J i j 0 n

theorem zero_current_commutes_Pi (i : Fin D.rank) :
    Commute (current J i 0) (Pi J hNil H hHG) := by
  apply commute_Pi J hNil H hHG
  · intro x
    exact zero_current_commutes_current J i x.1 _
  · intro x
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, annihilation, rowMode, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [WeylData.commute_apply _ _ (zero_current_commutes_current J i j _) v]

/-- Coefficients live on the actual Omega, with both inverse orientations
kept in the telescope. This is a vector/current Fock theorem only. -/
def actualFockEquiv : (Oscillator D ⊗[ℂ] Omega J) ≃ₗ[ℂ] M :=
  (LinearEquiv.lTensor (Oscillator D)
    (LinearEquiv.ofEq (Omega J) (actualWeyl J hNil H hHG).vacuum
      (actualWeyl_vacuum_eq J hNil H hHG hGH).symm)).trans
        (actualWeyl J hNil H hHG).fockEquiv

/-- Explicit finite reconstruction, with no desired spectral conclusion
in any premise. -/
theorem actual_taylor_reconstruction (v : M) :
    (∑ d ∈ Finset.Iic ((actualWeyl J hNil H hHG).jointCutoff v),
      (WeylData.factorial d : ℂ)⁻¹ •
        (actualWeyl J hNil H hHG).creation d
          (Pi J hNil H hHG ((actualWeyl J hNil H hHG).derivative d v))) = v :=
  (actualWeyl J hNil H hHG).taylor_reconstruction v

end D5.S3.VertexAlgebra.Modules.ActualCurrentTaylor
