/- GID: D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.claim; result=D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.result; claim=D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.claim
   digest: The continuous qutrit SIC family is not contained in the finite Clifford-stabilizer rays. -/

import D5.S3.Quantum.Algebra.WeylDisplacement
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic

namespace D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation

open Matrix D5.S3.Observer.WindowRegister D5.S3.Quantum.Algebra.WeylDisplacement
open scoped ComplexConjugate

noncomputable section

/-- The half-period phase in the single-qudit Pauli group. -/
def zeta (d : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / d)

/-- The source's single-qudit Pauli group, including its finite scalar phases. -/
def pauliGroup (d : ℕ) [NeZero d] : Set (Matrix (ZMod d) (ZMod d) ℂ) :=
  Set.range fun t : ZMod 2 × ZMod d × ZMod d × ZMod d =>
    ((-1 : ℂ) ^ t.1.val * zeta d ^ t.2.1.val) • displacement d t.2.2.1 t.2.2.2

/-- Unitary matrices whose conjugation maps the Pauli group onto itself. -/
def cliffordGroup (d : ℕ) [NeZero d] : Set (Matrix (ZMod d) (ZMod d) ℂ) :=
  {U | U ∈ Matrix.unitaryGroup (ZMod d) ℂ ∧
    (fun P => U * P * Uᴴ) '' pauliGroup d = pauliGroup d}

/-- The special Clifford group consists of the determinant-one Clifford matrices. -/
def specialClifford (d : ℕ) [NeZero d] : Set (Matrix (ZMod d) (ZMod d) ℂ) :=
  {U | U ∈ cliffordGroup d ∧ Matrix.det U = 1}

/-- All eigenvalues of all special Clifford matrices. -/
def Lambda (d : ℕ) [NeZero d] : Set ℂ :=
  {μ | ∃ U ∈ specialClifford d, Module.End.HasEigenvalue (Matrix.toLin' U) μ}

/-- The eigenphase extension in the source's convention. -/
def eigenphaseClifford (d : ℕ) [NeZero d] : Set (Matrix (ZMod d) (ZMod d) ℂ) :=
  {V | ∃ μ ∈ Lambda d, ∃ U ∈ specialClifford d, V = μ • U}

/-- The vectors fixed pointwise by every matrix in a set. -/
def invariantSubspace {d : ℕ} [NeZero d]
    (S : Set (Matrix (ZMod d) (ZMod d) ℂ)) : Submodule ℂ (ZMod d → ℂ) :=
  ⨅ U ∈ S, LinearMap.ker (Matrix.toLin' U - LinearMap.id)

/-- Hilbert-space normalization, expressed using the Hermitian dot product. -/
def IsNormalized {d : ℕ} [NeZero d] (ψ : ZMod d → ℂ) : Prop :=
  star ψ ⬝ᵥ ψ = 1

/-- A normalized vector spanning exactly a Clifford-stabilized fixed space. -/
def IsCliffordStabilizerState (d : ℕ) [NeZero d] (ψ : ZMod d → ℂ) : Prop :=
  IsNormalized ψ ∧ ∃ S : Set (Matrix (ZMod d) (ZMod d) ℂ),
    S ⊆ eigenphaseClifford d ∧ invariantSubspace S = Submodule.span ℂ {ψ}

/-- The Weyl-Heisenberg SIC fiducial condition; scalar Weyl phases are immaterial. -/
def IsSICFiducial (d : ℕ) [NeZero d] (ψ : ZMod d → ℂ) : Prop :=
  IsNormalized ψ ∧ ∀ a b : ZMod d, (a, b) ≠ (0, 0) →
    ‖star ψ ⬝ᵥ (displacement d a b *ᵥ ψ)‖ = 1 / Real.sqrt (d + 1)

/-- Every single-qudit SIC fiducial in every prime dimension is Clifford-stabilized. -/
def claim : Prop :=
  ∀ (d : ℕ) (hd : d.Prime),
    letI : NeZero d := ⟨hd.ne_zero⟩
    ∀ ψ : ZMod d → ℂ, IsSICFiducial d ψ → IsCliffordStabilizerState d ψ

/-- The continuous qutrit family, in the computational basis. -/
def qutritFiducial (z : ℂ) : ZMod 3 → ℂ :=
  fun j => if j = 0 then 0 else if j = 1 then (Real.sqrt 2 : ℂ)⁻¹
    else -z * (Real.sqrt 2 : ℂ)⁻¹

private theorem pauliGroup_finite (d : ℕ) [NeZero d] : (pauliGroup d).Finite :=
  Set.finite_range _

private theorem conjugation_eq_commute {d : ℕ} [NeZero d]
    (U V P : Matrix (ZMod d) (ZMod d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (ZMod d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (ZMod d) ℂ)
    (h : U * P * Uᴴ = V * P * Vᴴ) : Commute (Vᴴ * U) P := by
  have hUl : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU
  have hVl : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hV
  have hh := congrArg (fun A => Vᴴ * A * U) h
  have hl : Vᴴ * (U * P * Uᴴ) * U = (Vᴴ * U) * P := by
    calc
      _ = (Vᴴ * U) * P * (Uᴴ * U) := by noncomm_ring
      _ = _ := by rw [hUl, mul_one]
  have hr : Vᴴ * (V * P * Vᴴ) * U = P * (Vᴴ * U) := by
    calc
      _ = (Vᴴ * V) * P * (Vᴴ * U) := by noncomm_ring
      _ = _ := by rw [hVl, one_mul]
  exact hl.symm.trans (hh.trans hr)

private theorem special_same_generators (U V : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hU : U ∈ specialClifford 3) (hV : V ∈ specialClifford 3)
    (hX : U * shiftMatrix 3 * Uᴴ = V * shiftMatrix 3 * Vᴴ)
    (hZ : U * clockMatrix 3 * Uᴴ = V * clockMatrix 3 * Vᴴ) :
    ∃ c : ℂ, c ^ 3 = 1 ∧ U = c • V := by
  obtain ⟨c, hc⟩ := window_commutant_eq_scalars (Vᴴ * U)
    (conjugation_eq_commute U V _ hU.1.1 hV.1.1 hZ)
    (conjugation_eq_commute U V _ hU.1.1 hV.1.1 hX)
  have hVr : V * Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hV.1.1
  have hdet := congrArg Matrix.det hc
  have hroot : c ^ 3 = 1 := by
    simpa [Matrix.scalar, Matrix.det_diagonal, Matrix.det_mul,
      Matrix.det_conjTranspose, hU.2, hV.2] using hdet
  refine ⟨c, hroot, ?_⟩
  calc
    U = V * (Vᴴ * U) := by rw [← mul_assoc, hVr, one_mul]
    _ = V * Matrix.scalar (ZMod 3) c := by rw [← hc]
    _ = c • V := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]

/-- Determinant one leaves only three scalar possibilities in each conjugation fiber. -/
theorem specialClifford_three_finite : (specialClifford 3).Finite := by
  classical
  let f : Matrix (ZMod 3) (ZMod 3) ℂ →
      Matrix (ZMod 3) (ZMod 3) ℂ × Matrix (ZMod 3) (ZMod 3) ℂ :=
    fun U => (U * shiftMatrix 3 * Uᴴ, U * clockMatrix 3 * Uᴴ)
  have hX : shiftMatrix 3 ∈ pauliGroup 3 := by
    refine ⟨(0, 0, 1, 0), ?_⟩
    simp [displacement, show (1 : ZMod 3).val = 1 from rfl]
  have hZ : clockMatrix 3 ∈ pauliGroup 3 := by
    refine ⟨(0, 0, 0, 1), ?_⟩
    simp [displacement, show (1 : ZMod 3).val = 1 from rfl]
  have himage : (f '' specialClifford 3).Finite := by
    apply ((pauliGroup_finite 3).prod (pauliGroup_finite 3)).subset
    rintro _ ⟨U, hU, rfl⟩
    constructor
    · rw [← hU.1.2]
      exact ⟨shiftMatrix 3, hX, rfl⟩
    · rw [← hU.1.2]
      exact ⟨clockMatrix 3, hZ, rfl⟩
  apply Set.Finite.of_finite_fibers f himage
  rintro _ ⟨V, hV, rfl⟩
  let R : Finset ℂ := Polynomial.nthRootsFinset 3 1
  apply (R.finite_toSet.image (fun c => c • V)).subset
  rintro U ⟨hU, hUV⟩
  have heq : f U = f V := hUV
  obtain ⟨c, hc, hUc⟩ := special_same_generators U V hU hV
    (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  exact ⟨c, (Polynomial.mem_nthRootsFinset (by norm_num) 1).mpr hc, hUc.symm⟩

private theorem Lambda_three_finite : (Lambda 3).Finite := by
  have hh := specialClifford_three_finite.biUnion
    (fun U _ => Module.End.finite_hasEigenvalue (Matrix.toLin' U))
  apply hh.subset
  rintro c ⟨U, hU, hc⟩
  exact Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨hU, hc⟩⟩

/-- Both the special group and its eigenphase extension are finite. -/
theorem eigenphaseClifford_three_finite : (eigenphaseClifford 3).Finite := by
  apply ((Lambda_three_finite.prod specialClifford_three_finite).image
    (fun p => p.1 • p.2)).subset
  rintro V ⟨c, hc, U, hU, rfl⟩
  exact ⟨(c, U), ⟨hc, hU⟩, rfl⟩

private theorem normalized_projectors_eq {d : ℕ} [NeZero d]
    (ψ φ : ZMod d → ℂ) (hψ : IsNormalized ψ) (hφ : IsNormalized φ)
    (hspan : Submodule.span ℂ {ψ} = Submodule.span ℂ {φ}) :
    Matrix.vecMulVec ψ (star ψ) = Matrix.vecMulVec φ (star φ) := by
  change star ψ ⬝ᵥ ψ = 1 at hψ
  change star φ ⬝ᵥ φ = 1 at hφ
  have hmem : φ ∈ Submodule.span ℂ {ψ} := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_singleton φ)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hprod : star c * c = 1 := by
    have hh : star (c • ψ) ⬝ᵥ (c • ψ) =
        (star c * c) * (star ψ ⬝ᵥ ψ) := by
      simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hc, hφ] at hh
    simpa only [hψ, mul_one] using hh.symm
  rw [← hc]
  ext i j
  simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul, star_mul]
  calc
    ψ i * star (ψ j) = (star c * c) * (ψ i * star (ψ j)) := by rw [hprod, one_mul]
    _ = c * ψ i * (star (ψ j) * star c) := by ring

/-- Only finitely many normalized rank-one projectors arise from Clifford fixed spaces. -/
theorem stabilizer_projectors_three_finite :
    {P : Matrix (ZMod 3) (ZMod 3) ℂ | ∃ ψ : ZMod 3 → ℂ,
      IsCliffordStabilizerState 3 ψ ∧ P = Matrix.vecMulVec ψ (star ψ)}.Finite := by
  classical
  let A : Set (Matrix (ZMod 3) (ZMod 3) ℂ) :=
    {P | ∃ ψ : ZMod 3 → ℂ,
      IsCliffordStabilizerState 3 ψ ∧ P = Matrix.vecMulVec ψ (star ψ)}
  choose ψ hψ heq using fun P : A => P.property
  choose S hS hray using fun P : A => (hψ P).2
  have hfin : {S : Set (Matrix (ZMod 3) (ZMod 3) ℂ) |
      S ⊆ eigenphaseClifford 3}.Finite := eigenphaseClifford_three_finite.finite_subsets
  let := hfin.to_subtype
  have hinj : Function.Injective
      (fun P : A => (⟨S P, hS P⟩ : {S | S ⊆ eigenphaseClifford 3})) := by
    intro P Q h
    have hs : S P = S Q := congrArg Subtype.val h
    have hspan : Submodule.span ℂ {ψ P} = Submodule.span ℂ {ψ Q} := by
      rw [← hray P, ← hray Q, hs]
    apply Subtype.ext
    rw [heq P, heq Q]
    exact normalized_projectors_eq _ _ (hψ P).1 (hψ Q).1 hspan
  let : Finite A := Finite.of_injective _ hinj
  exact Set.toFinite A

private theorem qutrit_scale_sq :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  rw [← pow_two, inv_pow, hs]
  norm_num

private theorem sum_three (f : ZMod 3 → ℂ) :
    (∑ i, f i) = f 0 + f 1 + f 2 := by
  change (∑ i : Fin 3, f (show ZMod 3 from i)) = _
  rw [Fin.sum_univ_three]
  rfl

private theorem qutrit_normalized (z : ℂ) (hz : ‖z‖ = 1) :
    IsNormalized (qutritFiducial z) := by
  have hzz : star z * z = 1 := by simpa [hz] using RCLike.conj_mul z
  unfold IsNormalized dotProduct
  rw [sum_three]
  norm_num [qutritFiducial.eq_1, show (1 : ZMod 3) ≠ 0 from by decide,
    show (2 : ZMod 3) ≠ 0 from by decide,
    show (2 : ZMod 3) ≠ 1 from by decide, star_mul, star_inv₀]
  simp only [starRingEnd_apply]
  calc
    _ = (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ * (1 + star z * z) := by ring
    _ = 1 := by rw [qutrit_scale_sq, hzz]; norm_num

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The nine displacement words require finite matrix and scalar expansions.
private theorem qutrit_overlap (z : ℂ) (hz : ‖z‖ = 1) (a b : ZMod 3) :
    star (qutritFiducial z) ⬝ᵥ (displacement 3 a b *ᵥ qutritFiducial z) =
      if a = 0 then if b = 0 then 1 else -(1 / 2 : ℂ)
      else if a = 1 then -star z * windowRoot 3 ^ b.val / 2
      else -z * windowRoot 3 ^ (2 * b.val) / 2 := by
  have hzz : star z * z = 1 := by simpa [hz] using RCLike.conj_mul z
  have hw : windowRoot 3 ^ 3 = 1 := (windowRoot_isPrimitiveRoot 3).pow_eq_one
  have hw4 : windowRoot 3 ^ 4 = windowRoot 3 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hw, one_mul]
  have hsum : 1 + windowRoot 3 + windowRoot 3 ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using
      (windowRoot_isPrimitiveRoot 3).geom_sum_eq_zero (by norm_num)
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals
    norm_num [displacement, shiftMatrix, clockMatrix, Matrix.circulant_apply,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, sum_three,
      Matrix.diagonal_apply, Matrix.one_apply, qutritFiducial,
      show (1 : ZMod 3).val = 1 from rfl,
      show (2 : ZMod 3).val = 2 from rfl,
      show (-1 : ZMod 3) = 2 from by decide,
      show (-2 : ZMod 3) = 1 from by decide,
      show (1 : ZMod 3) - 2 = 2 from by decide,
      pow_succ, star_mul, star_inv₀, Fin.isValue,
      show (1 : ZMod 3) ≠ 0 from by decide,
      show (2 : ZMod 3) ≠ 0 from by decide,
      show (2 : ZMod 3) ≠ 1 from by decide,
      show (1 : ZMod 3) ≠ 2 from by decide,
      show (-1 : ZMod 3) ≠ 1 from by decide]
  all_goals
    try simp +decide only [starRingEnd_apply, if_true]
    ring_nf
    simp only [inv_pow, hs]
    first
    | solve | ring
    | solve | linear_combination (1 / 2 : ℂ) * hzz
    | solve | linear_combination (windowRoot 3 ^ 2 / 2) * hzz + (1 / 2 : ℂ) * hsum
    | solve | linear_combination (windowRoot 3 ^ 4 / 2) * hzz +
        (1 / 2 : ℂ) * hsum + (1 / 2 : ℂ) * hw4

/-- Every unit-circle parameter gives a normalized qutrit SIC fiducial. -/
theorem qutritFiducial_isSIC (z : ℂ) (hz : ‖z‖ = 1) :
    IsSICFiducial 3 (qutritFiducial z) := by
  refine ⟨qutrit_normalized z hz, ?_⟩
  intro a b hab
  have hw : ‖windowRoot 3‖ = 1 :=
    (windowRoot_isPrimitiveRoot 3).norm'_eq_one (by norm_num)
  rw [qutrit_overlap z hz a b]
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := by intro h; exact hab (by simp [h])
    norm_num [hb, norm_div]
  · by_cases h1 : a = 1 <;>
      norm_num [ha, h1, norm_div, norm_mul, norm_pow, hw, hz, norm_star]

private theorem qutrit_projector_entry (z : ℂ) :
    Matrix.vecMulVec (qutritFiducial z) (star (qutritFiducial z))
      (1 : ZMod 3) (2 : ZMod 3) = -star z / 2 := by
  simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply]
  norm_num [qutritFiducial, show (1 : ZMod 3) ≠ 0 from by decide,
    show (2 : ZMod 3) ≠ 0 from by decide,
    show (2 : ZMod 3) ≠ 1 from by decide, star_mul, star_inv₀]
  simp only [starRingEnd_apply]
  calc
    _ = -star z * ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) := by ring
    _ = _ := by rw [qutrit_scale_sq]; ring

/-- The off-diagonal entry remembers the parameter, even without a norm hypothesis. -/
theorem qutrit_projector_injective : Function.Injective
    (fun z : ℂ => Matrix.vecMulVec (qutritFiducial z) (star (qutritFiducial z))) := by
  intro z w h
  have hh : Matrix.vecMulVec (qutritFiducial z) (star (qutritFiducial z)) 1 2 =
      Matrix.vecMulVec (qutritFiducial w) (star (qutritFiducial w)) 1 2 :=
    congrArg (fun P : Matrix (ZMod 3) (ZMod 3) ℂ => P 1 2) h
  rw [qutrit_projector_entry, qutrit_projector_entry] at hh
  have hs : star z = star w := by linear_combination -2 * hh
  exact star_injective hs

private theorem unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  intro hfin
  apply Real.range_cos_infinite
  apply (hfin.image Complex.re).subset
  rintro _ ⟨t, rfl⟩
  exact ⟨Complex.exp (t * Complex.I), Complex.norm_exp_ofReal_mul_I t,
    Complex.exp_ofReal_mul_I_re t⟩

/-- The qutrit family has infinitely many projectors and the Clifford fixed rays are finite. -/
theorem result : ¬ claim := by
  intro hclaim
  have hall (z : ℂ) (hz : ‖z‖ = 1) :
      IsCliffordStabilizerState 3 (qutritFiducial z) :=
    hclaim 3 (by norm_num) _ (qutritFiducial_isSIC z hz)
  have hfamily :
      ((fun z : ℂ => Matrix.vecMulVec (qutritFiducial z) (star (qutritFiducial z))) ''
        {z : ℂ | ‖z‖ = 1}).Finite := by
    apply stabilizer_projectors_three_finite.subset
    rintro P ⟨z, hz, rfl⟩
    exact ⟨qutritFiducial z, hall z hz, rfl⟩
  exact (unit_circle_infinite.image qutrit_projector_injective.injOn) hfamily

#print axioms result

end
end D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation
