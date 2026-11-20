/- GID: D5/S3/Quantum/AURICOmega/TangentInvariantForms
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TangentInvariantForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Invariant bilinear forms on pure quaternions under unit quaternion conjugations. -/

import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.IsRealClosed.Real
import D5.S3.QuadraticForms.OddDimensionZeroDivisor
import D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Bilinear forms on the pure quaternions that are invariant under conjugation by unit
quaternions.

For a family `S` of unit quaternions, uniqueness of invariant forms up to a factor is equivalent
to irreducibility of the conjugation action of `S` on the pure quaternions, for arbitrary and for
symmetric forms. The conjugations by all unit quaternions act irreducibly. A single conjugation
by `u` with `u.re ≠ 0` and `u.im ≠ 0` (a rotation through an angle outside `πℤ` about `u.im`)
leaves exactly the three-parameter family `α ⟪x, y⟫ + β ⟪n, x⟫ ⟪n, y⟫ + γ ⟪n, x * y⟫`,
`n = u.im`, invariant. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.TangentInvariantForms

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
open D5.S3.QuadraticForms.OddDimensionZeroDivisor

/-! ### Conjugation by a unit quaternion -/

private lemma re_conj {q : ℍ[ℝ]} (hq : star q * q = 1) (z : ℍ[ℝ]) :
    (q * z * star q).re = z.re := by
  have h := congrArg QuaternionAlgebra.re hq
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    QuaternionAlgebra.re_one] at h ⊢
  linear_combination z.re * h

private lemma cancel_left {q : ℍ[ℝ]} (hq : star q * q = 1) (z : ℍ[ℝ]) :
    star q * (q * z) = z := by
  rw [← mul_assoc, hq, one_mul]

private lemma inner_conj {q : ℍ[ℝ]} (hq : star q * q = 1) (z w : ℍ[ℝ]) :
    ⟪q * z * star q, q * w * star q⟫_ℝ = ⟪z, w⟫_ℝ := by
  rw [Quaternion.inner_def, Quaternion.inner_def, star_mul, star_mul, star_star]
  have : q * z * star q * (q * (star w * star q)) = q * (z * star w) * star q := by
    simp only [mul_assoc, cancel_left hq]
  rw [this, re_conj hq]

private lemma conj_mul_conj {q : ℍ[ℝ]} (hq : star q * q = 1) (z w : ℍ[ℝ]) :
    q * z * star q * (q * w * star q) = q * (z * w) * star q := by
  simp only [mul_assoc, cancel_left hq]

/-- The conjugation by `star q` undoes the conjugation by `q`. -/
private lemma conj_star_conj {q : ℍ[ℝ]} (hq : q * star q = 1) (z : ℍ[ℝ]) :
    q * (star q * z * q) * star q = z := by
  simp only [mul_assoc, hq, mul_one]
  rw [← mul_assoc, hq, one_mul]

private lemma inner_conj_left (u : unitary ℍ[ℝ]) (p y : ℍ[ℝ]) :
    ⟪(u : ℍ[ℝ]) * p * star (u : ℍ[ℝ]), y⟫_ℝ =
      ⟪p, star (u : ℍ[ℝ]) * y * (u : ℍ[ℝ])⟫_ℝ := by
  conv_lhs => rw [← conj_star_conj (Unitary.mul_star_self_of_mem u.2) y]
  exact inner_conj (Unitary.star_mul_self_of_mem u.2) _ _

/-! ### Pure quaternions -/

private def qI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
private def qJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
private def qK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

private lemma eq_sum_of_re_eq_zero {y : ℍ[ℝ]} (hy : y.re = 0) :
    y = y.imI • qI + y.imJ • qJ + y.imK • qK := by
  ext <;> simp [qI, qJ, qK, hy]

private lemma eq_zero_of_inner_pure {d : ℍ[ℝ]} (hd : d.re = 0)
    (h : ∀ y : ℍ[ℝ], y.re = 0 → ⟪d, y⟫_ℝ = 0) : d = 0 :=
  inner_self_eq_zero.1 (h d hd)

/-- The pure quaternions as a submodule. -/
private abbrev pureSub : Submodule ℝ ℍ[ℝ] := LinearMap.ker (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))

private lemma mem_pure {x : ℍ[ℝ]} : x ∈ pureSub ↔ x.re = 0 := by
  simp [pureSub]

private lemma finrank_pure : Module.finrank ℝ pureSub = 3 := by
  show Module.finrank ℝ (LinearMap.ker (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))) = 3
  have hsurj : Function.Surjective (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) :=
    fun r => ⟨(r : ℍ[ℝ]), by simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1))
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at h
  have h4 : Module.finrank ℝ ℍ[ℝ,-1,0,-1] = 4 := QuaternionAlgebra.finrank_eq_four _ _ _
  omega

/-! ### The operator of a bilinear form on the pure quaternions -/

/-- `opOf B x` is the pure quaternion with `⟪opOf B x, y⟫ = B x y` for pure `y`. -/
private def opOf (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] :=
  (B.flip qI).smulRight qI + (B.flip qJ).smulRight qJ + (B.flip qK).smulRight qK

private lemma opOf_apply (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) (x : ℍ[ℝ]) :
    opOf B x = B x qI • qI + B x qJ • qJ + B x qK • qK := rfl

private lemma re_opOf (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) (x : ℍ[ℝ]) : (opOf B x).re = 0 := by
  simp [opOf_apply, qI, qJ, qK]

private lemma inner_opOf (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) (x : ℍ[ℝ]) {y : ℍ[ℝ]}
    (hy : y.re = 0) : ⟪opOf B x, y⟫_ℝ = B x y := by
  conv_rhs => rw [eq_sum_of_re_eq_zero hy]
  simp only [map_add, map_smul, smul_eq_mul, opOf_apply, inner_eq_components]
  simp [qI, qJ, qK, hy]
  ring

/-- Invariance of `B` on pure quaternions under conjugation by `u`. -/
private def Inv (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) (u : unitary ℍ[ℝ]) : Prop :=
  ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
    B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y

private lemma re_conj_unit (u : unitary ℍ[ℝ]) (z : ℍ[ℝ]) :
    ((u : ℍ[ℝ]) * z * star (u : ℍ[ℝ])).re = z.re :=
  re_conj (Unitary.star_mul_self_of_mem u.2) z

private lemma re_conj_star_unit (u : unitary ℍ[ℝ]) (z : ℍ[ℝ]) :
    (star (u : ℍ[ℝ]) * z * (u : ℍ[ℝ])).re = z.re := by
  have h : star (star (u : ℍ[ℝ])) * star (u : ℍ[ℝ]) = 1 := by
    rw [star_star]; exact Unitary.mul_star_self_of_mem u.2
  simpa only [star_star] using re_conj h z

/-- The operator of an invariant form commutes with the conjugation on pure quaternions. -/
private lemma opOf_conj (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) (u : unitary ℍ[ℝ]) (hB : Inv B u)
    {x : ℍ[ℝ]} (hx : x.re = 0) :
    opOf B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) =
      (u : ℍ[ℝ]) * opOf B x * star (u : ℍ[ℝ]) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_inner_pure ?_ fun y hy => ?_
  · rw [QuaternionAlgebra.re_sub, re_opOf, re_conj_unit, re_opOf, sub_zero]
  · have hy' : (star (u : ℍ[ℝ]) * y * (u : ℍ[ℝ])).re = 0 := by rw [re_conj_star_unit, hy]
    rw [inner_sub_left, inner_opOf _ _ hy, inner_conj_left, inner_opOf _ _ hy']
    have h := hB x _ hx hy'
    rw [conj_star_conj (Unitary.mul_star_self_of_mem u.2) y] at h
    rw [h, sub_self]

/-! ### Uniqueness of invariant forms and irreducibility -/

private lemma star_conj_conj (u : unitary ℍ[ℝ]) (z : ℍ[ℝ]) :
    star (u : ℍ[ℝ]) * ((u : ℍ[ℝ]) * z * star (u : ℍ[ℝ])) * (u : ℍ[ℝ]) = z := by
  have h : star (u : ℍ[ℝ]) * star (star (u : ℍ[ℝ])) = 1 := by
    rw [star_star]; exact Unitary.star_mul_self_of_mem u.2
  simpa only [star_star] using conj_star_conj h z

/-- If the conjugations leave no proper nonzero subspace of the pure quaternions invariant, an
invariant form is a multiple of the inner product there: the operator of the form commutes with
the conjugations, has a real eigenvalue because the pure quaternions have odd dimension, and its
eigenspace is invariant. -/
private lemma smul_inner_of_irreducible (S : Set (unitary ℍ[ℝ]))
    (h3 : ∀ W : Submodule ℝ ℍ[ℝ], (∀ w ∈ W, w.re = 0) →
      (∀ u ∈ S, ∀ w ∈ W, (u : ℍ[ℝ]) * w * star (u : ℍ[ℝ]) ∈ W) →
      W = ⊥ ∨ ∀ x : ℍ[ℝ], x.re = 0 → x ∈ W)
    (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) (hB : ∀ u ∈ S, Inv B u) :
    ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = c * ⟪x, y⟫_ℝ := by
  have hAP : ∀ x ∈ pureSub, opOf B x ∈ pureSub := fun x _ => mem_pure.2 (re_opOf B x)
  obtain ⟨μ, hμ⟩ := exists_hasEigenvalue_of_odd_finrank ((opOf B).restrict hAP)
    (by rw [finrank_pure]; decide)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv1 : opOf B v = μ • (v : ℍ[ℝ]) :=
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hv.1)
  let E : Submodule ℝ ℍ[ℝ] := pureSub ⊓ Module.End.eigenspace (opOf B) μ
  have hE : ∀ x, x ∈ E ↔ x.re = 0 ∧ opOf B x = μ • x := fun x => by
    simp only [E, Submodule.mem_inf, mem_pure, Module.End.mem_eigenspace_iff]
  have hinv : ∀ u ∈ S, ∀ w ∈ E, (u : ℍ[ℝ]) * w * star (u : ℍ[ℝ]) ∈ E := by
    intro u hu w hw
    obtain ⟨hw0, hw1⟩ := (hE w).1 hw
    refine (hE _).2 ⟨by rw [re_conj_unit, hw0], ?_⟩
    rw [opOf_conj B u (hB u hu) hw0, hw1, mul_smul_comm, smul_mul_assoc]
  rcases h3 E (fun w hw => ((hE w).1 hw).1) hinv with hbot | hall
  · exfalso
    have hvE : (v : ℍ[ℝ]) ∈ E := (hE _).2 ⟨mem_pure.1 v.2, hv1⟩
    rw [hbot, Submodule.mem_bot] at hvE
    exact hv.2 (Subtype.ext hvE)
  · refine ⟨μ, fun x y hx hy => ?_⟩
    rw [← inner_opOf B x hy, ((hE x).1 (hall x hx)).2, real_inner_smul_left]

/-- If every invariant symmetric form is a multiple of the inner product on the pure
quaternions, the conjugations leave no proper nonzero subspace of them invariant: the
orthogonal projection onto an invariant subspace commutes with the conjugations and gives an
invariant symmetric form. -/
private lemma irreducible_of_symm (S : Set (unitary ℍ[ℝ]))
    (h2 : ∀ B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ, (∀ x y, B x y = B y x) → (∀ u ∈ S, Inv B u) →
      ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = c * ⟪x, y⟫_ℝ)
    (W : Submodule ℝ ℍ[ℝ]) (hWre : ∀ w ∈ W, w.re = 0)
    (hWinv : ∀ u ∈ S, ∀ w ∈ W, (u : ℍ[ℝ]) * w * star (u : ℍ[ℝ]) ∈ W) :
    W = ⊥ ∨ ∀ x : ℍ[ℝ], x.re = 0 → x ∈ W := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hsurj : ∀ u ∈ S, ∀ z ∈ W, ∃ z' ∈ W, (u : ℍ[ℝ]) * z' * star (u : ℍ[ℝ]) = z := by
    intro u hu z hz
    let f : W →ₗ[ℝ] W := (LinearMap.mulLeftRight ℝ ((u : ℍ[ℝ]), star (u : ℍ[ℝ]))).restrict
      (fun z hz => by rw [LinearMap.mulLeftRight_apply]; exact hWinv u hu z hz)
    have hf : Function.Injective f := by
      intro a b hab
      have h := congrArg (fun t : W => star (u : ℍ[ℝ]) * (t : ℍ[ℝ]) * (u : ℍ[ℝ])) hab
      simp only [f, LinearMap.coe_restrict_apply, LinearMap.mulLeftRight_apply] at h
      rw [star_conj_conj, star_conj_conj] at h
      exact Subtype.ext h
    obtain ⟨z', hz'⟩ := (LinearMap.injective_iff_surjective.1 hf) ⟨z, hz⟩
    exact ⟨z', z'.2, congrArg Subtype.val hz'⟩
  have hcomm : ∀ u ∈ S, ∀ x : ℍ[ℝ], W.starProjection ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) =
      (u : ℍ[ℝ]) * W.starProjection x * star (u : ℍ[ℝ]) := by
    intro u hu x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (hWinv u hu _ (W.starProjection_apply_mem x)) fun z hz => ?_
    obtain ⟨z', hz'W, rfl⟩ := hsurj u hu z hz
    rw [← sub_mul, ← mul_sub, inner_conj (Unitary.star_mul_self_of_mem u.2),
      Submodule.starProjection_inner_eq_zero x z' hz'W]
  let Bw : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ := innerₗ ℍ[ℝ] ∘ₗ (W.starProjection : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ])
  have hBw : ∀ x y, Bw x y = ⟪W.starProjection x, y⟫_ℝ := fun _ _ => rfl
  obtain ⟨c, hc⟩ := h2 Bw
    (fun x y => by rw [hBw, hBw, Submodule.inner_starProjection_left_eq_right, real_inner_comm])
    (fun u hu x y _ _ => by
      rw [hBw, hBw, hcomm u hu, inner_conj (Unitary.star_mul_self_of_mem u.2)])
  have hc1 : c = 1 := by
    have h := hc w w (hWre w hwW) (hWre w hwW)
    rw [hBw, Submodule.starProjection_eq_self_iff.2 hwW] at h
    have hww : ⟪w, w⟫_ℝ ≠ 0 := inner_self_ne_zero.2 hw0
    have : (1 - c) * ⟪w, w⟫_ℝ = 0 := by linear_combination h
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hww)).symm
  intro x hx
  have h := hc x x hx hx
  rw [hBw, hc1, one_mul] at h
  rw [← Submodule.starProjection_eq_self_iff]
  have hd : ⟪x - W.starProjection x, x - W.starProjection x⟫_ℝ = 0 := by
    rw [inner_sub_right, Submodule.starProjection_inner_eq_zero x _
      (W.starProjection_apply_mem x), sub_zero, inner_sub_left, real_inner_comm x, h, sub_self]
  exact (sub_eq_zero.1 (inner_self_eq_zero.1 hd)).symm

/-- Conjugation by all unit quaternions leaves no proper nonzero subspace of the pure
quaternions invariant: any unit pure quaternion is conjugate to any other one. -/
private lemma irreducible_univ (W : Submodule ℝ ℍ[ℝ]) (hWre : ∀ w ∈ W, w.re = 0)
    (hWinv : ∀ u : unitary ℍ[ℝ], ∀ w ∈ W, (u : ℍ[ℝ]) * w * star (u : ℍ[ℝ]) ∈ W) :
    W = ⊥ ∨ ∀ x : ℍ[ℝ], x.re = 0 → x ∈ W := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact W.zero_mem
  have hunit : ∀ z : ℍ[ℝ], z ≠ 0 → ‖z‖⁻¹ • z ∈ unitary ℍ[ℝ] := fun z hz => by
    rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm, norm_smul,
      norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
  obtain ⟨c, hc⟩ := exists_unitary_mul_eq_mul ⟨_, hunit w hw0⟩ ⟨_, hunit x hx0⟩
    (by simp [hWre w hwW, hx])
  have hc' : ‖w‖⁻¹ • ((c : ℍ[ℝ]) * w * star (c : ℍ[ℝ])) = ‖x‖⁻¹ • x := by
    have h : (c : ℍ[ℝ]) * (‖w‖⁻¹ • w) = (‖x‖⁻¹ • x) * c := congrArg Subtype.val hc
    rw [← smul_mul_assoc, ← mul_smul_comm, h, mul_assoc, Unitary.mul_star_self_of_mem c.2,
      mul_one]
  have hxW : x = ‖x‖ • ‖w‖⁻¹ • ((c : ℍ[ℝ]) * w * star (c : ℍ[ℝ])) := by
    rw [hc', smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx0), one_smul]
  rw [hxW]
  exact W.smul_mem _ (W.smul_mem _ (hWinv c w hwW))

/-! ### One conjugation that is neither the identity nor a half-turn -/

private lemma conj_qI (r b : ℝ) (hrb : r ^ 2 + b ^ 2 = 1) :
    (⟨r, b, 0, 0⟩ : ℍ[ℝ]) * qI * star (⟨r, b, 0, 0⟩ : ℍ[ℝ]) = qI := by
  ext <;> simp [qI] <;> first | ring1 | linear_combination hrb

private lemma conj_qJ (r b : ℝ) :
    (⟨r, b, 0, 0⟩ : ℍ[ℝ]) * qJ * star (⟨r, b, 0, 0⟩ : ℍ[ℝ]) =
      (r ^ 2 - b ^ 2) • qJ + (2 * r * b) • qK := by
  ext <;> simp [qJ, qK] <;> ring

private lemma conj_qK (r b : ℝ) :
    (⟨r, b, 0, 0⟩ : ℍ[ℝ]) * qK * star (⟨r, b, 0, 0⟩ : ℍ[ℝ]) =
      (-(2 * r * b)) • qJ + (r ^ 2 - b ^ 2) • qK := by
  ext <;> simp [qJ, qK] <;> ring

private lemma expand (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) {x y : ℍ[ℝ]} (hx : x.re = 0)
    (hy : y.re = 0) :
    B x y = x.imI * y.imI * B qI qI + x.imI * y.imJ * B qI qJ + x.imI * y.imK * B qI qK +
      x.imJ * y.imI * B qJ qI + x.imJ * y.imJ * B qJ qJ + x.imJ * y.imK * B qJ qK +
      x.imK * y.imI * B qK qI + x.imK * y.imJ * B qK qJ + x.imK * y.imK * B qK qK := by
  conv_lhs => rw [eq_sum_of_re_eq_zero hx, eq_sum_of_re_eq_zero hy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- For the conjugation by `r + b i` with `r b ≠ 0`, the invariant forms on the pure
quaternions are spanned by the inner product, `⟪m, x⟫ ⟪m, y⟫` and `⟪m, x * y⟫` with `m = b i`:
the invariance equations at the basis `i, j, k` force the matrix of the form to commute with a
rotation through an angle outside `πℤ` about `i`. -/
private lemma classify_std (r b : ℝ) (hr : r ≠ 0) (hb : b ≠ 0) (hrb : r ^ 2 + b ^ 2 = 1)
    (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ)
    (hB : ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
      B ((⟨r, b, 0, 0⟩ : ℍ[ℝ]) * x * star (⟨r, b, 0, 0⟩ : ℍ[ℝ]))
        ((⟨r, b, 0, 0⟩ : ℍ[ℝ]) * y * star (⟨r, b, 0, 0⟩ : ℍ[ℝ])) = B x y) :
    ∃ α β γ : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
      B x y = α * ⟪x, y⟫_ℝ + β * ⟪(⟨0, b, 0, 0⟩ : ℍ[ℝ]), x⟫_ℝ * ⟪(⟨0, b, 0, 0⟩ : ℍ[ℝ]), y⟫_ℝ +
        γ * ⟪(⟨0, b, 0, 0⟩ : ℍ[ℝ]), x * y⟫_ℝ := by
  have hI : qI.re = 0 := rfl
  have hJ : qJ.re = 0 := rfl
  have hK : qK.re = 0 := rfl
  have e12 := hB qI qJ hI hJ
  have e13 := hB qI qK hI hK
  have e21 := hB qJ qI hJ hI
  have e31 := hB qK qI hK hI
  have e22 := hB qJ qJ hJ hJ
  have e23 := hB qJ qK hJ hK
  simp only [conj_qI r b hrb, conj_qJ, conj_qK, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at e12 e13 e21 e31 e22 e23
  have hb2 : 4 * b ^ 2 ≠ 0 := by positivity
  have hs : 2 * r * b ≠ 0 := by positivity
  have h12 : B qI qJ = 0 := (mul_eq_zero.1 (by
    linear_combination (r ^ 2 - b ^ 2 - 1) * e12 - 2 * r * b * e13 -
      ((r ^ 2 + b ^ 2 - 1) * B qI qJ) * hrb : 4 * b ^ 2 * B qI qJ = 0)).resolve_left hb2
  have h13 : B qI qK = 0 := (mul_eq_zero.1 (by
    linear_combination 2 * r * b * e12 + (r ^ 2 - b ^ 2 - 1) * e13 -
      ((r ^ 2 + b ^ 2 - 1) * B qI qK) * hrb : 4 * b ^ 2 * B qI qK = 0)).resolve_left hb2
  have h21 : B qJ qI = 0 := (mul_eq_zero.1 (by
    linear_combination (r ^ 2 - b ^ 2 - 1) * e21 - 2 * r * b * e31 -
      ((r ^ 2 + b ^ 2 - 1) * B qJ qI) * hrb : 4 * b ^ 2 * B qJ qI = 0)).resolve_left hb2
  have h31 : B qK qI = 0 := (mul_eq_zero.1 (by
    linear_combination 2 * r * b * e21 + (r ^ 2 - b ^ 2 - 1) * e31 -
      ((r ^ 2 + b ^ 2 - 1) * B qK qI) * hrb : 4 * b ^ 2 * B qK qI = 0)).resolve_left hb2
  set D := B qK qK - B qJ qJ with hD
  set E := B qJ qK + B qK qJ with hE
  have hX : 2 * r * b * D + (r ^ 2 - b ^ 2) * E = 0 := (mul_eq_zero.1 (by
    linear_combination e22 - ((r ^ 2 + b ^ 2 + 1) * B qJ qJ) * hrb :
      2 * r * b * (2 * r * b * D + (r ^ 2 - b ^ 2) * E) = 0)).resolve_left hs
  have hY : (r ^ 2 - b ^ 2) * D - 2 * r * b * E = 0 := (mul_eq_zero.1 (by
    linear_combination e23 - ((r ^ 2 + b ^ 2 + 1) * B qJ qK) * hrb :
      2 * r * b * ((r ^ 2 - b ^ 2) * D - 2 * r * b * E) = 0)).resolve_left hs
  have hD0 : D = 0 := by
    linear_combination 2 * r * b * hX + (r ^ 2 - b ^ 2) * hY - ((r ^ 2 + b ^ 2 + 1) * D) * hrb
  have hE0 : E = 0 := by
    linear_combination (r ^ 2 - b ^ 2) * hX - 2 * r * b * hY - ((r ^ 2 + b ^ 2 + 1) * E) * hrb
  refine ⟨B qJ qJ, (B qI qI - B qJ qJ) / b ^ 2, B qJ qK / b, fun x y hx hy => ?_⟩
  rw [expand B hx hy, inner_eq_components, inner_eq_components, inner_eq_components,
    inner_eq_components, Quaternion.imI_mul, hx, hy, h12, h13, h21, h31]
  have h33 : B qK qK = B qJ qJ := by linear_combination hD0
  have h32 : B qK qJ = -B qJ qK := by linear_combination hE0
  rw [h33, h32]
  field_simp
  ring

private lemma inner_conj_star (u : unitary ℍ[ℝ]) (x y : ℍ[ℝ]) :
    ⟪star (u : ℍ[ℝ]) * x * (u : ℍ[ℝ]), star (u : ℍ[ℝ]) * y * (u : ℍ[ℝ])⟫_ℝ = ⟪x, y⟫_ℝ := by
  have h : star (star (u : ℍ[ℝ])) * star (u : ℍ[ℝ]) = 1 := by
    rw [star_star]; exact Unitary.mul_star_self_of_mem u.2
  simpa only [star_star] using inner_conj h x y

private lemma conj_star_mul (u : unitary ℍ[ℝ]) (x y : ℍ[ℝ]) :
    star (u : ℍ[ℝ]) * x * (u : ℍ[ℝ]) * (star (u : ℍ[ℝ]) * y * (u : ℍ[ℝ])) =
      star (u : ℍ[ℝ]) * (x * y) * (u : ℍ[ℝ]) := by
  have h : star (star (u : ℍ[ℝ])) * star (u : ℍ[ℝ]) = 1 := by
    rw [star_star]; exact Unitary.mul_star_self_of_mem u.2
  simpa only [star_star] using conj_mul_conj h x y

private lemma mem_unitary_of_ne_zero {z : ℍ[ℝ]} (hz : z ≠ 0) : ‖z‖⁻¹ • z ∈ unitary ℍ[ℝ] := by
  rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm, norm_smul,
    norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

/-- A form invariant under the conjugation by a unit quaternion `u` with `u.re ≠ 0` and
`u.im ≠ 0` lies in the span of the three invariant forms: conjugating by a unit quaternion that
carries `i` to the unit vector of `u.im` reduces to the axis `i`. -/
private lemma classify (u : unitary ℍ[ℝ]) (hre : (u : ℍ[ℝ]).re ≠ 0) (him : (u : ℍ[ℝ]).im ≠ 0)
    (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) (hB : Inv B u) :
    ∃ α β γ : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
      B x y = α * ⟪x, y⟫_ℝ + β * ⟪(u : ℍ[ℝ]).im, x⟫_ℝ * ⟪(u : ℍ[ℝ]).im, y⟫_ℝ +
        γ * ⟪(u : ℍ[ℝ]).im, x * y⟫_ℝ := by
  set n := (u : ℍ[ℝ]).im
  have hn0 : ‖n‖ ≠ 0 := norm_ne_zero_iff.2 him
  obtain ⟨q, hq⟩ := exists_unitary_mul_eq_mul unitI ⟨_, mem_unitary_of_ne_zero him⟩
    (by simp [unitI, n])
  have hqI : (q : ℍ[ℝ]) * qI * star (q : ℍ[ℝ]) = ‖n‖⁻¹ • n := by
    have h : (q : ℍ[ℝ]) * qI = (‖n‖⁻¹ • n) * q := congrArg Subtype.val hq
    rw [h, mul_assoc, Unitary.mul_star_self_of_mem q.2, mul_one]
  have hm : (q : ℍ[ℝ]) * (⟨0, ‖n‖, 0, 0⟩ : ℍ[ℝ]) * star (q : ℍ[ℝ]) = n := by
    have : (⟨0, ‖n‖, 0, 0⟩ : ℍ[ℝ]) = ‖n‖ • qI := by ext <;> simp [qI]
    rw [this, mul_smul_comm, smul_mul_assoc, hqI, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  set r := (u : ℍ[ℝ]).re
  have hu : (u : ℍ[ℝ]) = r • 1 + ‖n‖ • ((q : ℍ[ℝ]) * qI * star (q : ℍ[ℝ])) := by
    rw [hqI, smul_smul, mul_inv_cancel₀ hn0, one_smul]
    ext <;> simp [n, r]
  set v : ℍ[ℝ] := ⟨r, ‖n‖, 0, 0⟩
  have hqv : (q : ℍ[ℝ]) * v = (u : ℍ[ℝ]) * q := by
    have hv' : v = r • 1 + ‖n‖ • qI := by ext <;> simp [v, qI]
    rw [hv', hu]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, mul_assoc,
      Unitary.star_mul_self_of_mem q.2]
  have hqv' : star v * star (q : ℍ[ℝ]) = star (q : ℍ[ℝ]) * star (u : ℍ[ℝ]) := by
    rw [← star_mul, hqv, star_mul]
  have hconj : ∀ x : ℍ[ℝ], (q : ℍ[ℝ]) * (v * x * star v) * star (q : ℍ[ℝ]) =
      (u : ℍ[ℝ]) * ((q : ℍ[ℝ]) * x * star (q : ℍ[ℝ])) * star (u : ℍ[ℝ]) := fun x => by
    calc (q : ℍ[ℝ]) * (v * x * star v) * star (q : ℍ[ℝ])
        = (q : ℍ[ℝ]) * v * x * (star v * star (q : ℍ[ℝ])) := by simp only [mul_assoc]
      _ = _ := by rw [hqv, hqv']; simp only [mul_assoc]
  have hrb : r ^ 2 + ‖n‖ ^ 2 = 1 := by
    have h1 : Quaternion.normSq (u : ℍ[ℝ]) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, mul_one]
    rw [sq ‖n‖, ← Quaternion.normSq_eq_norm_mul_self]
    rw [Quaternion.normSq_def'] at h1 ⊢
    simp only [n, r, Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im]
    linear_combination h1
  let B' : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ :=
    (B ∘ₗ LinearMap.mulLeftRight ℝ ((q : ℍ[ℝ]), star (q : ℍ[ℝ]))).compl₂
      (LinearMap.mulLeftRight ℝ ((q : ℍ[ℝ]), star (q : ℍ[ℝ])))
  have hB' : ∀ x y, B' x y = B ((q : ℍ[ℝ]) * x * star (q : ℍ[ℝ]))
      ((q : ℍ[ℝ]) * y * star (q : ℍ[ℝ])) := fun _ _ => rfl
  obtain ⟨α, β, γ, h⟩ := classify_std r ‖n‖ hre hn0 hrb B' (fun x y hx hy => by
    rw [hB', hB', hconj, hconj, hB _ _ (by rw [re_conj_unit, hx]) (by rw [re_conj_unit, hy])])
  refine ⟨α, β, γ, fun x y hx hy => ?_⟩
  have hx' : (star (q : ℍ[ℝ]) * x * q).re = 0 := by rw [re_conj_star_unit, hx]
  have hy' : (star (q : ℍ[ℝ]) * y * q).re = 0 := by rw [re_conj_star_unit, hy]
  have hback : ∀ z : ℍ[ℝ], (q : ℍ[ℝ]) * (star (q : ℍ[ℝ]) * z * q) * star (q : ℍ[ℝ]) = z :=
    conj_star_conj (Unitary.mul_star_self_of_mem q.2)
  have hmz : ∀ z : ℍ[ℝ], ⟪(⟨0, ‖n‖, 0, 0⟩ : ℍ[ℝ]), star (q : ℍ[ℝ]) * z * q⟫_ℝ = ⟪n, z⟫_ℝ :=
    fun z => by rw [← inner_conj_left, hm]
  have := h _ _ hx' hy'
  rw [hB', hback, hback, inner_conj_star, hmz, hmz, conj_star_mul, hmz] at this
  exact this

/-- Each of the three forms is invariant under the conjugation by `u`, since `u` commutes with
`u.im`. -/
private lemma inner_im_conj (u : unitary ℍ[ℝ]) (z : ℍ[ℝ]) :
    ⟪(u : ℍ[ℝ]).im, (u : ℍ[ℝ]) * z * star (u : ℍ[ℝ])⟫_ℝ = ⟪(u : ℍ[ℝ]).im, z⟫_ℝ := by
  have hc : (u : ℍ[ℝ]) * (u : ℍ[ℝ]).im = (u : ℍ[ℝ]).im * u := by
    ext <;> simp <;> ring
  have hn : star (u : ℍ[ℝ]) * (u : ℍ[ℝ]).im * (u : ℍ[ℝ]) = (u : ℍ[ℝ]).im := by
    rw [mul_assoc, ← hc, ← mul_assoc, Unitary.star_mul_self_of_mem u.2, one_mul]
  rw [real_inner_comm, inner_conj_left, hn, real_inner_comm]

/-! ### Main statements -/

/-- For any family `S` of unit quaternions the following are equivalent: every bilinear form
that is invariant on the pure quaternions under the conjugations by `S` is a multiple of the
inner product there; the same for symmetric forms; the conjugations by `S` leave no subspace of
the pure quaternions invariant other than `0` and all of them. -/
theorem invariant_bilinear_tfae (S : Set (unitary ℍ[ℝ])) :
    List.TFAE
      [ ∀ B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ,
          (∀ u ∈ S, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
            B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) →
          ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = c * ⟪x, y⟫_ℝ,
        ∀ B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ, (∀ x y, B x y = B y x) →
          (∀ u ∈ S, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
            B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) →
          ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = c * ⟪x, y⟫_ℝ,
        ∀ W : Submodule ℝ ℍ[ℝ], (∀ w ∈ W, w.re = 0) →
          (∀ u ∈ S, ∀ w ∈ W, (u : ℍ[ℝ]) * w * star (u : ℍ[ℝ]) ∈ W) →
          W = ⊥ ∨ ∀ x : ℍ[ℝ], x.re = 0 → x ∈ W ] := by
  tfae_have 1 → 2 := fun h1 B _ hB => h1 B hB
  tfae_have 2 → 3 := fun h2 W hWre hWinv => irreducible_of_symm S h2 W hWre hWinv
  tfae_have 3 → 1 := fun h3 B hB => smul_inner_of_irreducible S h3 B hB
  tfae_finish

/-- A bilinear form on the quaternions that is invariant on the pure quaternions under the
conjugation by every unit quaternion is a multiple of the inner product there. -/
theorem conj_invariant_bilinear_eq_smul_inner (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ)
    (hB : ∀ u : unitary ℍ[ℝ], ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
      B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) :
    ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = c * ⟪x, y⟫_ℝ :=
  smul_inner_of_irreducible Set.univ
    (fun W hWre hWinv => irreducible_univ W hWre fun u w hw => hWinv u (Set.mem_univ u) w hw)
    B fun u _ => hB u

/-- For a unit quaternion `u` that is neither `±1` nor pure (`u.re ≠ 0`, `u.im ≠ 0`), a bilinear
form is invariant on the pure quaternions under the conjugation by `u` exactly when it equals
`α ⟪x, y⟫ + β ⟪n, x⟫ ⟪n, y⟫ + γ ⟪n, x * y⟫` there, with `n = u.im`. -/
theorem conj_invariant_bilinear_iff (u : unitary ℍ[ℝ]) (hre : (u : ℍ[ℝ]).re ≠ 0)
    (him : (u : ℍ[ℝ]).im ≠ 0) (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) :
    (∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
        B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) ↔
      ∃ α β γ : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
        B x y = α * ⟪x, y⟫_ℝ + β * ⟪(u : ℍ[ℝ]).im, x⟫_ℝ * ⟪(u : ℍ[ℝ]).im, y⟫_ℝ +
          γ * ⟪(u : ℍ[ℝ]).im, x * y⟫_ℝ := by
  refine ⟨classify u hre him B, ?_⟩
  rintro ⟨α, β, γ, h⟩ x y hx hy
  rw [h _ _ (by rw [re_conj_unit, hx]) (by rw [re_conj_unit, hy]), h x y hx hy,
    inner_conj (Unitary.star_mul_self_of_mem u.2),
    conj_mul_conj (Unitary.star_mul_self_of_mem u.2), inner_im_conj, inner_im_conj, inner_im_conj]

end D5.S3.Quantum.AURICOmega.TangentInvariantForms
