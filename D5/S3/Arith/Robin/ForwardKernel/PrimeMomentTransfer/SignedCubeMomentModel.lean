/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SignedCubeMomentModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed cubes realize centred singular-series moments and cubic and fourth identities. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CentredProductExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticFourthDefect
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs

/-! A signed finite-cube realization of the quadratic formal moment values. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A centred coordinate on the finite Boolean cube. -/
private def cubeY (s : ℝ) (d : ι) (B : Finset ι) : ℝ :=
  s * (if d ∈ B then 1 else 0) - 1

private def cubeColumn (m : Finset ι → ℝ) : IncidenceAlgebra ℝ (Finset ι) where
  toFun D E := if E = ⊤ then m D else 0
  eq_zero_of_not_le' := by
    intro D E h
    split_ifs with he
    · exact False.elim (h (he ▸ le_top))
    · rfl

private def cubeWeight (C : Finset ι → ℝ) (s : ℝ) (B : Finset ι) : ℝ :=
  (IncidenceAlgebra.mu ℝ * cubeColumn (fun D => C D / s ^ D.card) :
    IncidenceAlgebra ℝ (Finset ι)) B ⊤

/-- The signed functional obtained by Boolean Möbius inversion. -/
private def signedCubeFunctional (C : Finset ι → ℝ) (s : ℝ) :
    (Finset ι → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ B, cubeWeight C s B * F B
  map_add' F G := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r F := by simp [Finset.mul_sum, mul_left_comm]

private lemma cubeWeight_upper_sum (C : Finset ι → ℝ) (s : ℝ) (D : Finset ι) :
    (∑ B : Finset ι with D ⊆ B, cubeWeight C s B) = C D / s ^ D.card := by
  have he := congrArg (fun F : IncidenceAlgebra ℝ (Finset ι) => F D ⊤)
    (show IncidenceAlgebra.zeta ℝ *
        (IncidenceAlgebra.mu ℝ * cubeColumn (fun E => C E / s ^ E.card)) =
        cubeColumn (fun E => C E / s ^ E.card) by
      rw [← mul_assoc, IncidenceAlgebra.zeta_mul_mu, one_mul])
  have hi : Finset.Icc D (⊤ : Finset ι) = Finset.univ.filter (D ⊆ ·) := by
    ext B; simp
  rw [IncidenceAlgebra.mul_apply] at he
  change (∑ B ∈ Finset.Icc D ⊤,
    IncidenceAlgebra.zeta ℝ D B * cubeWeight C s B) =
      cubeColumn (fun E => C E / s ^ E.card) D ⊤ at he
  have hc : cubeColumn (fun E => C E / s ^ E.card) D ⊤ = C D / s ^ D.card := by
    simp [cubeColumn]
  rw [hc] at he
  rw [hi] at he
  calc
    (∑ B : Finset ι with D ⊆ B, cubeWeight C s B) =
        ∑ B : Finset ι with D ⊆ B,
          IncidenceAlgebra.zeta ℝ D B * cubeWeight C s B := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [IncidenceAlgebra.zeta_of_le (Finset.mem_filter.mp hB).2, one_mul]
    _ = _ := he

private lemma cube_uncentred_moment (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    (D : Finset ι) :
    signedCubeFunctional C s (∏ d ∈ D, (cubeY s d + 1)) = C D := by
  have hp : (∏ d ∈ D, (cubeY s d + 1)) =
      fun B => s ^ D.card * (if D ⊆ B then 1 else 0) := by
    funext B
    simp only [Finset.prod_apply, Pi.add_apply, Pi.one_apply, cubeY,
      sub_add_cancel, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_boole]
    rfl
  rw [hp]
  change (∑ B, cubeWeight C s B *
    (s ^ D.card * (if D ⊆ B then 1 else 0))) = C D
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul, cubeWeight_upper_sum]
  exact div_mul_cancel₀ _ (pow_ne_zero _ hs)

/-- Every square-free coordinate moment is the centred singular series. -/
private theorem signedCubeFunctional_squarefree (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    (D : Finset ι) :
    signedCubeFunctional C s (∏ d ∈ D, cubeY s d) = centerFinite C D := by
  have he : (∏ d ∈ D, cubeY s d) =
      ∑ J ∈ D.powerset, (-1 : ℝ) ^ (D.card - J.card) •
        (∏ d ∈ J, (cubeY s d + 1)) := by
    simpa only [add_sub_cancel_right, Algebra.smul_def, map_pow, map_neg, map_one] using
      (prod_sub_one_expansion D (fun d => cubeY s d + 1))
  rw [he, map_sum]
  unfold centerFinite
  apply Finset.sum_congr rfl
  intro J hJ
  rw [map_smul, cube_uncentred_moment C s hs]
  rfl

omit [Fintype ι] in
private lemma cube_quadratic (s : ℝ) (d : ι) :
    (cubeY s d) ^ 2 = (s - 2) • cubeY s d +
      algebraMap ℝ (Finset ι → ℝ) (s - 1) := by
  funext B
  change (s * (if d ∈ B then 1 else 0) - 1) ^ 2 =
    (s - 2) * (s * (if d ∈ B then 1 else 0) - 1) + (s - 1)
  split_ifs <;> ring

private lemma cube_one (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0) (hC : C ∅ = 1) :
    signedCubeFunctional C s 1 = 1 := by
  simpa [centerFinite, hC] using signedCubeFunctional_squarefree C s hs ∅

private lemma cube_centred (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hC : C ∅ = 1) (hCs : ∀ d, C {d} = 1) (d : ι) :
    signedCubeFunctional C s (cubeY s d) = 0 := by
  have hp : ({d} : Finset ι).powerset = {∅, {d}} := by
    ext J
    simp only [Finset.mem_powerset, Finset.subset_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
  simpa [centerFinite, hp, hC, hCs] using signedCubeFunctional_squarefree C s hs {d}

omit [Fintype ι] in
private lemma cube_power (s : ℝ) (d : ι) (r : ℕ) :
    cubeY s d ^ r = (red r s).1 • cubeY s d +
      algebraMap ℝ (Finset ι → ℝ) (red r s).2 := by
  funext B
  exact red_pow s (cubeY s d B) (congrFun (cube_quadratic s d) B) r

private lemma cube_tuple_moment (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    {k : ℕ} (d : Fin k → ι) :
    signedCubeFunctional C s (∏ i, cubeY s (d i)) = reducedFinite C s d := by
  rw [Finset.prod_comp (cubeY s) d]
  simp_rw [cube_power]
  rw [Finset.prod_add, map_sum]
  unfold reducedFinite mult
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [Finset.prod_smul, Finset.prod_const_one, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one, map_smul,
    signedCubeFunctional_squarefree C s hs, smul_eq_mul]
  ring

/-- Formal coefficient moments are realized by the signed functional. -/
private theorem formalMoment_eq_signedCube (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    {k : ℕ} (f : Fin k → ι → ℝ) :
    formalMoment C s f = quadraticFamilyMoment (signedCubeFunctional C s) (cubeY s) f := by
  rw [quadraticFamilyMoment_eq_tuple_sum]
  simp only [formalMoment, cube_tuple_moment C s hs]

private lemma formalDistinct_eq_signedCube (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    {k : ℕ} (f : Fin k → ι → ℝ) :
    formalDistinct C f = distinctIndexMoment (signedCubeFunctional C s) (cubeY s) f := by
  unfold formalDistinct distinctIndexMoment
  apply Finset.sum_congr rfl
  intro d hd
  have hinj := (Finset.mem_filter.mp hd).2
  rw [← Finset.prod_image hinj.injOn, signedCubeFunctional_squarefree C s hs]

/-- The formal second moment adds the diagonal term to the distinct-index sum. -/
theorem formal_second_moment_eq (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hC : C ∅ = 1) (hCs : ∀ d, C {d} = 1) (f g : ι → ℝ) :
    formalMoment C s ![f, g] = formalDistinct C ![f, g] +
      (s - 1) * indexSum (f * g) := by
  simp_rw [formalMoment_eq_signedCube C s hs, formalDistinct_eq_signedCube C s hs]
  exact quadratic_second_moment_eq _ _ (s - 2) (s - 1)
    (cube_one C s hs hC) (cube_centred C s hs hC hCs) (cube_quadratic s) f g

/-- The formal cubic value has the three repeated-pair terms and the full diagonal. -/
theorem formal_third_moment_eq (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hC : C ∅ = 1) (hCs : ∀ d, C {d} = 1) (f g h : ι → ℝ) :
    formalMoment C s ![f, g, h] = formalDistinct C ![f, g, h] +
      (s - 2) * (formalDistinct C ![f * g, h] + formalDistinct C ![f * h, g] +
        formalDistinct C ![g * h, f]) + (s - 2) * (s - 1) * indexSum (f * g * h) := by
  simp_rw [formalMoment_eq_signedCube C s hs, formalDistinct_eq_signedCube C s hs]
  exact quadratic_third_moment_eq _ _ (s - 2) (s - 1)
    (cube_one C s hs hC) (cube_centred C s hs hC hCs) (cube_quadratic s) f g h

/-- The formal fourth pairing defect retains every repeated-index contribution. -/
theorem formal_fourth_pairing_defect (C : Finset ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hC : C ∅ = 1) (hCs : ∀ d, C {d} = 1) (f g h q : ι → ℝ) :
    formalMoment C s ![f, g, h, q] -
        perfectPairingSum (fun u v => formalMoment C s ![u, v]) f g h q =
      formalDistinct C ![f, g, h, q] -
        perfectPairingSum (fun u v => formalDistinct C ![u, v]) f g h q +
      (s - 2) * repeatedPairSum (fun u v w => formalDistinct C ![u, v, w]) f g h q +
      (s - 2) ^ 2 * pairPairSum (fun u v => formalDistinct C ![u, v]) f g h q +
      ((s - 2) ^ 2 - 2 * (s - 1)) *
        tripleSingletonSum (fun u v => formalDistinct C ![u, v]) f g h q +
      ((s - 2) ^ 2 * (s - 1) - 2 * (s - 1) ^ 2) * indexSum (f * g * h * q) := by
  simp_rw [formalMoment_eq_signedCube C s hs, formalDistinct_eq_signedCube C s hs]
  exact quadratic_fourth_pairing_defect _ _ (s - 2) (s - 1)
    (cube_one C s hs hC) (cube_centred C s hs hC hCs) (cube_quadratic s) f g h q

omit [Fintype ι] in
lemma centerFinite_image {κ : Type*} [DecidableEq κ]
    (C : Finset κ → ℝ) (e : ι → κ) (he : Function.Injective e) (D : Finset ι) :
    centerFinite (fun J => C (J.image e)) D = centerFinite C (D.image e) := by
  unfold centerFinite
  rw [Finset.powerset_image, Finset.sum_image (Finset.image_injective he).injOn]
  simp only [Finset.card_image_of_injective _ he]

omit [Fintype ι] in
private lemma reducedFinite_image (SS : Finset ℕ → ℝ) (s : ℝ)
    (e : ι → ℕ) (he : Function.Injective e) {k : ℕ} (d : Fin k → ι) :
    reducedFinite (fun J => SS (J.image e)) s d = reducedTuple SS s (e ∘ d) := by
  unfold reducedTuple
  unfold reducedFinite
  dsimp only
  conv_rhs =>
    rw [← Finset.image_image, Finset.powerset_image,
      Finset.sum_image (Finset.image_injective he).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← centerFinite_image SS e he J]
  congr 2
  · rw [Finset.prod_image he.injOn]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [mult, Function.comp_apply, he.eq_iff]
  · rw [← Finset.image_sdiff _ _ he, Finset.prod_image he.injOn]
    apply Finset.prod_congr rfl
    intro v hv
    simp only [mult, Function.comp_apply, he.eq_iff]

/-- Interval formal values are coefficient moments on any finite set containing their shifts. -/
theorem Phi_eq_formalMoment (SS : Finset ℕ → ℝ) (H s : ℝ) {k : ℕ}
    (a b : Fin k → ℝ) (S : Finset ℕ)
    (hS : ∀ i, points H (a i) (b i) ⊆ S) :
    Phi SS H s a b =
      formalMoment (fun J : Finset S => SS (J.image Subtype.val)) s
        (fun i d => if d.val ∈ points H (a i) (b i) then 1 else 0) := by
  classical
  unfold Phi formalMoment
  simp_rw [Fintype.prod_boole, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun d _ i => (d i).val)
  · intro d hd
    exact Fintype.mem_piFinset.mpr (Finset.mem_filter.mp hd).2
  · intro d hd d' hd' heq
    funext i
    exact Subtype.ext (congrFun heq i)
  · intro d hd
    have hm := Fintype.mem_piFinset.mp hd
    let d' : Fin k → S := fun i => ⟨d i, hS i (hm i)⟩
    exact ⟨d', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
  · intro d hd
    exact reducedFinite_image SS s Subtype.val Subtype.val_injective d

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
