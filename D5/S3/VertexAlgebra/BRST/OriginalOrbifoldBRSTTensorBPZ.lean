/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTTensorBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTTensorBPZ
   mirror-E: none(waiver:algebraic-original-matter-ghost-tensor-bpz)
   anchors: []
   utility: none
   digest: Finite signed BPZ transposition for the original matter–ghost tensor field. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTStateField
import D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

/-! The reflected matter and ghost indices are complementary in the opposite tensor
coefficient. The integer convolutions are finite on the indicated input tensors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTTensorBPZ

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock parity)
open OriginalOrbifoldCriticalMatter (Matter State matterDatum mode)
open OriginalOrbifoldMatterTensorField (stateField)
open OriginalOrbifoldBRSTStateField (Y Y_tmul support_tmul)
open OriginalOrbifoldBRSTBPZWard (betaTotal)
open OriginalOrbifoldMatterBPZ (matterBPZ)
open OriginalOrbifoldBRSTGhostBPZ (beta)
open StateField.BorcherdsPermutations (dividedTranslation lowerTruncated_modesOfStateField
  modesOfStateField)
open StateFieldResidueReconstruction (epsilon)
open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

open private betaTotal_tmul from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

local notation "DM" => dividedTranslation (mode 1)
local notation "DG" => dividedTranslation (BcGhostVirasoro.L 1)
local notation "DT" => dividedTranslation (VirasoroBRST.Ltotal matterDatum 1)
local notation "YG" => BcGhostStateField.Y

private theorem tensorModes_finite (a u : Matter) (b x : Fock) (n : ℤ) :
    Function.HasFiniteSupport (fun j : ℤ =>
      ((stateField a)[[j]]) u ⊗ₜ[ℂ] ((YG b)[[n - 1 - j]]) x) := by
  obtain ⟨A, hA⟩ := lowerTruncated_modesOfStateField stateField a u
  obtain ⟨B, hB⟩ := lowerTruncated_modesOfStateField YG b x
  exact (Set.finite_Icc _ _).subset (support_tmul a u b x n A B hA hB)

private theorem betaTotal_mode_tmul (a u v : Matter) (b x y : Fock) (n : ℤ) :
    betaTotal (((Y (a ⊗ₜ[ℂ] b))[[n]]) (u ⊗ₜ[ℂ] x)) (v ⊗ₜ[ℂ] y) =
      ∑ᶠ j : ℤ, matterBPZ (((stateField a)[[j]]) u) v *
        beta (((YG b)[[n - 1 - j]]) x) y := by
  let term : ℤ → State := fun j =>
    ((stateField a)[[j]]) u ⊗ₜ[ℂ] ((YG b)[[n - 1 - j]]) x
  let form : State →ₗ[ℂ] ℂ := betaTotal.flip (v ⊗ₜ[ℂ] y)
  have hfinite : Function.HasFiniteSupport term := tensorModes_finite a u b x n
  rw [Y_tmul]
  change form (∑ᶠ j : ℤ, term j) = _
  rw [map_finsum form hfinite]
  apply finsum_congr
  intro j
  change betaTotal (((stateField a)[[j]]) u ⊗ₜ[ℂ] ((YG b)[[n - 1 - j]]) x)
    (v ⊗ₜ[ℂ] y) = _
  exact betaTotal_tmul (((stateField a)[[j]]) u) v (((YG b)[[n - 1 - j]]) x) y

private def reflect (c : ℤ) : ℤ ≃ ℤ where
  toFun j := c - j
  invFun j := c - j
  left_inv j := by
    change c - (c - j) = j
    omega
  right_inv j := by
    change c - (c - j) = j
    omega

/-- For fixed descendant orders, the component BPZ indices give the native opposite
tensor coefficient. The same identity accepts an already parity-transformed ghost input. -/
theorem reflected_mode_pair (a u v : Matter) (b x y : Fock) (h k n : ℤ) (r s : ℕ) :
    (∑ᶠ j : ℤ,
      matterBPZ u (((stateField (DM r a))[[2 * h - (r : ℤ) - j - 2]]) v) *
        beta x (((YG (DG s b))[[2 * k - (s : ℤ) - (n - 1 - j) - 2]]) y)) =
      betaTotal (u ⊗ₜ[ℂ] x)
        (((Y (DM r a ⊗ₜ[ℂ] DG s b))[[2 * (h + k) - (r : ℤ) - (s : ℤ) - n - 2]])
          (v ⊗ₜ[ℂ] y)) := by
  let N : ℤ := 2 * (h + k) - (r : ℤ) - (s : ℤ) - n - 2
  let e := reflect (2 * h - (r : ℤ) - 2)
  let term : ℤ → State := fun i =>
    ((stateField (DM r a))[[i]]) v ⊗ₜ[ℂ] ((YG (DG s b))[[N - 1 - i]]) y
  let form := betaTotal (u ⊗ₜ[ℂ] x)
  change _ = form (((Y (DM r a ⊗ₜ[ℂ] DG s b))[[N]]) (v ⊗ₜ[ℂ] y))
  rw [Y_tmul]
  change _ = form (∑ᶠ i : ℤ, term i)
  rw [map_finsum form (tensorModes_finite (DM r a) v (DG s b) y N)]
  calc
    _ = ∑ᶠ j : ℤ, form (term (e j)) := by
      apply finsum_congr
      intro j
      have hi : e j = 2 * h - (r : ℤ) - j - 2 := by
        dsimp [e, reflect]
        omega
      have hj : N - 1 - e j = 2 * k - (s : ℤ) - (n - 1 - j) - 2 := by
        rw [hi]
        dsimp [N]
        omega
      simp only [form, term, betaTotal_tmul]
      rw [hj, hi]
    _ = _ := finsum_comp_equiv e (f := fun i => form (term i))

/-- The divided powers of the native total lowering mode split into products of the
two divided powers on pure tensors. -/
theorem divided_total_L1_tmul (a : Matter) (b : Fock) (d : ℕ) :
    DT d (a ⊗ₜ[ℂ] b) =
      ∑ rs ∈ antidiagonal d, DM rs.1 a ⊗ₜ[ℂ] DG rs.2 b := by
  let ml := Module.End.rTensorAlgHom ℂ Matter Fock
  let gl := Module.End.lTensorAlgHom ℂ Fock Matter
  have hcomm : Commute (ml (mode 1)) (gl (BcGhostVirasoro.L 1)) := by
    let matterMap : Module.End ℂ State :=
      TensorProduct.map (mode 1) (LinearMap.id : Module.End ℂ Fock)
    let ghostMap : Module.End ℂ State :=
      TensorProduct.map (LinearMap.id : Module.End ℂ Matter) (BcGhostVirasoro.L 1)
    change matterMap * ghostMap = ghostMap * matterMap
    apply TensorProduct.ext'
    intro u x
    simp only [matterMap, ghostMap, Module.End.mul_apply, TensorProduct.map_tmul,
      LinearMap.id_apply]
  change (((d.factorial : ℂ)⁻¹) • (ml (mode 1) + gl (BcGhostVirasoro.L 1)) ^ d)
    (a ⊗ₜ[ℂ] b) = _
  rw [hcomm.add_pow', LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro rs hrs
  have hd : rs.1 + rs.2 = d := mem_antidiagonal.mp hrs
  have hscalar :
      (d.factorial : ℂ)⁻¹ * (d.choose rs.1 : ℂ) =
        (rs.1.factorial : ℂ)⁻¹ * (rs.2.factorial : ℂ)⁻¹ := by
    rw [← hd, Nat.cast_add_choose]
    have hne (q : ℕ) : (q.factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
    field_simp [hne] <;> ring
  rw [← Nat.cast_smul_eq_nsmul ℂ, LinearMap.smul_apply, smul_smul, hscalar,
    ← map_pow ml, ← map_pow gl, Module.End.mul_apply]
  simp only [dividedTranslation, LinearMap.smul_apply, TensorProduct.smul_tmul_smul] <;> rfl

private theorem sum_antidiagonal_cutoffs {V : Type*} [AddCommMonoid V]
    (A B : ℕ) (f : ℕ × ℕ → V)
    (hzero : ∀ rs, A ≤ rs.1 ∨ B ≤ rs.2 → f rs = 0) :
    (∑ d ∈ Finset.range (A + B), ∑ rs ∈ antidiagonal d, f rs) =
      ∑ rs ∈ Finset.range A ×ˢ Finset.range B, f rs := by
  classical
  let P := Finset.range A ×ˢ Finset.range B
  let D := Finset.range (A + B)
  let degree (rs : ℕ × ℕ) := rs.1 + rs.2
  have hmap : ∀ rs ∈ P, degree rs ∈ D := by
    intro rs hrs
    obtain ⟨hr, hs⟩ := Finset.mem_product.mp hrs
    exact Finset.mem_range.mpr (Nat.add_lt_add (Finset.mem_range.mp hr) (Finset.mem_range.mp hs))
  change (∑ d ∈ D, ∑ rs ∈ antidiagonal d, f rs) = ∑ rs ∈ P, f rs
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  apply Finset.sum_congr rfl
  intro d _
  symm
  apply Finset.sum_subset
  · intro rs hrs
    exact mem_antidiagonal.mpr (Finset.mem_filter.mp hrs).2
  · intro rs hrs hnot
    apply hzero
    have hn : rs ∉ P := fun hp =>
      hnot (Finset.mem_filter.mpr ⟨hp, mem_antidiagonal.mp hrs⟩)
    simpa only [P, Finset.mem_product, Finset.mem_range, not_and_or, not_lt] using hn

/-- The finite matter and ghost adjunctions give the signed BPZ transpose for a pure
tensor source and pure tensor inputs. The weights are integral and the parity power
acts on the first ghost input. Any annihilating descendant cutoffs may be used. -/
theorem betaTotal_mode_adjoint_tmul (a : Matter) (b : Fock) (h k : ℤ) (p A B : ℕ)
    (ha : ∀ r, A ≤ r → DM r a = 0) (hb : ∀ s, B ≤ s → DG s b = 0)
    (hm : ∀ (j : ℤ) (u v : Matter),
      matterBPZ (((stateField a)[[j]]) u) v =
        epsilon h * ∑ r ∈ Finset.range A,
          matterBPZ u (((stateField (DM r a))[[2 * h - (r : ℤ) - j - 2]]) v))
    (hg : ∀ (j : ℤ) (x y : Fock),
      beta (((YG b)[[j]]) x) y =
        epsilon k * ∑ s ∈ Finset.range B,
          beta ((parity ^ p) x) (((YG (DG s b))[[2 * k - (s : ℤ) - j - 2]]) y))
    (n : ℤ) (u v : Matter) (x y : Fock) :
    betaTotal (((Y (a ⊗ₜ[ℂ] b))[[n]]) (u ⊗ₜ[ℂ] x)) (v ⊗ₜ[ℂ] y) =
      epsilon (h + k) * ∑ d ∈ Finset.range (A + B),
        betaTotal (u ⊗ₜ[ℂ] ((parity ^ p) x))
          (((Y (DT d (a ⊗ₜ[ℂ] b)))[[2 * (h + k) - (d : ℤ) - n - 2]])
            (v ⊗ₜ[ℂ] y)) := by
  classical
  let P := Finset.range A ×ˢ Finset.range B
  let signedInput := u ⊗ₜ[ℂ] ((parity ^ p) x)
  let pairAt (m : ℤ) : State →ₗ[ℂ] ℂ :=
    (betaTotal signedInput).comp
      ((LinearMap.applyₗ (R := ℂ) (v ⊗ₜ[ℂ] y)).comp (modesOfStateField Y m))
  let reflectedIndex (d : ℤ) : ℤ := 2 * (h + k) - d - n - 2
  let pairedDescendants (rs : ℕ × ℕ) :=
    pairAt (reflectedIndex ((rs.1 : ℤ) + (rs.2 : ℤ))) (DM rs.1 a ⊗ₜ[ℂ] DG rs.2 b)
  let M (j : ℤ) (r : ℕ) :=
    matterBPZ u (((stateField (DM r a))[[2 * h - (r : ℤ) - j - 2]]) v)
  let G (j : ℤ) (s : ℕ) :=
    beta ((parity ^ p) x) (((YG (DG s b))[[2 * k - (s : ℤ) - (n - 1 - j) - 2]]) y)
  let term (j : ℤ) (rs : ℕ × ℕ) := M j rs.1 * G j rs.2
  have hfinite (rs : ℕ × ℕ) : Function.HasFiniteSupport (fun j => term j rs) := by
    let N := reflectedIndex ((rs.1 : ℤ) + (rs.2 : ℤ))
    let e := reflect (2 * h - (rs.1 : ℤ) - 2)
    let tensorTerm (i : ℤ) : State :=
      ((stateField (DM rs.1 a))[[i]]) v ⊗ₜ[ℂ] ((YG (DG rs.2 b))[[N - 1 - i]]) y
    have hf : Function.HasFiniteSupport (fun i => betaTotal signedInput (tensorTerm i)) :=
      (tensorModes_finite (DM rs.1 a) v (DG rs.2 b) y N).fun_comp (map_zero _)
    have heq (j : ℤ) : term j rs = betaTotal signedInput (tensorTerm (e j)) := by
      have hi : e j = 2 * h - (rs.1 : ℤ) - j - 2 := by
        dsimp [e, reflect]
        omega
      have hj : N - 1 - e j = 2 * k - (rs.2 : ℤ) - (n - 1 - j) - 2 := by
        rw [hi]
        dsimp [N, reflectedIndex]
        omega
      simp only [term, M, G, signedInput, tensorTerm, betaTotal_tmul]
      rw [hj, hi]
    simp_rw [heq]
    exact hf.preimage_embedding e.toEmbedding
  have hsign : epsilon (h + k) = epsilon h * epsilon k :=
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) h k
  have hrow (j : ℤ) :
      matterBPZ (((stateField a)[[j]]) u) v * beta (((YG b)[[n - 1 - j]]) x) y =
        epsilon (h + k) * ∑ rs ∈ P, term j rs := by
    rw [hm j u v, hg (n - 1 - j) x y, hsign]
    change (epsilon h * ∑ r ∈ Finset.range A, M j r) *
        (epsilon k * ∑ s ∈ Finset.range B, G j s) =
      (epsilon h * epsilon k) * ∑ rs ∈ P, term j rs
    have hprod : (∑ r ∈ Finset.range A, M j r) * (∑ s ∈ Finset.range B, G j s) =
        ∑ rs ∈ P, term j rs := by
      change _ = ∑ rs ∈ Finset.range A ×ˢ Finset.range B, term j rs
      rw [Finset.sum_mul, Finset.sum_product]
      simp only [Finset.mul_sum, term]
    rw [← hprod]
    ring
  have hdiag (d : ℕ) :
      pairAt (reflectedIndex d) (DT d (a ⊗ₜ[ℂ] b)) =
        ∑ rs ∈ antidiagonal d, pairedDescendants rs := by
    rw [divided_total_L1_tmul, map_sum]
    apply Finset.sum_congr rfl
    intro rs hrs
    have hd : (rs.1 : ℤ) + (rs.2 : ℤ) = (d : ℤ) := by
      exact_mod_cast (mem_antidiagonal.mp hrs : rs.1 + rs.2 = d)
    simp only [pairedDescendants, hd]
  have hzero (rs : ℕ × ℕ) (hr : A ≤ rs.1 ∨ B ≤ rs.2) : pairedDescendants rs = 0 := by
    rcases hr with hr | hs
    · simp only [pairedDescendants, ha _ hr, TensorProduct.zero_tmul, map_zero]
    · simp only [pairedDescendants, hb _ hs, TensorProduct.tmul_zero, map_zero]
  change _ = epsilon (h + k) * ∑ d ∈ Finset.range (A + B),
    pairAt (reflectedIndex d) (DT d (a ⊗ₜ[ℂ] b))
  rw [betaTotal_mode_tmul]
  calc
    _ = ∑ᶠ j : ℤ, epsilon (h + k) * ∑ rs ∈ P, term j rs := finsum_congr hrow
    _ = epsilon (h + k) * ∑ rs ∈ P, ∑ᶠ j : ℤ, term j rs := by
      -- This exchange uses the union of the finite supports for the pairs in P.
      rw [← finsum_sum_comm P term (fun rs _ => hfinite rs)]
      simpa only [smul_eq_mul] using
        (smul_finsum (epsilon (h + k)) (fun j => ∑ rs ∈ P, term j rs)).symm
    _ = epsilon (h + k) * ∑ rs ∈ P, pairedDescendants rs := by
      congr 1
      apply Finset.sum_congr rfl
      intro rs _
      have hindex : reflectedIndex ((rs.1 : ℤ) + (rs.2 : ℤ)) =
          2 * (h + k) - (rs.1 : ℤ) - (rs.2 : ℤ) - n - 2 := by
        dsimp [reflectedIndex]
        omega
      change (∑ᶠ j : ℤ, M j rs.1 * G j rs.2) =
        betaTotal signedInput
          (((Y (DM rs.1 a ⊗ₜ[ℂ] DG rs.2 b))[[reflectedIndex ((rs.1 : ℤ) + (rs.2 : ℤ))]])
            (v ⊗ₜ[ℂ] y))
      rw [hindex]
      exact reflected_mode_pair a u v b ((parity ^ p) x) y h k n rs.1 rs.2
    _ = _ := by
      simp_rw [hdiag]
      rw [sum_antidiagonal_cutoffs A B pairedDescendants hzero]

#print axioms reflected_mode_pair
#print axioms divided_total_L1_tmul
#print axioms betaTotal_mode_adjoint_tmul

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTTensorBPZ
