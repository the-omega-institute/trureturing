/- GID: D5/S3/Quantum/Analysis/AsynchronousTensorMass
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/AsynchronousTensorMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire fixed dual of an asynchronous algebraic tensor sum on proper-cone data. -/

import D5.S3.Quantum.Analysis.AsynchronousMassRigidity

/-! # Fixed mass functionals on the purely algebraic tensor carrier -/

namespace D5.S3.Quantum.AsynchronousTensorMass

open Function Set
open scoped BigOperators TensorProduct

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [Nontrivial A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The asynchronous sum on the actual algebraic tensor product. No tensor cone is selected. -/
noncomputable def asynchronous (Phi : A →ₗ[ℝ] A) (alpha : ι → ℝ) :
    (⨂[ℝ] _i : ι, A) →ₗ[ℝ] (⨂[ℝ] _i : ι, A) :=
  ∑ j, alpha j • PiTensorProduct.map
    (fun i : ι => if i = j then Phi else LinearMap.id)

/-- The algebraic tensor power of the original mass functional. -/
noncomputable def tensorMass (u : Module.Dual ℝ A) : Module.Dual ℝ (⨂[ℝ] _i : ι, A) :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℝ ι ℝ).compLinearMap (fun _ => u))

private theorem slot_tprod (Phi : A →ₗ[ℝ] A) (j : ι) (a : ι → A) :
    PiTensorProduct.map (fun i : ι => if i = j then Phi else LinearMap.id)
      (PiTensorProduct.tprod ℝ a) =
      PiTensorProduct.tprod ℝ (update a j (Phi (a j))) := by
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases hij : i = j
  · subst i; simp
  · simp [hij, Function.update_of_ne hij]

/-- On a pure tensor, the asynchronous sum replaces one slot at a time. -/
theorem asynchronous_tprod (Phi : A →ₗ[ℝ] A) (alpha : ι → ℝ) (a : ι → A) :
    asynchronous Phi alpha (PiTensorProduct.tprod ℝ a) =
      ∑ j, alpha j • PiTensorProduct.tprod ℝ (update a j (Phi (a j))) := by
  simp only [asynchronous, LinearMap.sum_apply, LinearMap.smul_apply, slot_tprod]

/-- The full real dual fixed space of the positive asynchronous algebraic tensor sum
is exactly the line of the original tensor mass. This proves the fixed-space clause of
source (79.6); it makes no spectral or algebraic-multiplicity assertion. -/
theorem fixed_tensor_dual (C : ProperCone ℝ A) (u : Module.Dual ℝ A)
    (hgen : Submodule.span ℝ (C : Set A) = ⊤)
    (hpos : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (Phi : A →ₗ[ℝ] A) (hPhiPos : ∀ x ∈ C, Phi x ∈ C)
    (hmass : u.comp Phi = u)
    (hdual : ∀ f : Module.Dual ℝ A, f.comp Phi = f → ∃ c : ℝ, f = c • u)
    (alpha : ι → ℝ) (hAlpha : ∀ i, 0 < alpha i) (hsum : ∑ i, alpha i = 1)
    (g : Module.Dual ℝ (⨂[ℝ] _i : ι, A)) :
    g.comp (asynchronous Phi alpha) = g ↔ ∃ c : ℝ, g = c • tensorMass (ι := ι) u := by
  classical
  obtain ⟨hne, hcompact, hconv, hspan⟩ :=
    AsynchronousMassRigidity.entire_base_geometry C u hgen hpos
  let K := Foundation.CircuitBalancedConfirmation.base C.toPointedCone u
  have huPhi (x : A) : u (Phi x) = u x := congrArg (fun f : Module.Dual ℝ A => f x) hmass
  have hinv : MapsTo Phi K K := by
    intro x hx
    exact ⟨hPhiPos x hx.1, (huPhi x).trans hx.2⟩
  constructor
  · intro hfixed
    let F := g.compMultilinearMap (PiTensorProduct.tprod ℝ)
    have hh : ∀ a ∈ Set.pi Set.univ (fun _ : ι => K),
        F a = ∑ i, alpha i * F (update a i (Phi (a i))) := by
      intro a _
      have he := congrArg (fun f : Module.Dual ℝ (⨂[ℝ] _i : ι, A) =>
        f (PiTensorProduct.tprod ℝ a)) hfixed
      change g (asynchronous Phi alpha (PiTensorProduct.tprod ℝ a)) =
        g (PiTensorProduct.tprod ℝ a) at he
      rw [asynchronous_tprod, map_sum] at he
      simpa only [F, LinearMap.compMultilinearMap_apply, map_smul, smul_eq_mul] using he.symm
    obtain ⟨c, hc⟩ := AsynchronousMassRigidity.multilinear_mass_factorization
      Phi u hmass hdual hcompact hne hconv hspan hinv (fun _ hx => hx.2)
      alpha hAlpha hsum F hh
    refine ⟨c, ?_⟩
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    simpa [F, tensorMass, MultilinearMap.mkPiAlgebra_apply, smul_eq_mul] using hc a
  · rintro ⟨c, rfl⟩
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    have hprod (j : ι) : (∏ i, u (update a j (Phi (a j)) i)) = ∏ i, u (a i) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hij : i = j
      · subst i; simpa using huPhi (a j)
      · simp [Function.update_of_ne hij]
    change (c • tensorMass u) (asynchronous Phi alpha (PiTensorProduct.tprod ℝ a)) =
      (c • tensorMass u) (PiTensorProduct.tprod ℝ a)
    rw [asynchronous_tprod]
    simp only [LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, map_sum, map_smul, slot_tprod, tensorMass,
      PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, smul_eq_mul]
    simp only [hprod, ← Finset.sum_mul, hsum, one_mul]


example (Phi : A →ₗ[ℝ] A) (alpha : ι → ℝ) (hsum : ∑ i, alpha i = 1)
    {v : A} (hv : Phi v = -v) (hvne : v ≠ 0) :
    asynchronous Phi alpha (PiTensorProduct.tprod ℝ (fun _ : ι => v)) =
        -PiTensorProduct.tprod ℝ (fun _ : ι => v) ∧
      PiTensorProduct.tprod ℝ (fun _ : ι => v) ≠ 0 := by
  constructor
  · rw [asynchronous_tprod]
    simp only [hv, MultilinearMap.map_update_neg, Function.update_eq_self,
      ← Finset.sum_smul, hsum, one_smul]
  · obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hvne
    have he : tensorMass f (PiTensorProduct.tprod ℝ (fun _ : ι => v)) = 1 := by
      simp [tensorMass, hf, MultilinearMap.mkPiAlgebra_apply]
    intro hz
    rw [hz, map_zero] at he
    exact zero_ne_one he

end D5.S3.Quantum.AsynchronousTensorMass
