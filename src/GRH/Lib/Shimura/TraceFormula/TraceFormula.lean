import GRH.Lib.Shimura.HeckeTower.GroupRingOperators
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish (known
result; see Lib.Shimura.TraceFormula.MarkedEqDefinite).

This file: Trace of a (twisted) Hecke operator on algebraic forms as sum over representatives. -/

open Function LinearMap Finset
attribute [local simp] cosetFn asAlgebraHom_eq_sum_support sum_mul Finsupp.single_apply

/-- Trace formula. M: the F : G → W with F(e(γ)g) = ρ(γ)F(g), right K-invariant, zero on D. The
sets {γ : e(γ)r_iK = gK} are finite, empty for g ∈ D, with ∑_i w_i·cardinality = 1 for g ∉
D; σ⁻¹K = K; TF = a·(s∘F∘σ⁻¹), a ∈ A[G] acting by right translation. Then dim M < ∞, tr T =
∑_i w_i ∑_γ φ(r_i⁻¹σ(e(γ)r_i)) tr(sρ(γ)), φ the image of a in A[G/K]. -/
lemma trace_eq_weighted_sum {A G Γ W M I} [Group G] [Group Γ] {e : Γ →* G} {K} [Field A]
  [AddCommGroup W] [Module A W] [Module.Finite A W] [AddCommGroup M] [Module A M] [Fintype I] {ρ :
  Representation A Γ W} {s T D a} (r : I → G) (w : I → A) (ι : M →ₗ[A] G → W) (hM : ι.range =
  ρ.coindV e ⊓ .pi D ⊥ ⊓ levelSpace (rightRegular ..) K) (σ : G ≃* G) (S : I → G → _) (hS : ∀ i g γ,
  γ ∈ S i g ↔ g⁻¹ * (e γ * r i) ∈ K) (hw : ∀ g, if g ∉ D then ∑ i, w i * #(S i g) = 1 else ∀ i,
  S i g = ∅) (hT : ∀ ψ, ι (T ψ) = (rightRegular ..).asAlgebraHom a (s <| ι ψ <| σ.symm ·)) (hσ :
  K.comap ↑σ = K) (hι : Injective ι := by simp) : Module.Finite A M ∧ trace A M T = ∑ i, w i * ∑ᶠ γ,
  cosetFn K a ((r i)⁻¹ * σ (e γ) * σ (r i)) * (s * ρ γ).trace A W := by
  let J i := codRestrictOfInjective (pi (S i · |>.sum ρ)) ι hι fun v ↦ by
    simp [hM, funext_iff]; use ⟨fun γ g ↦ sum_equiv (.mulLeft γ⁻¹) ?_ ?_, by grind⟩,
      fun _ _ _ ↦ sum_equiv 1 ?_ ?_ <;> simp_all [mul_assoc, mul_mem_cancel_left]
  have hJ : ∑ i, w i • J i ∘ₗ proj (r i) ∘ₗ ι = 1 := ext fun ψ ↦ hι (by
    ext g; have ⟨c, d⟩ := hM.le ⟨ψ, rfl⟩; simp at c
    simp +contextual [J, smul_comm (w _), ← smul_assoc, ← sum_smul, ← c.1, ← hS,
      fun x h ↦ by simpa using congrFun (d ⟨g⁻¹ * x, h⟩) g]
    grind [one_smul, smul_zero])
  have := Module.Finite.of_surjective (lsum A _ A J) (⟨(w · • _), by simpa using congr($hJ ·)⟩)
  rw [← mul_one T, ← hJ]; simp [mul_sum, this]; congr!
  erw [← trace_comp_cycle, show _ ∘ₗ _ = ∑ g ∈ _, a.coeff g • s * (S ..).sum ρ by aesop]
  simp [mul_sum, sum_sigma']; rw [← finsum_sum_filter (·.2)]
  simp [sum_filter, sum_sigma, mul_assoc, ← QuotientGroup.eq, ↓K.mem_comap, hσ ▸ hS]
