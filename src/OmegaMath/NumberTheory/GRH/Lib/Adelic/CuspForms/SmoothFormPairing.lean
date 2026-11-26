import OmegaMath.NumberTheory.GRH.Lib.Weil.Unramified.SphericalHecke
import OmegaMath.NumberTheory.GRH.Lib.GLn.SchurModule.WeightRepBasic
import OmegaMath.NumberTheory.GRH.Lib.Adelic.CuspForms.RealConvolution
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

Part of: Congruence subgroups and level structures of adelic groups (known result; see
Lib.Adelic.Unitary.CongruenceLevel).

This file: Integral elements supported off a modulus are congruent to one; block embedding. Smooth
algebraic modular forms on definite unitary groups, right translation, invariant pairing. -/

noncomputable section

open NumberField Matrix Valued
variable {E n n' : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [Fintype n'] {a : 𝓞 E}

lemma sub_one_mem_span_iff_atPlace {g i j} (hg : g ∈ Kf E n) :
  (g.1.1 - 1) i j ∈ Ô E ∙ algebraMap _ _ a ↔ ∀ u, a ∈ u.1 → v (((g.atPlace u).1 - 1) i j) ≤
  u.intValuation a := mem_span_iff_valuation_le.trans (by aesop (add simp mem_Kf))

lemma inf_supportedOn_le_principalLevel {S} (h : ∀ w ∈ S, a ∉ w.1 ∧ a ∉ (star w).1) :
  Kf .. ⊓ Gf.supportedOn n S ≤ principalLevel n a :=
  fun _ ⟨b, c⟩ ↦ ⟨b, by simp +contextual (disch := grind [star_star])
  [↓← mem_span_singleton_iff_exists_mul, ↓sub_one_mem_span_iff_atPlace b, Gf.mem_supportedOn.1 c]⟩

lemma block_embFin {E : Type} [Field E] [CMType E]
    (ε : _ ⊕ Unit ≃ n') γ : U.block ε ((stdSpace E n).embFin γ, 1) =
  stdEmbFin (U.block ε (γ, 1)) := by ext : 2; erw [stdSpace_embFin]; simp [← submatrix_map]

variable {E n : Type} [Field E] [CMType E] [Fintype n]
  (V : Space E n 1) (κ : Weight E)

/-- Algebraic modular forms of weight κ on a definite space V: functions f on G_f with open
right stabiliser and f(γg) = ρ_κ(γ)f(g) for rational γ, ρ_κ = `Space.weightRep`. -/
def Space.forms := SmoothForm V.embFin (V.weightRep κ.1 κ.2)

/-- The representation of the finite adelic unitary group on forms of weight κ on V by right
translation. -/
@[simps! -fullyApplied apply_apply_coe] def Space.formTranslation :=
  (rightRegular ..).subrepresentation (V.forms κ) fun a φ h ↦ (smoothFormRep _ _ a ⟨φ, h⟩).2

variable {V κ} {σ : ℂ →+* ℂ} {B : _ →ₛₗ[σ] _ →ₗ[ℂ] ℂ}
  (hB : ∀ γ v v', B (V.weightRep _ κ.2 γ v) (V.weightRep _ κ.2 γ v') = B v v')

include hB in @[local simp] lemma pairing_mem_smoothInvariants (φ ψ : V.forms κ) : (fun g ↦
  B (φ.1 g) (ψ.1 g)) ∈ smoothInvariants V.Γf := ⟨fun | _, ⟨_, rfl⟩ => by simp [φ.2.2 _, ψ.2.2 _, *],
  (rightStab _ ⊓ _).isOpen_mono (by aesop_cat) (.and φ.2.1 ψ.2.1)⟩

variable (B) in
/-- For a σ-sesquilinear B invariant under the weight κ action of U(J)(E), V definite, the
pairing (φ, φ') ↦ ∫ B(φ(g), φ'(g)) dg of forms, over Γ\G_f with vol K₀ = 1. -/
def smoothPairing : V.forms κ →ₛₗ[σ] V.forms κ →ₗ[ℂ] ℂ := by apply (LinearMap.mk₂'ₛₗ _ _ fun φ φ' ↦
           classIntegral V.Γf (Kf ..) fun g ↦ B (φ.1 g) (φ'.1 g)) <;> simp [classIntegral_add,
  ← Pi.add_def, *]

lemma smoothPairing_formTranslation a φ φ' : smoothPairing B hB (V.formTranslation κ a φ)
  (V.formTranslation κ a φ') = smoothPairing B hB φ φ' := map_classIntegral (.id _) a
