import GRH.Lib.Weil.MixedModel.AdelicSum
import GRH.Lib.General.NumberTheory.LocalProduct
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus (known
result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Projection of finite adeles to finitely many places has a continuous additive section. -/


open RestrictedProduct
variable {E : Type} [Field E] [NumberField E] (P : Finset (FinPlace E))

/-- The ring homomorphism sending a finite adele to its components at the places of the finite
set P. -/
@[simps!] noncomputable def evalPlaces : 𝔸f E →+* LocProd P := .pi (evalAt ·.1)

/-- Extension by zero: the additive and multiplicative map from the product of the E_w, w in P, to
the finite adeles, with component 0 outside P. -/
noncomputable def adeleOfLocal :
  LocProd P →ₙ+* 𝔸f E := by use! fun y ↦ inclusion _ _ (𝓖 := .principal Pᶜ) ?_ (.mk
  (fun w ↦ if h : w ∈ P then y ⟨w, h⟩ else 0) ?_) <;> aesop (add safe (by congrm ⟨?_, _⟩))

@[fun_prop] lemma continuous_adeleOfLocal : Continuous (adeleOfLocal P) :=
  (continuous_inclusion (R := _) (by
  simp)).comp (continuous_rng_of_principal.2 (continuous_pi fun _ ↦ by simp; split <;> fun_prop))

@[fun_prop] lemma continuous_evalPlaces : Continuous (evalPlaces P) :=
  continuous_pi (continuous_evalAt ·.1)

@[simp] lemma evalPlaces_adeleOfLocal x : evalPlaces P (adeleOfLocal P x) = x :=
  funext (dite_eq_left ·.2)

lemma adeleOfLocal_evalPlaces x : adeleOfLocal P (evalPlaces P x) =
  idem P * x := by aesop (add simp idem_apply)
