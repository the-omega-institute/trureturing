import GRH.Lib.General.Groups.VirtualCharacters
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

This file: Central idempotents of group algebras and their tensor products over product groups. -/

open Fint Function MonoidAlgebra Representation

variable {H} [Group H] {e : ℂ[H]} {V} [AddCommGroup V] [Module ℂ V] {ι} [Fintype ι] {G : ι → _}
  [∀ i, Group (G i)] [∀ i, Finite (G i)] {ρ : Representation ℂ (∀ i, G i) V} {x : ∀ i, ℂ[G i]}

lemma IsClassFunction.commute (h : IsClassFunction e.coeff) x :
    Commute x e := ext (by grind [coeff_mul_apply_left, coeff_mul_apply_right, mul_inv_cancel_left])

lemma asAlgebraHom_eq_sum (σ : Representation ℂ H V) {e : ℂ[H]} [Fintype H] :
    σ.asAlgebraHom e = ∑ s, e.coeff s • σ s := Finsupp.sum_fintype _ _ (by simp)

attribute [local simp] Finset.prod_boole Finset.prod_univ_sum Finsupp.single_apply
  Finsupp.sum_fintype coeff_mul_apply_left one_def

/-- e is a central idempotent of the complex group algebra of a group. -/
def IsCentralProj (e : ℂ[H]) := IsIdempotentElem e ∧ IsClassFunction e.coeff

/-- The multiplicative map sending (x_i), x_i in ℂ[G_i], to ⊗x_i in ℂ[∏G_i], whose coefficient
at (s_i) is the product of the coefficients x_i(s_i). -/
@[simps!] noncomputable def piTensorElem : (∀ i, ℂ[G i]) →* ℂ[∀ i, G i] :=
    ⟨⟨fun x ↦ groupAlgElem fun s ↦ ∏ i, (x i).coeff (s i), by aesop⟩, by aesop⟩

/-- For a complex representation ρ of a finite product ∏ G_j of finite groups and x in ℂ[G_i],
the pure tensor with x at i and 1 elsewhere acts as x acts in the restriction of ρ to the
factor G_i. -/
lemma asAlgebraHom_piTensorElem_mulSingle i x : ρ.asAlgebraHom (piTensorElem (Pi.mulSingle i x)) =
  asAlgebraHom (ρ.comp (.mulSingle G i)) x := by rw [asAlgebraHom_eq_sum, asAlgebraHom_eq_sum,
  Fintype.sum_of_injective _ (Pi.mulSingle_injective i)] <;> simp_all [Finset.prod_congr rfl,
  Fintype.prod_eq_mul_prod_compl i, Pi.mulSingle, update_eq_iff, -not_forall]

lemma piTensorElem_apply_eq_zero {v} i (h : asAlgebraHom (ρ.comp (.mulSingle G i)) (x i) v = 0) :
    ρ.asAlgebraHom (piTensorElem x) v = 0 := (by simpa [-one_def] using! update_mul x 1 i 1 (x i) :
  x = _ * Pi.mulSingle i _) ▸ by simp_all [asAlgebraHom_piTensorElem_mulSingle]

lemma piTensorElem_mul_eq_zero {y} i (h : x i * y i = 0) : piTensorElem x * piTensorElem
  y = 0 := by ext; simp [← map_mul, ↓Finset.prod_eq_zero (Finset.mem_univ i), *]

namespace IsCentralProj

lemma one_sub : IsCentralProj e → IsCentralProj (1 - e) := .imp .one_sub (by simp [eq_comm])

lemma map (h : IsCentralProj e) σ : IsCentralProj (mapRingHom H σ e) := h.imp (·.map _) (by aesop)

lemma piTensorElem (h : ∀ i, IsCentralProj (x i)) :
    IsCentralProj (_root_.piTensorElem x) := ⟨.map (funext (h · |>.1) :) _, by simp [(h _).2]⟩
