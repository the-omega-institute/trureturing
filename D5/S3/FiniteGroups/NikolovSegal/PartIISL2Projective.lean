/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL2Projective
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL2Projective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centre-quotient scalar transfer and projective cardinality cutoff. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL2GeneralLinear
set_option autoImplicit false
namespace NikolovSegal.PartIIA1RootSupply
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

/-- The actual induced action on SL2/Z(SL2); the centre is characteristic. -/
def projectiveAut (beta : MulAut SL(2,F)) : MulAut PSL(2,F) :=
  QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) beta
    ((Subgroup.characteristic_iff_map_eq.mp inferInstance) beta)

private theorem projective_map (beta : MulAut SL(2,F)) (s : SL(2,F)) :
    projectiveAut beta (QuotientGroup.mk' (Subgroup.center _) s) =
      QuotientGroup.mk' (Subgroup.center _) (beta s) := rfl

private theorem projective_corrected_power (beta : MulAut SL(2,F)) (y s : SL(2,F)) (n : ℕ) :
    QuotientGroup.mk' (Subgroup.center _) (((beta*MulAut.conj y⁻¹)^n) s) =
      ((projectiveAut beta*MulAut.conj (QuotientGroup.mk' (Subgroup.center _) y)⁻¹)^n)
        (QuotientGroup.mk' (Subgroup.center _) s) := by
  let p := QuotientGroup.mk' (Subgroup.center SL(2,F))
  have hs : ∀ s, p ((beta*MulAut.conj y⁻¹) s) =
      (projectiveAut beta*MulAut.conj (p y)⁻¹) (p s) := by
    intro s
    simp only [MulAut.mul_apply,MulAut.conj_inv_apply,MulAut.conj_apply]
    rw [← projective_map]
    congr 1
  change p (((beta*MulAut.conj y⁻¹)^n) s) =
    ((projectiveAut beta*MulAut.conj (p y)⁻¹)^n) (p s)
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',MulAut.mul_apply,hs,ih]
    rw [pow_succ',MulAut.mul_apply]
    rfl

/-- Full actual PSL2 scalar PRODUCT for prescribed projective semilinear
GL2 actions, with one projective correction tuple before every target.
The field and length bounds are uniform before the matrix/field tuple. -/
theorem actual_PGL2_semilinear_scalar_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (A : Fin (4*M) → Matrix.GeneralLinearGroup (Fin 2) F)
    (phi : Fin (4*M) → RingAut F) (e : Fin (4*M) → ℕ) :
    PartIIScalarProductInput q (4*M)
      (fun j => projectiveAut (generalLinearAut (A j)*fieldAut (phi j))) e := by
  intro he
  let beta := fun j => generalLinearAut (A j)*fieldAut (phi j)
  let p := QuotientGroup.mk' (Subgroup.center SL(2,F))
  obtain ⟨y,hy⟩ := actual_GL2_semilinear_scalar_product hq hM hF A phi e he
  refine ⟨fun j => p (y j),?_⟩
  intro target
  obtain ⟨s,hs⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(2,F)) target
  obtain ⟨c,hc⟩ := hy s
  refine ⟨fun j => p (c j),?_⟩
  have hm : ∀ f : Fin (4*M) → SL(2,F), p (orderedProduct f) =
      orderedProduct (fun j => p (f j)) := by
    intro f
    simp only [orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def]
  have hh := congrArg p hc
  rw [hm,hs] at hh
  have hv : ∀ j, p ((c j)⁻¹ * (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (c j))) =
      (p (c j))⁻¹ * (((projectiveAut (beta j)*MulAut.conj (p (y j))⁻¹)^(q/e j)) (p (c j))) := by
    intro j
    rw [map_mul,map_inv,projective_corrected_power]
  change orderedProduct (fun j => p ((c j)⁻¹ * (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (c j)))) = target at hh
  simpa only [hv] using hh

private theorem projective_card_bound [Fintype F] [DecidableEq F] :
    Nat.card PSL(2,F) ≤ Fintype.card F ^ 4 := by
  have hq : Nat.card PSL(2,F) ≤ Nat.card SL(2,F) :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center SL(2,F)))
      (QuotientGroup.mk'_surjective _)
  have hsl : Fintype.card SL(2,F) ≤ Fintype.card (Matrix (Fin 2) (Fin 2) F) :=
    Fintype.card_le_of_injective (fun g : SL(2,F) => g.val) Subtype.val_injective
  have hm : Fintype.card (Matrix (Fin 2) (Fin 2) F) = Fintype.card F ^ 4 := by
    change Fintype.card (Fin 2 → Fin 2 → F) = _
    rw [Fintype.card_fun,Fintype.card_fun,Fintype.card_fin]
    simp only [← pow_mul]
  rw [Nat.card_eq_fintype_card (α := SL(2,F))] at hq
  exact hq.trans (hsl.trans hm.le)

/-- A genuine chosen-length rank-one scalar supplier with M,C chosen BEFORE
all finite fields, groups and semilinear matrix/divisor tuples. The cutoff
uses group cardinality exactly as in the full supplier. Classification of
arbitrary PSL2 automorphisms and all other finite-simple families stay open. -/
theorem uniform_PGL2_semilinear_scalar_products (q : ℕ) (hq : 0 < q) :
    ∃ m C : ℕ, 0 < m ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      C < Nat.card PSL(2,F) →
      ∀ A : Fin m → Matrix.GeneralLinearGroup (Fin 2) F,
      ∀ phi : Fin m → RingAut F, ∀ e : Fin m → ℕ,
      PartIIScalarProductInput q m
        (fun j => projectiveAut (generalLinearAut (A j)*fieldAut (phi j))) e := by
  let M := q*(2*q+1)+1
  let K := 2*(2*q+1)^q
  refine ⟨4*M,K^4,by dsimp [M]; positivity,?_⟩
  intro F _ _ _ hcard A phi e
  have hf : K < Fintype.card F := by
    by_contra hn
    have hle : Fintype.card F ≤ K := Nat.le_of_not_gt hn
    have hb := projective_card_bound (F := F)
    have hp := Nat.pow_le_pow_left hle 4
    exact (not_lt_of_ge (hb.trans hp)) hcard
  exact actual_PGL2_semilinear_scalar_product hq (by dsimp [M]; omega) hf A phi e
end NikolovSegal.PartIIA1RootSupply
