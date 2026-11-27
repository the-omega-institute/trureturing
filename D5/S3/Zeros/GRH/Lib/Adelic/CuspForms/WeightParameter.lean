/- GID: D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/WeightParameter
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/CuspForms/WeightParameter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.CuspForms.WeightParameter. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/CuspForms/WeightParameter.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.SchurOrthogonality
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.Petersson
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

This file: Harish-Chandra parameter versus highest weight; highest coefficient, degree and dimension
on compact unitary groups. -/

open MeasureTheory Complex ComplexConjugate Finset Fintype


variable {Φ n} [Fintype Φ] [Fintype n] {κ e N} {l : Φ → @HCParam n 1} (h : IsHCParam κ e l) (w)
attribute [local grind] hcParameter IsHCParam decrPosition

lemma hcParameter_strictAnti {w} : StrictAnti (hcParameter κ e N w) :=
  strictAnti_nat_of_succ_lt (by grind)

lemma isHCParam_hcParameter n [Fintype n] κ e : IsHCParam κ e fun (w : Φ) i ↦
  hcParameter κ e (card n) w (equivFin n i) :=
  by simp [IsHCParam, Function.Injective, hcParameter_strictAnti.injective.eq_iff, Fin.val_inj]

/-- Fix w. If an integer sequence L has L(p) = L(p+1) + 2κ_w(p+1) + 2 whenever p+1 < N and
equals `hcParameter` at one index q < N, then it equals `hcParameter` at every p < N. -/
lemma hcParameter_eq_of_steps (L : ℕ → ℤ) (hs : ∀ p, p + 1 < N → L p = L (p + 1) + 2 * κ w (p + 1) +
  2) {q} (h₀ : q < N) (h : L q = hcParameter κ e N w q) : ∀ p < N, hcParameter κ e N w p = L p := by
  grind [(Nat.rec (by tauto) (by grind) : ∀ p < N, _ = L p - hcParameter κ e N w p)]

/-- Irreducibility: let each l_w be injective, v = `highestVector` κ l, and x range over the product
of compact unitary groups. If ⟨v, xu⟩ = 0 for all x, or the linear form f kills all xv, then
f(u) = 0. -/
lemma highestVector_cyclic (h : ∀ w, (l w).Injective) e (f : _ →ₗ[ℂ] ℂ) u : (∀ x,
  gramForm (highestVector κ l) (conjWeylRep κ e (s := 1) x u) = 0) ∨ (∀ x,
  f (conjWeylRep κ e (s := 1) x (highestVector κ l)) = 0) → f u = 0 := by
  rintro ⟨⟩ <;> simpa [*, gramForm_highestVector_self, -Fintype.card_pi] using
    schur_orthogonality e f (highestVector κ l) u (highestVector κ l)

include h

lemma IsHCParam.eq_hcParameter i : l w i = hcParameter κ e (card n) w (decrPosition (l w) i) := by
  choose u b H using
    (h w).2; rw [decrPosition, card_bijective (Fin.mk _ <| b ·) (t := Iio ⟨_, b i⟩)] <;> simp [H,
    hcParameter_strictAnti.lt_iff_gt, ↓bijective_iff_injective_and_card]; intro; grind

lemma IsHCParam.exists_decrPosition_eq {q} (hq : q < card n) : ∃ i, decrPosition (l w) i = q ∧
  l w i = hcParameter κ e (card n) w q ∧ ∀ x <
  l w i, q < #{k | x < l w k} := ((exists_equiv_decrPosition (h w).1).choose.surjective ⟨q, hq⟩).imp
  (by grind [eq_hcParameter, card_lt_card, ssubset_iff.2 ⟨·, _⟩])

lemma IsHCParam.hasGap c : (l w).HasGap c := ⟨(h w).1, by grind [h.eq_hcParameter], nofun⟩

/-- If l is twice the Harish-Chandra parameter of (κ, e), then for signs all 1, `lowestKType` of l_w
at i equals e_w + Σ_{p<h<|n|} κ_w(h), p the number of j with l_w(j) > l_w(i). -/
lemma IsHCParam.lowestKType_eq i : (l w).lowestKType i = e w + diagramWeight (rankAt n) κ (w,
  decrPosition (l w) i) := by simp [HCParam.lowestKType, paramAddRho, twoRho]; grind
  [card_lt_add_card_gt_add_one _ i, h.eq_hcParameter]

/-- If l is twice the Harish-Chandra parameter of (κ, e), the matrix coefficient ⟨v⁺, ρ(x)v⁺⟩ of
ρ = `conjWeylRep` on the product of compact groups U(n), at v⁺ = `highestVector`, is ∏_w conj
ψ_{l_w}(x_w), with ψ = `HCParam.dsCoeff`. -/
lemma IsHCParam.gramForm_conjWeylRep_eq_dsCoeff x : gramForm (highestVector κ l)
  (conjWeylRep κ e (s := 1) x (highestVector κ l)) = ∏ w, conj ((l w).dsCoeff (x w)) := by
  choose _ _ using (exists_equiv_decrPosition <| h · |>.1)
  simpa [↓gramForm_apply, ↓star_highestVector, highestVector, *, conjWeylRep,
    conj_weightMinors.trans weightMinors_transpose.symm, mem_maxCompactU, dsCoeff_of_mem_maxCompactU
    (h.hasGap _ 0), funext (h.lowestKType_eq _)] using! weylRep_coeff_eq_prod_weightMinors ..

/-- If l is twice the Harish-Chandra parameter of (κ, e), the product over w of the formal
degrees `formalDegree` of l_w
for the compact group U(n) equals the dimension of the representation of weight κ. -/
lemma IsHCParam.prod_formalDegree : ∏ w, (l w).formalDegree = card (WeylIndex n κ) := inv_injective
  (ofReal_injective (by simpa [h.gramForm_conjWeylRep_eq_dsCoeff, h _, ↓dsCoeff_inv (h.hasGap _ 0),
  formalDegree, Pi.inv_def, ← prod_mul_distrib, conj_mul',
  ← integral_fintype_prod_eq_prod, ← integral_complex_ofReal, gramForm_highestVector_self] using!
  (fun v ↦ schur_orthogonality e (gramForm v) v v v) (highestVector κ l)))
