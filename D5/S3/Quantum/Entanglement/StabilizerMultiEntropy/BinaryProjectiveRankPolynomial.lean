/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluate the normalized signed rank polynomial of binary projective geometry. -/

import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.FieldTheory.Finiteness
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
noncomputable section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W]

private def qMaps (P : Submodule K V) :
    { f : V →ₗ[K] W // P ≤ f.ker } ≃ ((V ⧸ P) →ₗ[K] W) where
  toFun f := P.liftQ f.1 f.2
  invFun f := ⟨f.comp P.mkQ, by
    intro x hx
    change f (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero P).mpr hx, map_zero]⟩
  left_inv f := by
    apply Subtype.ext
    exact P.liftQ_mkQ f.1 f.2
  right_inv f := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := P.mkQ_surjective x
    simp [Submodule.liftQ_apply]

private theorem annihilator_count (P : Submodule K V) :
    Nat.card { f : V →ₗ[K] W // P ≤ f.ker } =
      Nat.card W ^ (Module.finrank K V - Module.finrank K P) := by
  rw [Nat.card_congr (qMaps P)]
  let b := Module.finBasis K (V ⧸ P)
  rw [← Nat.card_congr (b.constr K).toEquiv, Nat.card_fun, Nat.card_fin]
  have h := P.finrank_quotient_add_finrank
  congr 1
  omega

private def independentMaps (d : Nat) (b : Module.Basis (Fin d) K V) :
    { f : V →ₗ[K] W // Function.Injective f } ≃
      {v : Fin d → W // LinearIndependent K v} where
  toFun f := ⟨f ∘ b, b.linearIndependent.map
    (by rw [LinearMap.ker_eq_bot.mpr f.2]; exact disjoint_bot_right)⟩
  invFun v := ⟨b.constr K v.1, b.injective_constr_of_linearIndependent v.2⟩
  left_inv f := by
    apply Subtype.ext
    apply b.ext
    simp [Function.comp_def]
  right_inv v := by
    apply Subtype.ext
    funext i
    simp

omit [Module.Finite K V] in
private theorem injection_count [Fintype K] [Finite W]
    (d : Nat) (b : Module.Basis (Fin d) K V) (h : d ≤ Module.finrank K W) :
    Nat.card { f : V →ₗ[K] W // Function.Injective f } =
      ∏ j : Fin d, (Fintype.card K ^ Module.finrank K W - Fintype.card K ^ j.val) := by
  rw [Nat.card_congr (independentMaps d b), card_linearIndependent h]


section Finite
variable [Finite V] [Finite W]

private noncomputable instance : Fintype (V →ₗ[K] W) :=
  letI : Finite (V →ₗ[K] W) :=
    Finite.of_injective (fun f : V →ₗ[K] W => (f : V → W)) DFunLike.coe_injective
  Fintype.ofFinite _

private theorem nat_card_finset {A : Type*} (s : Finset A) :
    Nat.card {x // x ∈ s} = s.card := by
  exact Nat.card_eq_fintype_card.trans (Fintype.card_coe s)

omit [Module.Finite K V] [Finite V] [Finite W] in
private theorem maps_avoid_nonzero_iff (f : V →ₗ[K] W) :
    (∀ v : V, v ≠ 0 → f v ≠ 0) ↔ Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hn
    exact h x hn hx
  · intro h v hv he
    apply hv
    have : v ∈ f.ker := he
    rwa [h, Submodule.mem_bot] at this

/-- The actual linear maps avoiding zero on every nonzero vector are
counted by the signed rank sum, without any polynomial hypothesis. -/
private theorem signed_rank_count [Fintype V] [DecidableEq V] :
    (Nat.card { f : V →ₗ[K] W // Function.Injective f } : Int) =
      ∑ U ∈ ((Finset.univ : Finset V).erase 0).powerset,
        (-1 : Int)^U.card * (Nat.card W : Int) ^
          (Module.finrank K V - Module.finrank K (Submodule.span K (U : Set V))) := by
  classical
  let P : Finset V := Finset.univ.erase 0
  let S (v : V) : Finset (V →ₗ[K] W) := Finset.univ.filter (fun f => f v = 0)
  have hP (f : V →ₗ[K] W) : f ∈ P.inf (fun v => (S v)ᶜ) ↔ Function.Injective f := by
    rw [Finset.mem_inf, ← maps_avoid_nonzero_iff]
    simp [P,S]
  have hS (U : Finset V) (f : V →ₗ[K] W) :
      f ∈ U.inf S ↔ Submodule.span K (U : Set V) ≤ f.ker := by
    rw [Finset.mem_inf, Submodule.span_le]
    simp [S,Set.subset_def,LinearMap.mem_ker]
  have hcard (U : Finset V) : (U.inf S).card =
      Nat.card W ^ (Module.finrank K V - Module.finrank K (Submodule.span K (U : Set V))) := by
    calc
      (U.inf S).card = Nat.card {f // f ∈ U.inf S} := (nat_card_finset _).symm
      _ = Nat.card {f : V →ₗ[K] W // Submodule.span K (U : Set V) ≤ f.ker} :=
        Nat.card_congr (Equiv.subtypeEquivRight (hS U))
      _ = _ := annihilator_count _
  calc
    (Nat.card { f : V →ₗ[K] W // Function.Injective f } : Int) =
        ((P.inf (fun v => (S v)ᶜ)).card : Int) := by
      congr 1
      exact (Nat.card_congr (Equiv.subtypeEquivRight hP).symm).trans (nat_card_finset _)
    _ = ∑ U ∈ P.powerset, (-1 : Int)^U.card * ((U.inf S).card : Int) :=
      Finset.inclusion_exclusion_card_inf_compl P S
    _ = _ := by simp [hcard,P]

end Finite

private abbrev Vec (d : Nat) := Fin d → ZMod 2

private def rankPoly (d : Nat) : Polynomial Int :=
  ∑ U ∈ ((Finset.univ : Finset (Vec d)).erase 0).powerset,
    Polynomial.C ((-1 : Int)^U.card) * Polynomial.X ^
      (d - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set (Vec d))))

private def productPoly (d : Nat) : Polynomial Int :=
  ∏ j : Fin d, (Polynomial.X - Polynomial.C ((2 : Int)^j.val))

private theorem eval_pow (d m : Nat) (hdm : d ≤ m) :
    (rankPoly d).eval ((2 : Int)^m) = (productPoly d).eval ((2 : Int)^m) := by
  have hpow : Nat.card (Vec m) = 2^m := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, ZMod.card]
  have h : Module.finrank (ZMod 2) (Vec m) = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hd : Module.finrank (ZMod 2) (Vec d) = d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hc := injection_count (K := ZMod 2) (V := Vec d) (W := Vec m)
      d (Pi.basisFun _ _) (h.symm ▸ hdm)
  rw [h, ZMod.card] at hc
  have he := signed_rank_count (K := ZMod 2) (V := Vec d) (W := Vec m)
  rw [hc,hpow,hd] at he
  simp only [Nat.cast_pow,Nat.cast_ofNat] at he
  simp only [rankPoly, productPoly, Polynomial.eval_finsetSum, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_sub]
  rw [← he, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hi : (2 : Nat)^i.val ≤ 2^m :=
    Nat.pow_le_pow_right (by decide) (Nat.le_trans (Nat.le_of_lt i.isLt) hdm)
  simp only [Int.natCast_sub hi, Nat.cast_pow, Nat.cast_ofNat]

private theorem factor_poly (d : Nat) : rankPoly d = productPoly d := by
  apply Polynomial.eq_of_infinite_eval_eq
  let q (m : Nat) : Int := ((2 : Nat) ^ (m+d) : Nat)
  have hinj : Function.Injective q := by
    intro a b hab
    dsimp [q] at hab
    have hh : (2 : Nat)^(a+d) = 2^(b+d) := by exact_mod_cast hab
    have hm := (Nat.pow_right_injective (by decide : 2 ≤ (2 : Nat))) hh
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨m,rfl⟩
  simp only [Set.mem_ofPred_eq,q,Nat.cast_pow,Nat.cast_ofNat]
  exact eval_pow d (m+d) (Nat.le_add_left _ _)


private theorem factor_eval {R : Type*} [CommRing R] (d : Nat) (q : R) :
    (∑ U ∈ ((Finset.univ : Finset (Vec d)).erase 0).powerset,
      (-1 : R)^U.card * q ^
        (d - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set (Vec d))))) =
      ∏ j : Fin d, (q-(2 : R)^j.val) := by
  have h := congrArg (Polynomial.eval₂RingHom (Int.castRingHom R) q) (factor_poly d)
  simpa only [rankPoly, productPoly, map_sum, map_prod, map_mul, map_sub, map_pow,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, map_neg, map_one,
    Int.coe_castRingHom, Int.cast_ofNat] using h

/-- The signed span-rank sum of the actual nonzero binary vectors. -/
def normalizedRankSum {R : Type*} [Field R] (d : ℕ) (q : R) : R :=
  ∑ U ∈ ((Finset.univ : Finset (Fin d → ZMod 2)).erase 0).powerset,
    (-1 : R)^U.card * (q⁻¹) ^
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set (Fin d → ZMod 2)))

/-- The dimension-indexed family of normalized evaluations, in every field. -/
def normalizedRankFamily (d : ℕ) : ∀ R : Type*, Field R → R → R :=
  fun R F q => @normalizedRankSum R F d q

/-- Exact Walsh normalization at every nonzero size parameter, even though
the counting argument itself sampled integral sizes 2^m. -/
theorem normalized_factor (d : ℕ) :
    let observed := normalizedRankFamily d
    ∀ {R : Type*} [F : Field R] (q : R), q ≠ 0 →
      observed R F q = ∏ j : Fin d, (1-(2 : R)^j.val/q) := by
  dsimp only [normalizedRankFamily, normalizedRankSum]
  intro R F q hq
  have hd : Module.finrank (ZMod 2) (Vec d) = d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  calc
    _ = (q⁻¹)^d * ∑ U ∈ ((Finset.univ : Finset (Vec d)).erase 0).powerset,
        (-1 : R)^U.card * q ^
          (d - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set (Vec d)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      let P := Submodule.span (ZMod 2) (U : Set (Vec d))
      let r := Module.finrank (ZMod 2) P
      have h := P.finrank_quotient_add_finrank
      rw [hd] at h
      have hr : r ≤ d := by dsimp [r]; omega
      change (-1 : R)^U.card * (q⁻¹)^r =
        (q⁻¹)^d * ((-1 : R)^U.card * q^(d-r))
      have hk : (q⁻¹)^d = (q⁻¹)^(d-r)*(q⁻¹)^r := by
        rw [← pow_add, Nat.sub_add_cancel hr]
      have hi : (q⁻¹)^(d-r)*q^(d-r) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hq, one_pow]
      rw [hk]
      calc
        _ = (-1 : R)^U.card * (q⁻¹)^r * 1 := by rw [mul_one]
        _ = (-1 : R)^U.card * (q⁻¹)^r * ((q⁻¹)^(d-r)*q^(d-r)) := by rw [hi]
        _ = _ := by ac_rfl
    _ = (q⁻¹)^d * ∏ j : Fin d, (q-(2 : R)^j.val) := by rw [factor_eval]
    _ = (∏ _ : Fin d, q⁻¹) * ∏ j : Fin d, (q-(2 : R)^j.val) := by simp
    _ = ∏ j : Fin d, (q⁻¹ * (q-(2 : R)^j.val)) := by rw [Finset.prod_mul_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [mul_sub, inv_mul_cancel₀ hq, div_eq_mul_inv, mul_comm q⁻¹]

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
