/- GID: D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetQ4UnitCubes
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Independent cubic characters give normal forms in the original quartic reset orders. -/
import D5.S3.Factorization.Embeddings.FiniteKernelModThree
import D5.S0.Tower.DBonacci.Irreducibility
import D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
import D5.S0.Tower.DBonacci.PerronRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes

open Polynomial NumberField
open D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S3.Factorization.Embeddings.FiniteKernelModThree
open scoped BigOperators

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private abbrev Plus4 := AdjoinRoot (f 4)
private abbrev Minus4 := AdjoinRoot (g 4)
private abbrev Common4 := AdjoinRoot (reduce (g 4))
private abbrev PlusField := AdjoinRoot ((f 4).map (Int.castRingHom ℚ))
private abbrev MinusField := AdjoinRoot ((g 4).map (Int.castRingHom ℚ))

private theorem f_four : f 4 = (X^4-X^3-X^2-X-1 : ℤ[X]) := by
  simp [f, S, Finset.sum_range_succ] <;> ring

private theorem g_four : g 4 = (X^4+X^3+X^2+X+1 : ℤ[X]) := by
  simp [g, S, Finset.sum_range_succ] <;> ring

private theorem common_four :
    reduce (g 4) = (X^4+X^3+X^2+X+1 : (ZMod 2)[X]) := by
  rw [g_four]
  simp [reduce]

private theorem f_monic : (f 4).Monic := by rw [f_four]; monicity!
private theorem g_monic : (g 4).Monic := by rw [g_four]; monicity!
private theorem f_degree : (f 4).natDegree = 4 := by rw [f_four]; compute_degree!
private theorem g_degree : (g 4).natDegree = 4 := by rw [g_four]; compute_degree!
private theorem common_degree : (reduce (g 4)).natDegree = 4 := by
  change ((g 4).map (Int.castRingHom (ZMod 2))).natDegree = 4
  rw [g_monic.natDegree_map, g_degree]

/- The common residue field uses the cyclotomic order certificate. -/
private instance commonIrreducible : Fact (Irreducible (reduce (g 4))) := by
  have hcycl : reduce (g 4) = cyclotomic 5 (ZMod 2) := by
    rw [common_four, cyclotomic_prime]
    norm_num [Finset.sum_range_succ] <;> ring
  have hord (h : Nat.Coprime 2 5) : orderOf (ZMod.unitOfCoprime 2 h) = 4 := by
    apply (orderOf_eq_iff (by norm_num : 0 < 4)).mpr
    constructor
    · apply Units.ext
      norm_num [ZMod.coe_unitOfCoprime] <;> decide
    · intro m hm hpos he
      have he' := congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) he
      interval_cases m <;> norm_num [ZMod.coe_unitOfCoprime] at he' <;> revert he' <;> decide
  refine ⟨ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5)
    (by norm_num) (by simpa only [hcycl] using
      (dvd_rfl : cyclotomic 5 (ZMod 2) ∣ cyclotomic 5 (ZMod 2))) ?_⟩
  rw [hord, common_degree]

private instance plusIrreducible :
    Fact (Irreducible ((f 4).map (Int.castRingHom ℚ))) := by
  refine ⟨?_⟩
  simpa [f, S, Finset.sum_range_succ] using
    (dbonacci_irreducible 4 (by norm_num)).2

private instance minusIrreducible :
    Fact (Irreducible ((g 4).map (Int.castRingHom ℚ))) :=
  ⟨(Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast g_monic.isPrimitive).mp
    (Polynomial.Monic.irreducible_of_irreducible_map
      (Int.castRingHom (ZMod 2)) (g 4) g_monic commonIrreducible.out)⟩

private instance : Field Common4 := AdjoinRoot.instField

private theorem plus_degree : Module.finrank ℚ PlusField = 4 := by
  calc
    Module.finrank ℚ PlusField = ((f 4).map (Int.castRingHom ℚ)).natDegree :=
      (AdjoinRoot.powerBasis' (f_monic.map (Int.castRingHom ℚ))).finrank
    _ = (f 4).natDegree := f_monic.natDegree_map _
    _ = 4 := f_degree

private theorem minus_degree : Module.finrank ℚ MinusField = 4 := by
  calc
    Module.finrank ℚ MinusField = ((g 4).map (Int.castRingHom ℚ)).natDegree :=
      (AdjoinRoot.powerBasis' (g_monic.map (Int.castRingHom ℚ))).finrank
    _ = (g 4).natDegree := g_monic.natDegree_map _
    _ = 4 := g_degree

/- Literal units in the original orders, with polynomial inverse certificates. -/
private def polynomialUnit (p a b : ℤ[X]) (hab : p ∣ a*b-1) : (AdjoinRoot p)ˣ where
  val := AdjoinRoot.mk p a
  inv := AdjoinRoot.mk p b
  val_inv := by
    have hz := AdjoinRoot.mk_eq_zero.mpr hab
    simpa only [map_sub, map_mul, map_one, sub_eq_zero] using hz
  inv_val := by
    rw [mul_comm]
    have hz := AdjoinRoot.mk_eq_zero.mpr hab
    simpa only [map_sub, map_mul, map_one, sub_eq_zero] using hz

def alpha : Plus4ˣ := polynomialUnit (f 4) X (X^3-X^2-X-1) ⟨1, by rw [f_four]; ring⟩
def beta : Minus4ˣ := polynomialUnit (g 4) X (X^4) ⟨X-1, by rw [g_four]; ring⟩
def Bplus : Plus4ˣ := polynomialUnit (f 4) (1+X) (2-X+2*X^2-X^3)
  ⟨-1, by rw [f_four]; ring⟩
def Bminus : Minus4ˣ := polynomialUnit (g 4) (1+X) (-X-X^3)
  ⟨-1, by rw [g_four]; ring⟩

private theorem alpha_val : (alpha : Plus4) = AdjoinRoot.root (f 4) := rfl
private theorem beta_val : (beta : Minus4) = AdjoinRoot.root (g 4) := rfl
private theorem Bplus_val : (Bplus : Plus4) = 1+AdjoinRoot.root (f 4) := by
  simp [Bplus, polynomialUnit]
private theorem Bminus_val : (Bminus : Minus4) = 1+AdjoinRoot.root (g 4) := by
  simp [Bminus, polynomialUnit]

/- Original orders embed by Gauss divisibility. No assertion about equality
with a maximal order or injectivity after taking cube quotients occurs. -/
private def orderToField (p : ℤ[X]) :
    AdjoinRoot p →+* AdjoinRoot (p.map (Int.castRingHom ℚ)) :=
  AdjoinRoot.map (Int.castRingHom ℚ) p _ dvd_rfl

private theorem orderToField_mk (p a : ℤ[X]) :
    orderToField p (AdjoinRoot.mk p a) =
      AdjoinRoot.mk (p.map (Int.castRingHom ℚ)) (a.map (Int.castRingHom ℚ)) := by
  have he : (orderToField p).comp (AdjoinRoot.mk p) =
      (AdjoinRoot.mk (p.map (Int.castRingHom ℚ))).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    ext <;> simp [orderToField]
  exact RingHom.congr_fun he a

private theorem orderToField_injective (p : ℤ[X]) (hp : p.Monic) :
    Function.Injective (orderToField p) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨b, rfl⟩ := AdjoinRoot.mk_surjective y
  apply AdjoinRoot.mk_eq_mk.mpr
  apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast p (a-b) hp.isPrimitive).mpr
  rw [Polynomial.map_sub]
  exact AdjoinRoot.mk_eq_mk.mp (by simpa only [orderToField_mk] using hxy)

private def orderToIntegers (p : ℤ[X]) (hp : p.Monic)
    [Fact (Irreducible (p.map (Int.castRingHom ℚ)))] :
    AdjoinRoot p →+* 𝓞 (AdjoinRoot (p.map (Int.castRingHom ℚ))) := by
  letI := hp.finite_adjoinRoot
  exact
    { toFun := fun x => ⟨orderToField p x,
        (IsIntegral.of_finite ℤ x).map (orderToField p).toIntAlgHom⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }

private theorem orderToIntegers_injective (p : ℤ[X]) (hp : p.Monic)
    [Fact (Irreducible (p.map (Int.castRingHom ℚ)))] :
    Function.Injective (orderToIntegers p hp) := by
  intro x y h
  exact orderToField_injective p hp
    (congrArg (fun z : 𝓞 (AdjoinRoot (p.map (Int.castRingHom ℚ))) => z.val) h)

private def plusIntegerUnits : Plus4ˣ →* (𝓞 PlusField)ˣ := Units.map (orderToIntegers (f 4) f_monic).toMonoidHom
private def minusIntegerUnits : Minus4ˣ →* (𝓞 MinusField)ˣ := Units.map (orderToIntegers (g 4) g_monic).toMonoidHom

/- The real root classification is needed for the signature, not merely the
exhibition of two real roots. The positive argument reuses PerronRoot. -/
private def P (x : ℝ) : ℝ := x^4-x^3-x^2-x-1
private def H (t : ℝ) : ℝ := t^4+t^3-t^2+t-1

private theorem eval_plus (x : ℝ) :
    aeval x ((f 4).map (Int.castRingHom ℚ)) = P x := by
  rw [f_four]
  simp [P]

private theorem positive_root_unique {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hpx : P x = 0) (hpy : P y = 0) : x = y := by
  have he (z : ℝ) (hz : 0 < z) (hpz : P z = 0) : dbonacciReciprocalSum 4 z = 1 := by
    apply (dbonacci_characteristic_iff_reciprocalSum 4 hz.ne').mp
    norm_num [Finset.sum_range_succ]
    dsimp [P] at hpz
    linarith
  exact (dbonacci_reciprocalSum_strictAntiOn 4 (by norm_num)).injOn hx hy
    ((he x hx hpx).trans (he y hy hpy).symm)

private theorem H_strictMono : StrictMonoOn H (Set.Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact (by unfold H; fun_prop : Continuous H).continuousOn
  · intro x hx
    have hxpos : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    have hd : HasDerivAt H (4*x^3+3*x^2-2*x+1) x := by
      convert! ((((hasDerivAt_pow 4 x).add (hasDerivAt_pow 3 x)).sub
        (hasDerivAt_pow 2 x)).add (hasDerivAt_id x)).sub_const 1 using 1 <;>
        first | rfl | (dsimp [H]; ring)
    rw [hd.deriv]
    have hcube := pow_pos hxpos 3
    nlinarith [sq_nonneg (x-(1:ℝ)/3)]

private theorem negative_root_exists : ∃ n : ℝ, -1 < n ∧ n < 0 ∧ P n = 0 := by
  have hc : Continuous H := by unfold H; fun_prop
  obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
    hc.continuousOn (show (0:ℝ) ∈ Set.Icc (H 0) (H 1) by norm_num [H])
  have htpos : 0 < t := by
    by_contra hh
    have : t = 0 := le_antisymm (le_of_not_gt hh) ht.1
    norm_num [this, H] at ht0
  have htone : t < 1 := by
    by_contra hh
    have : t = 1 := le_antisymm ht.2 (le_of_not_gt hh)
    norm_num [this, H] at ht0
  refine ⟨-t, by linarith, by linarith, ?_⟩
  dsimp [P, H] at *
  nlinarith only [ht0]

private def posRoot : ℝ := dbonacciPerronRoot 4
private def negRoot : ℝ := Classical.choose negative_root_exists

private theorem posRoot_spec : 0 < posRoot ∧ P posRoot = 0 := by
  have hs := dbonacciPerronRoot_spec 4 (by norm_num)
  refine ⟨lt_trans zero_lt_one hs.1, ?_⟩
  have he := hs.2.2
  norm_num [Finset.sum_range_succ] at he
  dsimp [P, posRoot]
  linarith

private theorem negRoot_spec : negRoot < 0 ∧ P negRoot = 0 :=
  ⟨(Classical.choose_spec negative_root_exists).2.1,
    (Classical.choose_spec negative_root_exists).2.2⟩

private theorem all_real_roots (x : ℝ) (hx : P x = 0) : x = posRoot ∨ x = negRoot := by
  rcases lt_trichotomy x 0 with hn | hz | hp
  · right
    have hxH : H (-x) = 0 := by dsimp [P, H] at *; nlinarith only [hx]
    have hnH : H (-negRoot) = 0 := by
      have he := negRoot_spec.2
      dsimp [P, H] at *
      nlinarith only [he]
    have he := H_strictMono.injOn (by linarith : 0 < -x)
      (by linarith [negRoot_spec.1] : 0 < -negRoot) (hxH.trans hnH.symm)
    linarith
  · norm_num [hz, P] at hx
  · exact Or.inl (positive_root_unique hp posRoot_spec.1 hx posRoot_spec.2)

/- Explicit bridge from the full set of real roots to all real embeddings. -/
private def realRootsEquiv :
    Fin 2 ≃ {x : ℝ // x ∈ ((f 4).map (Int.castRingHom ℚ)).aroots ℝ} := by
  let r : Fin 2 → {x : ℝ // x ∈ ((f 4).map (Int.castRingHom ℚ)).aroots ℝ} :=
    fun i => ⟨if i = 0 then posRoot else negRoot, by
      rw [Polynomial.mem_aroots]
      refine ⟨plusIrreducible.out.ne_zero, ?_⟩
      rw [eval_plus]
      split_ifs
      · exact posRoot_spec.2
      · exact negRoot_spec.2⟩
  apply Equiv.ofBijective r
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      have he := congrArg Subtype.val hij
      simp [r] at he
      linarith [posRoot_spec.1, negRoot_spec.1]
  · intro x
    have hx : P x.val = 0 := by
      rw [← eval_plus]
      exact (Polynomial.mem_aroots.mp x.property).2
    rcases all_real_roots x.val hx with hp | hn
    · exact ⟨0, Subtype.ext (by simpa [r] using hp.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [r] using hn.symm)⟩

private def realEmbeddingEquiv (K : Type*) [Field K] [NumberField K] :
    (K →+* ℝ) ≃ {φ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ} where
  toFun φ := ⟨Complex.ofRealHom.comp φ, by
    change star (Complex.ofRealHom.comp φ) = Complex.ofRealHom.comp φ
    ext x
    simp⟩
  invFun φ := φ.property.embedding
  left_inv φ := by ext x; rfl
  right_inv φ := by
    apply Subtype.ext
    ext x
    exact NumberField.ComplexEmbedding.IsReal.coe_embedding_apply φ.property x

private theorem plus_signature :
    InfinitePlace.nrRealPlaces PlusField = 2 ∧
      InfinitePlace.nrComplexPlaces PlusField = 1 := by
  classical
  let e : (PlusField →+* ℝ) ≃ Fin 2 :=
    (RingHom.equivRatAlgHom PlusField ℝ).trans
      ((AdjoinRoot.equiv ℝ ℚ _ plusIrreducible.out.ne_zero).trans realRootsEquiv.symm)
  have hr : InfinitePlace.nrRealPlaces PlusField = 2 := by
    rw [← InfinitePlace.card_real_embeddings]
    calc
      Fintype.card {φ : PlusField →+* ℂ // NumberField.ComplexEmbedding.IsReal φ} =
          Fintype.card (PlusField →+* ℝ) := Fintype.card_congr (realEmbeddingEquiv PlusField).symm
      _ = Fintype.card (Fin 2) := Fintype.card_congr e
      _ = 2 := Fintype.card_fin 2
  refine ⟨hr, ?_⟩
  have hd := InfinitePlace.card_add_two_mul_card_eq_rank PlusField
  rw [hr, plus_degree] at hd
  omega

private def plusRealEmbedding : PlusField →+* ℝ :=
  ((AdjoinRoot.equiv ℝ ℚ _ plusIrreducible.out.ne_zero).symm
    (realRootsEquiv 0)).toRingHom

private theorem plus_no_three (u : Plus4ˣ) (hu : u^3 = 1) : u = 1 := by
  let j := orderToField (f 4)
  let e := plusRealEmbedding
  have hp : (e (j (u : Plus4)))^3 = 1 := by
    simpa only [map_pow, Units.val_one, map_one, Units.val_pow_eq_pow_val] using
      congrArg (fun v : Plus4ˣ => e (j (v : Plus4))) hu
  have he : e (j (u : Plus4)) = 1 := by
    apply (show Odd (3:ℕ) by decide).pow_injective
    simpa using hp
  apply Units.ext
  apply orderToField_injective (f 4) f_monic
  apply e.injective
  simpa only [j, Units.val_one, map_one] using he

private theorem betaField_primitive :
    IsPrimitiveRoot (AdjoinRoot.root ((g 4).map (Int.castRingHom ℚ))) 5 := by
  let b := AdjoinRoot.root ((g 4).map (Int.castRingHom ℚ))
  have hb : b^4+b^3+b^2+b+1 = 0 := by
    simpa [b, g_four] using AdjoinRoot.eval₂_root ((g 4).map (Int.castRingHom ℚ))
  have hpow : b^5 = 1 := by linear_combination (b-1)*hb
  have hne : b ≠ 1 := by
    intro h
    norm_num [h] at hb
  exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hpow hne)

private theorem minus_signature :
    InfinitePlace.nrRealPlaces MinusField = 0 ∧
      InfinitePlace.nrComplexPlaces MinusField = 2 := by
  have hr := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
    (by norm_num : 2 < 5) betaField_primitive
  refine ⟨hr, ?_⟩
  have hd := InfinitePlace.card_add_two_mul_card_eq_rank MinusField
  rw [hr, minus_degree] at hd
  omega

private theorem minus_no_three (u : Minus4ˣ) (hu : u^3 = 1) : u = 1 := by
  by_contra hne
  let j := orderToField (g 4)
  have hj : Function.Injective j := orderToField_injective (g 4) g_monic
  have hx : (j (u : Minus4))^3 = 1 := by
    simpa only [map_pow, Units.val_one, map_one, Units.val_pow_eq_pow_val] using
      congrArg (fun v : Minus4ˣ => j (v : Minus4)) hu
  have hn : j (u : Minus4) ≠ 1 := by
    intro h
    apply hne
    apply Units.ext
    apply hj
    simpa only [Units.val_one, map_one] using h
  have ht : IsPrimitiveRoot (j (u : Minus4)) 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hx hn)
  have hd := ht.lcm_totient_le_finrank (K := ℚ) betaField_primitive
    (cyclotomic.irreducible_rat (by decide : 0 < Nat.lcm 3 5))
  have htot : (Nat.lcm 3 5).totient = 8 := by
    rw [show Nat.lcm 3 5 = 3*5 by decide,
      Nat.totient_mul (by decide : Nat.Coprime 3 5),
      Nat.totient_prime Nat.prime_three,
      Nat.totient_prime (by norm_num : Nat.Prime 5)]
  rw [minus_degree, htot] at hd
  omega

private theorem plus_rank : NumberField.Units.rank PlusField = 2 := by
  rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    plus_signature.1, plus_signature.2]

private theorem minus_rank : NumberField.Units.rank MinusField = 1 := by
  rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    minus_signature.1, minus_signature.2]

private theorem plus_cube_dimension :
    Module.Finite (ZMod 3) (ModN (Additive Plus4ˣ) 3) ∧
      Module.finrank (ZMod 3) (ModN (Additive Plus4ˣ) 3) ≤ 2 := by
  simpa only [plus_rank] using embedded_units_modThree plusIntegerUnits
    (Units.map_injective (orderToIntegers_injective (f 4) f_monic)) plus_no_three

private theorem minus_cube_dimension :
    Module.Finite (ZMod 3) (ModN (Additive Minus4ˣ) 3) ∧
      Module.finrank (ZMod 3) (ModN (Additive Minus4ˣ) 3) ≤ 1 := by
  simpa only [minus_rank] using embedded_units_modThree minusIntegerUnits
    (Units.map_injective (orderToIntegers_injective (g 4) g_monic)) minus_no_three

/- The two finite characters. Common4 is the literal common quotient and
evalSeven is the literal alpha=5 homomorphism from the original plus order. -/
private theorem rplus_mk (p : ℤ[X]) :
    rplus 4 (AdjoinRoot.mk (f 4) p) = AdjoinRoot.mk (reduce (g 4)) (reduce p) := rfl
private theorem rminus_mk (p : ℤ[X]) :
    rminus 4 (AdjoinRoot.mk (g 4) p) = AdjoinRoot.mk (reduce (g 4)) (reduce p) := rfl

private def aUnit : Common4ˣ := Units.map (rminus 4).toMonoidHom beta
private def bUnit : Common4ˣ := Units.map (rminus 4).toMonoidHom Bminus

private theorem aUnit_val : (aUnit : Common4) = AdjoinRoot.root (reduce (g 4)) := by
  change rminus 4 (beta : Minus4) = _
  rw [beta_val]
  simpa [reduce] using rminus_mk X

private theorem bUnit_val : (bUnit : Common4) = 1+AdjoinRoot.root (reduce (g 4)) := by
  change rminus 4 (Bminus : Minus4) = _
  rw [Bminus_val, map_add, map_one]
  congr 1
  simpa [reduce] using rminus_mk X

private theorem plus_alpha_residue : Units.map (rplus 4).toMonoidHom alpha = aUnit := by
  apply Units.ext
  change rplus 4 (alpha : Plus4) = (aUnit : Common4)
  rw [alpha_val, aUnit_val]
  simpa [reduce] using rplus_mk X

private theorem plus_B_residue : Units.map (rplus 4).toMonoidHom Bplus = bUnit := by
  apply Units.ext
  change rplus 4 (Bplus : Plus4) = (bUnit : Common4)
  rw [Bplus_val, bUnit_val, map_add, map_one]
  congr 1
  simpa [reduce] using rplus_mk X

private instance : Module.Finite (ZMod 2) Common4 :=
  (g_monic.map (Int.castRingHom (ZMod 2))).finite_adjoinRoot
private instance : Finite Common4 := Module.finite_of_finite (ZMod 2)
private instance : Fintype Common4 := Fintype.ofFinite Common4

private theorem common_card : Fintype.card Common4 = 16 := by
  let b := (AdjoinRoot.powerBasis' (g_monic.map (Int.castRingHom (ZMod 2)))).basis
  calc
    Fintype.card Common4 = Fintype.card (Fin ((reduce (g 4)).natDegree) → ZMod 2) :=
      Fintype.card_congr b.equivFun.toEquiv
    _ = 16 := by simp [common_degree]

private theorem aUnit_fifth : aUnit^5 = 1 := by
  have hcert : reduce (g 4) ∣ ((X : (ZMod 2)[X])^5-1) := by
    refine ⟨X-1, ?_⟩
    rw [common_four]
    ring
  have hz := AdjoinRoot.mk_eq_zero.mpr hcert
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, aUnit_val]
  have he : (AdjoinRoot.root (reduce (g 4)))^5-1 = 0 := by
    simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one] using hz
  exact sub_eq_zero.mp he

private def zK : Common4ˣ := bUnit^5

private theorem common_fifteenth (u : Common4ˣ) : u^15 = 1 := by
  apply Units.ext
  have h := FiniteField.pow_card_sub_one_eq_one (u : Common4) u.ne_zero
  simpa only [common_card, show 16-1 = (15:ℕ) from rfl,
    Units.val_pow_eq_pow_val, Units.val_one] using h

private theorem zK_cube : zK^3 = 1 := by
  simpa only [zK, ← pow_mul] using common_fifteenth bUnit

private theorem zK_ne_one : zK ≠ 1 := by
  have hpoly : (1+(X : (ZMod 2)[X]))^5-1-(X^3+X^2) = reduce (g 4)*X := by
    rw [common_four]
    have hfive : (5 : (ZMod 2)[X]) = 1 := by
      change C (5 : ZMod 2) = C 1
      exact congrArg C (by decide)
    have hnine : (9 : (ZMod 2)[X]) = 1 := by
      change C (9 : ZMod 2) = C 1
      exact congrArg C (by decide)
    ring_nf
    simp only [hfive, hnine, mul_one]
  have he : (zK : Common4)-1 = AdjoinRoot.mk (reduce (g 4)) (X^3+X^2) := by
    have he' := AdjoinRoot.mk_eq_mk.mpr (show reduce (g 4) ∣
      ((1+(X : (ZMod 2)[X]))^5-1)-(X^3+X^2) from ⟨X, hpoly⟩)
    simpa only [map_sub, map_pow, map_add, map_one, AdjoinRoot.mk_X,
      zK, Units.val_pow_eq_pow_val, bUnit_val] using he'
  have hn : AdjoinRoot.mk (reduce (g 4)) (X^3+X^2) ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (g_monic.map (Int.castRingHom (ZMod 2)))
    · intro hz
      have hc := congrArg (fun p : (ZMod 2)[X] => p.coeff 3) hz
      norm_num at hc
    · change ((X : (ZMod 2)[X])^3+X^2).natDegree < (reduce (g 4)).natDegree
      rw [common_degree,
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp),
        Polynomial.natDegree_X_pow]
      norm_num
  intro hz
  apply hn
  rw [← he, hz, Units.val_one, sub_self]

private theorem zK_primitive : IsPrimitiveRoot zK 3 :=
  IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime zK_cube zK_ne_one)

private def evalSeven : Plus4 →+* ZMod 7 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 7)) 5 (by norm_num [f_four]; decide)

private def zSeven : (ZMod 7)ˣ := Units.mk0 4 (by decide)

private theorem zSeven_primitive : IsPrimitiveRoot zSeven 3 := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime
  · apply Units.ext
    norm_num [zSeven] <;> decide
  · intro h
    have he := congrArg (fun u : (ZMod 7)ˣ => (u : ZMod 7)) h
    norm_num [zSeven] at he
    revert he
    decide

private theorem seven_sixth (u : (ZMod 7)ˣ) : u^6 = 1 := by
  simpa using ZMod.units_pow_card_sub_one_eq_one 7 u

/- Oriented logarithm of a d-th power in the order-three roots. The only
group used here is the actual finite residue unit group. -/
private def powerToZpowers {R : Type*} [CommRing R] [IsDomain R]
    (z : Rˣ) (hz : IsPrimitiveRoot z 3) (d : ℕ)
    (hd : ∀ u : Rˣ, (u^d)^3 = 1) : Rˣ →* Subgroup.zpowers z where
  toFun u := ⟨u^d, by rw [hz.zpowers_eq]; exact hd u⟩
  map_one' := Subtype.ext (one_pow d)
  map_mul' u v := Subtype.ext (mul_pow u v d)

private def cubicCharacter {R : Type*} [CommRing R] [IsDomain R]
    (z : Rˣ) (hz : IsPrimitiveRoot z 3) (d : ℕ)
    (hd : ∀ u : Rˣ, (u^d)^3 = 1) : Additive Rˣ →+ ZMod 3 :=
  hz.zmodEquivZPowers.symm.toAddMonoidHom.comp (powerToZpowers z hz d hd).toAdditive

private theorem cubicCharacter_value {R : Type*} [CommRing R] [IsDomain R]
    (z : Rˣ) (hz : IsPrimitiveRoot z 3) (d : ℕ)
    (hd : ∀ u : Rˣ, (u^d)^3 = 1) (u : Rˣ) (i : ℕ) (hi : u^d = z^i) :
    cubicCharacter z hz d hd (Additive.ofMul u) = (i : ZMod 3) := by
  change hz.zmodEquivZPowers.symm (Additive.ofMul
    (⟨u^d, by rw [hz.zpowers_eq]; exact hd u⟩ : Subgroup.zpowers z)) = (i : ZMod 3)
  have he : (⟨u^d, by rw [hz.zpowers_eq]; exact hd u⟩ : Subgroup.zpowers z) =
      ⟨z^i, ⟨(i : ℤ), by simp⟩⟩ :=
    Subtype.ext hi
  rw [he]
  exact hz.zmodEquivZPowers_symm_apply_pow i

private def cK : Additive Common4ˣ →+ ZMod 3 :=
  cubicCharacter zK zK_primitive 5
    (fun u => by simpa only [← pow_mul] using common_fifteenth u)

private def cSeven : Additive (ZMod 7)ˣ →+ ZMod 3 :=
  cubicCharacter zSeven zSeven_primitive 2
    (fun u => by simpa only [← pow_mul] using seven_sixth u)

private theorem cK_a : cK (Additive.ofMul aUnit) = 0 := by
  apply cubicCharacter_value _ _ _ _ aUnit 0
  simpa only [pow_zero] using aUnit_fifth

private theorem cK_b : cK (Additive.ofMul bUnit) = 1 := by
  apply cubicCharacter_value _ _ _ _ bUnit 1
  simp only [zK, pow_one]

private def plusCharacterK : Additive Plus4ˣ →+ ZMod 3 :=
  cK.comp (Units.map (rplus 4).toMonoidHom).toAdditive
private def minusCharacterK : Additive Minus4ˣ →+ ZMod 3 :=
  cK.comp (Units.map (rminus 4).toMonoidHom).toAdditive
private def plusCharacterSeven : Additive Plus4ˣ →+ ZMod 3 :=
  cSeven.comp (Units.map evalSeven.toMonoidHom).toAdditive

private theorem plusCharacterK_alpha : plusCharacterK (Additive.ofMul alpha) = 0 := by
  change cK (Additive.ofMul (Units.map (rplus 4).toMonoidHom alpha)) = 0
  rw [plus_alpha_residue, cK_a]
private theorem plusCharacterK_B : plusCharacterK (Additive.ofMul Bplus) = 1 := by
  change cK (Additive.ofMul (Units.map (rplus 4).toMonoidHom Bplus)) = 1
  rw [plus_B_residue, cK_b]
private theorem minusCharacterK_B : minusCharacterK (Additive.ofMul Bminus) = 1 := cK_b

private theorem plusCharacterSeven_alpha : plusCharacterSeven (Additive.ofMul alpha) = 1 := by
  change cSeven (Additive.ofMul (Units.map evalSeven.toMonoidHom alpha)) = 1
  apply cubicCharacter_value _ _ _ _ _ 1
  apply Units.ext
  norm_num [evalSeven, alpha, polynomialUnit, zSeven, AdjoinRoot.lift_mk, AdjoinRoot.lift_root] <;> decide

private theorem plusCharacterSeven_B : plusCharacterSeven (Additive.ofMul Bplus) = 0 := by
  change cSeven (Additive.ofMul (Units.map evalSeven.toMonoidHom Bplus)) = 0
  apply cubicCharacter_value _ _ _ _ _ 0
  apply Units.ext
  norm_num [evalSeven, Bplus, polynomialUnit, zSeven, AdjoinRoot.lift_mk, AdjoinRoot.lift_root] <;> decide

/- These quotient helpers are applications of ModN's existing universal
property; the integral-coordinate infrastructure stays in ModN.basis. -/
private def cubeClass {U : Type*} [CommGroup U] (u : U) : ModN (Additive U) 3 :=
  ModN.mkQ (G := Additive U) 3 (Additive.ofMul u)

private theorem cubeClass_mul {U : Type*} [CommGroup U] (u v : U) :
    cubeClass (u*v) = cubeClass u + cubeClass v :=
  (ModN.mkQ (G := Additive U) 3).map_add _ _

private theorem cubeClass_pow {U : Type*} [CommGroup U] (u : U) (n : ℕ) :
    cubeClass (u^n) = (n : ZMod 3) • cubeClass u := by
  change ModN.mkQ (G := Additive U) 3 (n • Additive.ofMul u) = _
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

private def quotientCharacter {U : Type*} [CommGroup U] (χ : Additive U →+ ZMod 3) :
    ModN (Additive U) 3 →ₗ[ZMod 3] ZMod 3 :=
  ModN.liftEquiv'.symm ⟨χ, fun a => by rw [nsmul_eq_mul]; exact mul_eq_zero_of_left (by decide) _⟩

private theorem quotientCharacter_class {U : Type*} [CommGroup U]
    (χ : Additive U →+ ZMod 3) (u : U) :
    quotientCharacter χ (cubeClass u) = χ (Additive.ofMul u) := rfl

/- The finite character matrix attains the actual Dirichlet bound.
We use an injective linear synthesis map of equal dimension rather than
retaining a second basis/coordinate framework. Its surjectivity is the
infinite-unit exhaustion step; finite arithmetic alone does not supply it. -/
private def plusSynthesis :
    (ZMod 3 × ZMod 3) →ₗ[ZMod 3] ModN (Additive Plus4ˣ) 3 where
  toFun t := t.1 • cubeClass alpha + t.2 • cubeClass Bplus
  map_add' t s := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' r t := by simp [smul_add, smul_smul]

private theorem plusSynthesis_injective : Function.Injective plusSynthesis := by
  let D := (quotientCharacter plusCharacterSeven).prod (quotientCharacter plusCharacterK)
  have hd : Function.LeftInverse D plusSynthesis := by
    intro t
    apply Prod.ext
    · change quotientCharacter plusCharacterSeven
        (t.1 • cubeClass alpha + t.2 • cubeClass Bplus) = t.1
      simp [quotientCharacter_class, plusCharacterSeven_alpha, plusCharacterSeven_B]
    · change quotientCharacter plusCharacterK
        (t.1 • cubeClass alpha + t.2 • cubeClass Bplus) = t.2
      simp [quotientCharacter_class, plusCharacterK_alpha, plusCharacterK_B]
  exact hd.injective

private theorem plusSynthesis_surjective : Function.Surjective plusSynthesis := by
  letI := plus_cube_dimension.1
  have hlow := LinearMap.finrank_le_finrank_of_injective plusSynthesis_injective
  have hdim : Module.finrank (ZMod 3) (ZMod 3 × ZMod 3) =
      Module.finrank (ZMod 3) (ModN (Additive Plus4ˣ) 3) := by
    have htwo : Module.finrank (ZMod 3) (ZMod 3 × ZMod 3) = 2 := by
      simp only [Module.finrank_prod, Module.finrank_self]
    rw [htwo]
    rw [htwo] at hlow
    exact le_antisymm hlow plus_cube_dimension.2
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    plusSynthesis_injective

private def minusSynthesis : (ZMod 3) →ₗ[ZMod 3] ModN (Additive Minus4ˣ) 3 where
  toFun t := t • cubeClass Bminus
  map_add' t s := add_smul t s _
  map_smul' r t := by simp [smul_smul]

private theorem minusSynthesis_injective : Function.Injective minusSynthesis := by
  have hd : Function.LeftInverse (quotientCharacter minusCharacterK) minusSynthesis := by
    intro t
    change quotientCharacter minusCharacterK (t • cubeClass Bminus) = t
    simp [quotientCharacter_class, minusCharacterK_B]
  exact hd.injective

private theorem minusSynthesis_surjective : Function.Surjective minusSynthesis := by
  letI := minus_cube_dimension.1
  have hlow := LinearMap.finrank_le_finrank_of_injective minusSynthesis_injective
  have hdim : Module.finrank (ZMod 3) (ZMod 3) =
      Module.finrank (ZMod 3) (ModN (Additive Minus4ˣ) 3) := by
    rw [Module.finrank_self] at *
    exact le_antisymm hlow minus_cube_dimension.2
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    minusSynthesis_injective

/-- every original plus-order unit has
the stated form, with the cube witness in that same original order. -/
theorem plus_cube_normal_form (u : Plus4ˣ) :
    ∃ i j : Fin 3, ∃ v : Plus4ˣ, u = alpha^i.val * Bplus^j.val * v^3 := by
  obtain ⟨t, ht⟩ := plusSynthesis_surjective (cubeClass u)
  let i : Fin 3 := ⟨t.1.val, t.1.val_lt⟩
  let j : Fin 3 := ⟨t.2.val, t.2.val_lt⟩
  have hq : cubeClass u = cubeClass (alpha^i.val * Bplus^j.val) := by
    rw [cubeClass_mul, cubeClass_pow, cubeClass_pow]
    simpa only [plusSynthesis, LinearMap.coe_mk, AddHom.coe_mk, i, j, ZMod.natCast_zmod_val] using ht.symm
  obtain ⟨v, hv⟩ := exists_original_cube_of_quotient_eq u (alpha^i.val * Bplus^j.val) hq
  exact ⟨i, j, v, hv⟩

/-- no ambient cube-root witness is used. -/
theorem minus_cube_normal_form (u : Minus4ˣ) :
    ∃ k : Fin 3, ∃ v : Minus4ˣ, u = Bminus^k.val * v^3 := by
  obtain ⟨t, ht⟩ := minusSynthesis_surjective (cubeClass u)
  let k : Fin 3 := ⟨t.val, t.val_lt⟩
  have hq : cubeClass u = cubeClass (Bminus^k.val) := by
    rw [cubeClass_pow]
    simpa only [minusSynthesis, LinearMap.coe_mk, AddHom.coe_mk, k, ZMod.natCast_zmod_val] using ht.symm
  obtain ⟨v, hv⟩ := exists_original_cube_of_quotient_eq u (Bminus^k.val) hq
  exact ⟨k, v, hv⟩


/-- The already oriented character of the literal common residue unit group.
This does not descend through time until a time-annihilation proof is supplied. -/
def residueCharacter : Additive (Common 4)ˣ →+ ZMod 3 := cK

/-- Read the Bplus exponent of THIS integral cube factorization.
The root and the exponent are supplied together, not chosen independently. -/
theorem residueCharacter_plus_factorization (u : Plus4ˣ)
    (i j : Fin 3) (v : Plus4ˣ)
    (hu : u = alpha^i.val * Bplus^j.val * v^3) :
    residueCharacter (Additive.ofMul (Units.map (rplus 4).toMonoidHom u)) =
      (j.val : ZMod 3) := by
  change plusCharacterK (Additive.ofMul u) = (j.val : ZMod 3)
  rw [hu]
  have hthree : (3 : ZMod 3) = 0 := by decide
  simp only [ofMul_mul, ofMul_pow, map_add, map_nsmul,
    plusCharacterK_alpha, plusCharacterK_B, nsmul_eq_mul, Nat.cast_ofNat, hthree,
    mul_zero, mul_one, zero_mul, zero_add, add_zero]





/-- Compatibility consumer. The hypothesis is literal equality
of residues under the existing rplus/rminus maps, not a rho-image premise. -/
theorem compatible_cube_normal_forms (u : Plus4ˣ) (w : Minus4ˣ)
    (hcompat : Units.map (rplus 4).toMonoidHom u = Units.map (rminus 4).toMonoidHom w) :
    ∃ i j k : Fin 3, ∃ v : Plus4ˣ, ∃ t : Minus4ˣ,
      u = alpha^i.val * Bplus^j.val * v^3 ∧
      w = Bminus^k.val * t^3 ∧ (j.val : ZMod 3) = (k.val : ZMod 3) := by
  obtain ⟨i, j, v, hu⟩ := plus_cube_normal_form u
  obtain ⟨k, t, hw⟩ := minus_cube_normal_form w
  have hc : plusCharacterK (Additive.ofMul u) = minusCharacterK (Additive.ofMul w) :=
    congrArg (fun x : Common4ˣ => cK (Additive.ofMul x)) hcompat
  have hthree : (3 : ZMod 3) = 0 := by decide
  have hp : plusCharacterK (Additive.ofMul u) = (j.val : ZMod 3) := by
    rw [hu]
    simp only [ofMul_mul, ofMul_pow, map_add, map_nsmul,
      plusCharacterK_alpha, plusCharacterK_B, nsmul_eq_mul, Nat.cast_ofNat, hthree,
      mul_zero, mul_one, zero_mul, zero_add, add_zero]
  have hm : minusCharacterK (Additive.ofMul w) = (k.val : ZMod 3) := by
    rw [hw]
    simp only [ofMul_mul, ofMul_pow, map_add, map_nsmul,
      minusCharacterK_B, nsmul_eq_mul, Nat.cast_ofNat, hthree, mul_one, zero_mul, add_zero]
  exact ⟨i, j, k, v, t, hu, hw, hp.symm.trans (hc.trans hm)⟩

end D5.S3.ConceptDynamics.Coding.ResetQ4UnitCubes
