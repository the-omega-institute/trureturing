/- GID: D5/S3/Arith/FibonacciAtomic/AffineValuationQueryLowerBound
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/AffineValuationQueryLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimum complete valuation histories force the affine identification budget. -/

import D5.S3.Observer.Budget.ResidueHeightUpperBound
import D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators NumberField
open D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

namespace D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound

abbrev Point (p e d : ℕ) := Fin d → ZMod (p ^ e)
abbrev AffineQuery (p e d : ℕ) := Point p e d × ZMod (p ^ e)

def affineValue {p e d : ℕ} (q : AffineQuery p e d) (x : Point p e d) :
    ZMod (p ^ e) := (∑ i, q.1 i * x i) + q.2

def affineReadout (p e d : ℕ) (q : AffineQuery p e d) (x : Point p e d) : ℕ :=
  residueReadout p e 0 (affineValue q x)

private theorem minimum_response_certificate {X Q : Type} [Fintype X]
    (read : Q → X → ℕ) (U : PassiveProtocol Q (fun _ => ℕ)) :
    ∀ (S : Finset X), S.Nonempty →
    Set.InjOn (runPassiveProtocol read U) (S : Set X) →
    ∃ x ∈ S, ∀ y ∈ S,
      (∀ a ∈ runPassiveProtocol read U x, read a.1 y ≤ a.2) ↔ y = x := by
  classical
  induction U with
  | stop =>
    intro S nonempty inj
    obtain ⟨x, hx⟩ := nonempty
    refine ⟨x, hx, ?_⟩
    intro y hy
    constructor
    · intro _
      exact inj hy hx rfl
    · intro _ a ha
      simp only [runPassiveProtocol, List.not_mem_nil] at ha
  | query q next ih =>
    intro S nonempty inj
    obtain ⟨z, hz, minimal⟩ := S.exists_min_image (read q) nonempty
    let r := read q z
    let S' := S.filter (fun y => read q y = r)
    have nonempty' : S'.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
    have inj' : Set.InjOn (runPassiveProtocol read (next r)) (S' : Set X) := by
      intro a ha b hb equal
      obtain ⟨haS, har⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbS, hbr⟩ := Finset.mem_filter.mp hb
      apply inj haS hbS
      simp only [runPassiveProtocol, har, hbr, equal]
    obtain ⟨x, hx, smaller⟩ := ih r S' nonempty' inj'
    obtain ⟨hxS, hxr⟩ := Finset.mem_filter.mp hx
    refine ⟨x, hxS, ?_⟩
    intro y hy
    simp only [runPassiveProtocol, hxr, List.forall_mem_cons]
    constructor
    · rintro ⟨head, tail⟩
      have hyr : read q y = r := le_antisymm head (minimal y hy)
      exact (smaller y (Finset.mem_filter.mpr ⟨hy, hyr⟩)).mp tail
    · intro equal
      subst y
      exact ⟨hxr.le, (smaller x hx).mpr rfl⟩

/-- Every exact deterministic history selector for arbitrary affine complete
valuation queries has an actual fixed input costing at least d e (p-1).
The trace and fuel functions specify its terminating executions, including
all saturated and correlated responses. -/
theorem affine_valuation_query_lower_bound (p e d : ℕ) (hp : p.Prime)
    (he : 1 ≤ e) (hd : 1 ≤ d)
    : (∀ T : PassiveProtocol (AffineQuery p e d) (fun _ => ℕ),
        Function.Injective (runPassiveProtocol (affineReadout p e d) T) →
        ∃ x : Point p e d,
          d * e * (p - 1) ≤ (runPassiveProtocol (affineReadout p e d) T x).length) ∧
      (∀ (policy : List (Sigma (fun _ : AffineQuery p e d => ℕ)) →
          Sum (AffineQuery p e d) (Point p e d))
        (trace : Point p e d → List (Sigma (fun _ : AffineQuery p e d => ℕ)))
        (fuel : Point p e d → ℕ),
        (∀ x, D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute
          (affineReadout p e d) policy (fuel x) [] x = some (trace x, x)) →
        ∃ x : Point p e d, d * e * (p - 1) ≤ (trace x).length) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have static_bound (m : ℕ)
      (a : Fin m → (Fin d → ZMod (p ^ e)) →+ ZMod (p ^ e))
      (c : Fin m → ZMod (p ^ e)) (r : Fin m → ℕ)
      (hr : ∀ j, r j < e) (xstar : Fin d → ZMod (p ^ e))
      (hdepth : ∀ j, p ^ r j ∣ (a j xstar + c j).val)
      (hsingle : ∀ x : Fin d → ZMod (p ^ e),
        (∀ j, ¬p ^ (r j + 1) ∣ (a j x + c j).val) ↔ x = xstar) :
      d * e * (p - 1) ≤ m := by
    classical
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    letI : Fact p.Prime := ⟨hp⟩
    letI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    letI : NeZero ((p ^ (k + 1) : ℕ) : ℚ) := ⟨by
      exact_mod_cast pow_ne_zero (k + 1) hp.ne_zero⟩
    let K := CyclotomicField (p ^ (k + 1)) ℚ
    letI : IsCyclotomicExtension {p ^ (k + 1)} ℚ K := by
      dsimp [K]
      exact CyclotomicField.isCyclotomicExtension (p ^ (k + 1)) ℚ
    let O := 𝓞 K
    let X := Fin d → ZMod (p ^ (k + 1))
    let C := AddChar X O
    let ζ : K := IsCyclotomicExtension.zeta (p ^ (k + 1)) ℚ K
    have hz : IsPrimitiveRoot ζ (p ^ (k + 1)) :=
      IsCyclotomicExtension.zeta_spec _ _ _
    let ζo : O := ⟨ζ, hz.isIntegral (pow_pos hp.pos _)⟩
    have hzo : ζo ^ (p ^ (k + 1)) = 1 := by
      apply Subtype.ext
      exact hz.pow_eq_one
    let ψ : AddChar (ZMod (p ^ (k + 1))) O :=
      AddChar.zmodChar _ hzo
    let b : Fin m → ℕ := fun j => p ^ (k - r j)
    let χ : Fin m → C := fun j =>
      (ψ.mulShift (b j : ZMod (p ^ (k + 1)))).compAddMonoidHom (a j)
    let u : Fin m → O := fun j => ψ ((b j : ZMod (p ^ (k + 1))) * c j)
    let F : X → O := fun x => ∏ j, (1 - u j * χ j x)
    have phase (n : ℕ) (z : ZMod (p ^ (k + 1))) :
        ψ ((n : ZMod (p ^ (k + 1))) * z) = ζo ^ (n * z.val) := by
      have cast : ((n * z.val : ℕ) : ZMod (p ^ (k + 1))) =
          (n : ZMod (p ^ (k + 1))) * z := by simp
      rw [← cast]
      exact AddChar.zmodChar_apply' hzo _
    have factor (j : Fin m) (x : X) :
        u j * χ j x = ζo ^ (b j * (a j x + c j).val) := by
      change ψ ((b j : ZMod (p ^ (k + 1))) * c j) *
        ψ ((b j : ZMod (p ^ (k + 1))) * a j x) = _
      rw [← AddChar.map_add_eq_mul]
      rw [← mul_add, add_comm (c j)]
      exact phase (b j) _
    have leaf_support (x : X) : F x ≠ 0 ↔ x = xstar := by
      have each (j : Fin m) :
          1 - u j * χ j x ≠ 0 ↔ ¬p ^ (r j + 1) ∣ (a j x + c j).val := by
        rw [factor]
        have root : ζo ^ (b j * (a j x + c j).val) = 1 ↔
            p ^ (k + 1) ∣ b j * (a j x + c j).val := by
          have coe : ζo ^ (b j * (a j x + c j).val) = 1 ↔
              ζ ^ (b j * (a j x + c j).val) = 1 := by
            exact Subtype.ext_iff
          rw [coe, hz.pow_eq_one_iff_dvd]
        have split : p ^ (k + 1) = b j * p ^ (r j + 1) := by
          dsimp [b]
          rw [← pow_add]
          congr 1
          have := hr j
          omega
        rw [sub_ne_zero, ne_comm]
        exact (not_congr root).trans (by
          simp only [split]
          have hb : 0 < b j := pow_pos hp.pos _
          exact not_congr (Nat.mul_dvd_mul_iff_left hb))
      change (∏ j : Fin m, (1 - u j * χ j x)) ≠ 0 ↔ x = xstar
      have prod_iff := Finset.prod_ne_zero_iff (s := Finset.univ)
        (f := fun j : Fin m => 1 - u j * χ j x)
      exact prod_iff.trans (by simpa only [Finset.mem_univ, forall_true_left, each] using hsingle x)
    let ev (x : X) : C →* O :=
      { toFun := fun η => η x
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let E (x : X) : MonoidAlgebra O C →ₐ[O] O :=
      MonoidAlgebra.lift O O C (ev x)
    have average (g : MonoidAlgebra O C) :
        ∑ x : X, E x g = (Fintype.card X : O) * g.coeff 1 := by
      induction g using MonoidAlgebra.induction_linear with
      | zero => simp
      | add g h hg hh =>
          simp only [map_add, Finset.sum_add_distrib, hg, hh,
            MonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
      | single η v =>
          simp only [E, MonoidAlgebra.lift_single, Algebra.smul_def]
          change (∑ x : X, v * η x) = _
          rw [← Finset.mul_sum, AddChar.sum_eq_ite]
          have identity : (1 : C) = 0 := rfl
          by_cases hη : η = 1
          · subst η
            simp [identity, mul_comm]
          · have hηzero : η ≠ 0 := by simpa only [← identity] using hη
            simp [hη, hηzero]
    let g : MonoidAlgebra O C :=
      ∏ j : Fin m, (MonoidAlgebra.single 1 1 - MonoidAlgebra.single (χ j) (u j))
    have evaluates (x : X) : E x g = F x := by
      simp [g, F, E, MonoidAlgebra.lift_single, ev]
      rfl
    have hcard : Fintype.card X = p ^ (d * (k + 1)) := by
      simp only [X, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul]
      congr 1
      exact Nat.mul_comm _ _
    have integral_divisibility : (p ^ (d * (k + 1)) : O) ∣ F xstar := by
      refine ⟨g.coeff 1, ?_⟩
      calc
        F xstar = ∑ x : X, F x := by
          symm
          apply Finset.sum_eq_single xstar
          · intro x _ hxx
            exact not_ne_iff.mp (fun hx => hxx ((leaf_support x).mp hx))
          · simp
        _ = (p ^ (d * (k + 1)) : O) * g.coeff 1 := by
          simpa only [evaluates, hcard, Nat.cast_pow] using average g
    let N : O →* ℕ := Int.natAbsHom.toMonoidHom.comp (Algebra.norm ℤ)
    have deg : Module.finrank ℤ O = p ^ k * (p - 1) := by
      rw [NumberField.RingOfIntegers.rank,
        IsCyclotomicExtension.finrank (n := p ^ (k + 1)) K (Polynomial.cyclotomic.irreducible_rat
          (pow_pos hp.pos _)), Nat.totient_prime_pow_succ hp]
    have norm_factor (j : Fin m) : N (1 - u j * χ j xstar) = p ^ (p ^ k) := by
      obtain ⟨w, hw⟩ := hdepth j
      have hn : ¬p ^ (r j + 1) ∣ (a j xstar + c j).val :=
        (hsingle xstar).mpr rfl j
      have hwp : ¬p ∣ w := by
        intro h
        apply hn
        rw [hw, pow_succ]
        exact Nat.mul_dvd_mul_left _ h
      have hzw : IsPrimitiveRoot (ζ ^ w) (p ^ (k + 1)) :=
        hz.pow_of_coprime w (hp.coprime_pow_of_not_dvd hwp)
      have exponent : b j * (a j xstar + c j).val = w * p ^ k := by
        rw [hw]
        dsimp [b]
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by have := hr j; omega)]
        exact Nat.mul_comm _ _
      have coe_factor : ((1 - u j * χ j xstar : O) : K) =
          1 - (ζ ^ w) ^ (p ^ k) := by
        rw [factor, exponent]
        change 1 - ζ ^ (w * p ^ k) = 1 - (ζ ^ w) ^ (p ^ k)
        rw [pow_mul]
      have norm_sub : |Algebra.norm ℚ ((ζ ^ w) ^ (p ^ k) - 1)| = (p : ℚ) ^ (p ^ k) := by
        have hirr := Polynomial.cyclotomic.irreducible_rat (pow_pos hp.pos (k + 1))
        by_cases hk : k = 0
        · subst k
          by_cases hp2 : p = 2
          · subst p
            rw [hzw.norm_pow_sub_one_two hirr]
            norm_num
          · rw [hzw.norm_pow_sub_one_of_prime_pow_ne_two hirr le_rfl
                (by simpa using hp2)]
            rw [abs_of_nonneg (by positivity : 0 ≤ (p : ℚ) ^ (p ^ 0))]
        · rw [hzw.norm_pow_sub_one_eq_prime_pow_of_ne_zero hirr le_rfl hk]
          rw [abs_of_nonneg (by positivity : 0 ≤ (p : ℚ) ^ (p ^ k))]
      have norm_neg_one : |Algebra.norm ℚ (-1 : K)| = 1 := by
        have eq : (-1 : K) = algebraMap ℚ K (-1) := by simp
        rw [eq, Algebra.norm_algebraMap, abs_pow]
        simp
      have rat : |Algebra.norm ℚ ((1 - u j * χ j xstar : O) : K)| =
          (p : ℚ) ^ (p ^ k) := by
        rw [coe_factor, show (1 : K) - (ζ ^ w) ^ (p ^ k) =
          (-1) * ((ζ ^ w) ^ (p ^ k) - 1) by ring,
          map_mul, abs_mul, norm_neg_one, one_mul, norm_sub]
      dsimp [N]
      apply Nat.cast_injective (R := ℚ)
      rw [Nat.cast_pow]
      calc
        ((Algebra.norm ℤ (1 - u j * χ j xstar)).natAbs : ℚ) =
            |(Algebra.norm ℤ (1 - u j * χ j xstar) : ℚ)| := by
          rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
        _ = (p : ℚ) ^ (p ^ k) := by rw [Algebra.coe_norm_int]; exact rat
    have norm_leaf : N (F xstar) = p ^ (m * p ^ k) := by
      dsimp [F]
      rw [map_prod]
      simp only [norm_factor, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, Nat.mul_comm]
    have norm_scalar : N (p ^ (d * (k + 1)) : O) =
        p ^ (d * (k + 1) * (p ^ k * (p - 1))) := by
      change (Algebra.norm ℤ (p ^ (d * (k + 1)) : O)).natAbs = _
      rw [map_pow, Algebra.norm_natCast, deg, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast]
      rw [← pow_mul]
      congr 1
      ac_rfl
    have numeric : p ^ (d * (k + 1) * (p ^ k * (p - 1))) ∣ p ^ (m * p ^ k) := by
      simpa only [norm_scalar, norm_leaf] using map_dvd N integral_divisibility
    have exponents := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp numeric
    have reordered : d * (k + 1) * (p - 1) * p ^ k ≤ m * p ^ k := by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using exponents
    exact Nat.le_of_mul_le_mul_right reordered (pow_pos hp.pos _)

  have tree_bound (T : PassiveProtocol (AffineQuery p e d) (fun _ => ℕ))
      (identifies : Function.Injective (runPassiveProtocol (affineReadout p e d) T)) :
      ∃ x : Point p e d,
        d * e * (p - 1) ≤ (runPassiveProtocol (affineReadout p e d) T x).length := by
    obtain ⟨x, _, cert⟩ := minimum_response_certificate (affineReadout p e d) T
      Finset.univ Finset.univ_nonempty identifies.injOn
    have same (c y : ZMod (p ^ e)) :
        residueReadout p e c y =
          D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth p e c y := by
      unfold residueReadout D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.depth
      congr 1
      ext i
      simp only [Finset.mem_filter, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff']
    have geometry := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result p e he).1
    have bound (q : AffineQuery p e d) (y : Point p e d) : affineReadout p e d q y ≤ e := by
      rw [affineReadout, same]
      exact (geometry 0 (affineValue q y)).1
    have threshold (q : AffineQuery p e d) (y : Point p e d) (i : ℕ) (hi : i ≤ e) :
        i ≤ affineReadout p e d q y ↔ p ^ i ∣ (affineValue q y).val := by
      rw [affineReadout, same, (geometry 0 (affineValue q y)).2 i hi]
      simp only [ZMod.cast_eq_val, ZMod.val_zero, Nat.cast_zero,
        ZMod.natCast_eq_zero_iff]
    let L := runPassiveProtocol (affineReadout p e d) T x
    have actual : ∀ a ∈ L, affineReadout p e d a.1 x = a.2 := by
      have replay (U : PassiveProtocol (AffineQuery p e d) (fun _ => ℕ)) :
          ∀ a ∈ runPassiveProtocol (affineReadout p e d) U x,
            affineReadout p e d a.1 x = a.2 := by
        induction U with
        | stop => simp [runPassiveProtocol]
        | query q next ih =>
          simp only [runPassiveProtocol, List.forall_mem_cons]
          exact ⟨True.intro, ih _⟩
      exact replay T
    let J := {i : Fin L.length // (L.get i).2 < e}
    let m := Fintype.card J
    let o : Fin m ≃ J := (Fintype.equivFin J).symm
    let q (j : Fin m) := (L.get (o j).val).1
    let r (j : Fin m) := (L.get (o j).val).2
    let a (j : Fin m) : Point p e d →+ ZMod (p ^ e) :=
      { toFun := fun y => ∑ i, (q j).1 i * y i
        map_zero' := by simp
        map_add' := by intro y z; simp [mul_add, Finset.sum_add_distrib] }
    let c (j : Fin m) := (q j).2
    have hr (j : Fin m) : r j < e := (o j).property
    have values (j : Fin m) (y : Point p e d) :
        a j y + c j = affineValue (q j) y := rfl
    have hdepth (j : Fin m) : p ^ r j ∣ (a j x + c j).val := by
      rw [values, ← threshold (q j) x (r j) (hr j).le]
      exact (actual _ (List.get_mem _ _)).ge
    have hsingle (y : Point p e d) :
        (∀ j, ¬p ^ (r j + 1) ∣ (a j y + c j).val) ↔ y = x := by
      rw [← cert y (Finset.mem_univ _)]
      constructor
      · intro outside b hb
        have bi : ∃ i : Fin L.length, L.get i = b := List.mem_iff_get.mp hb
        obtain ⟨i, hi⟩ := bi
        by_cases hbe : b.2 < e
        · let ji : J := ⟨i, by simpa only [hi] using hbe⟩
          obtain ⟨j, hj⟩ := o.surjective ji
          have nondiv := outside j
          rw [values, ← threshold (q j) y (r j + 1) (by have := hr j; omega)] at nondiv
          have hq : q j = b.1 := by dsimp only [q]; rw [hj]; exact congrArg Sigma.fst hi
          have hrr : r j = b.2 := by dsimp only [r]; rw [hj]; exact congrArg (fun z => z.2) hi
          rw [hq, hrr] at nondiv
          omega
        · exact (bound b.1 y).trans (by omega)
      · intro survived j
        rw [values, ← threshold (q j) y (r j + 1) (by have := hr j; omega)]
        have h := survived (L.get (o j).val) (List.get_mem _ _)
        change affineReadout p e d (q j) y ≤ r j at h
        omega
    have count : m ≤ L.length := by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin L.length => (L.get i).2 < e)
    exact ⟨x, (static_bound m a c r hr x hdepth hsingle).trans count⟩
  refine ⟨tree_bound, ?_⟩
  intro policy trace fuel correct
  let X := Point p e d
  let Q := AffineQuery p e d
  let B := Finset.univ.sup (fun x : X => (trace x).length)
  have trace_bound (x : X) : (trace x).length ≤ B :=
    Finset.le_sup (f := fun y : X => (trace y).length) (Finset.mem_univ x)
  let Legal (_ : Finset X) (_ : X) := True
  let tp (_ : Finset X) (_ : X) := 0
  obtain ⟨T, decode, _, runs, _⟩ :=
    (D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.result
      (affineReadout p e d) (fun _ => 1) Legal tp (fun _ => ()) (fun _ => ())
      Finset.univ Finset.univ_nonempty B
      ⟨0, trivial, rfl⟩ (fun _ _ => ⟨0, trivial, rfl⟩)).1 policy
      (fun x _ => ⟨fuel x, trace x, x, correct x, trivial, by simpa [tp] using trace_bound x⟩)
  have identifies : Function.Injective (runPassiveProtocol (affineReadout p e d) T) := by
    intro x y equal
    have hx := (runs x (Finset.mem_univ _) (fuel x) (trace x) x (correct x)).1
    have hy := (runs y (Finset.mem_univ _) (fuel y) (trace y) y (correct y)).1
    rw [equal] at hx
    exact hx.symm.trans hy
  obtain ⟨x, lower⟩ := tree_bound T identifies
  have cost := (runs x (Finset.mem_univ _) (fuel x) (trace x) x (correct x)).2.2.2.2.2.2.1
  refine ⟨x, lower.trans ?_⟩
  simpa [tp] using cost

#print axioms affine_valuation_query_lower_bound

end D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
