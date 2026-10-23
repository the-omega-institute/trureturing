/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentWard
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentWard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native full-source current Ward identity for corrected half-Fock fields. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality
open LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCurrentCorrection
open LatticeHalfFockFiniteCorrection
open LatticeHalfFockFockNormalField
open LatticeHalfFockCorrectedField
open LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents
open MvPolynomial
open scoped BigOperators TensorProduct

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

private theorem prod_shift (a : ℂ) (order : ℕ) :
    a * ∏ offset ∈ Finset.range order, (a - 1 - (offset : ℂ)) =
      ∏ offset ∈ Finset.range (order + 1), (a - (offset : ℂ)) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  ring


private theorem jetScalar_contraction (q : ℤ) (order : ℕ) :
    LatticeHalfFock.frequency q * jetScalar order (-q - 1) =
      (order + 1 : ℂ) * Ring.choose (LatticeHalfFock.frequency q) (order + 1) := by
  rw [jetScalar, Ring.choose_eq_smul, ← Polynomial.aeval_eq_smeval,
    Polynomial.aeval_def, ← Polynomial.eval_map, descPochhammer_map,
    descPochhammer_eval_eq_prod_range]
  simp only [smul_eq_mul, div_eq_mul_inv, LatticeHalfFock.frequency,
    Int.cast_neg, Int.cast_sub, Int.cast_one]
  have hfreq : (↑q + 1 * 2⁻¹ : ℂ) = (q : ℂ) + 1 / 2 := by ring
  simp_rw [hfreq]
  have hprod : (∏ x ∈ Finset.range order,
      (-(-↑q - 1) - 3 * 2⁻¹ - (x : ℂ))) =
      ∏ x ∈ Finset.range order,
        ((q : ℂ) + 1 / 2 - 1 - (x : ℂ)) := by
    apply Finset.prod_congr rfl
    intro x hx
    ring
  rw [hprod]
  rw [← prod_shift ((q : ℂ) + 1 / 2) order]
  have hfactorial : (order.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero order
  have hsuccessor : (order + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero order
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp [hfactorial, hsuccessor]
  push_cast
  ring

private theorem jetCurrent_commutator_apply
    (D : LatticeData) (hu : IsUnit D.G.det)
    (i l : Fin D.rank) (q m : ℤ) (order : ℕ)
    (v : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        (jetCurrent D hu (l, order) m v) -
      jetCurrent D hu (l, order) m
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q v) =
      (if q + m + 1 = 0 then
        (jetScalar order m * LatticeHalfFock.frequency q * (D.G i l : ℂ)) • v
       else 0) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul polynomial ground =>
    simp only [jetCurrent, LinearMap.smul_apply, map_smul,
      LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
      TensorProduct.map_tmul, LinearMap.id_apply]
    rw [← smul_sub, ← TensorProduct.sub_tmul,
      LatticeHalfFock.current_heisenberg_apply]
    split_ifs <;>
      simp [TensorProduct.smul_tmul', smul_smul, mul_comm, mul_left_comm, mul_assoc]
  | add first second firstProof secondProof =>
    simp only [map_add]
    calc
      _ = ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
            ((jetCurrent D hu (l, order) m) first) -
          (jetCurrent D hu (l, order) m)
            ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q) first)) +
          ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
            ((jetCurrent D hu (l, order) m) second) -
          (jetCurrent D hu (l, order) m)
            ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q) second)) := by abel
      _ = _ := by
        rw [firstProof, secondProof]
        by_cases h : q + m + 1 = 0 <;> simp [h, smul_add]

private theorem singleton_term_commutator
    (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (j : Index D) (F : NativeField D hu)
    (q e m : ℤ) (x : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        (flatTerm D hu F [j] e x (m, ())) -
      flatTerm D hu F [j] e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) (m, ()) =
      if m < 0 then
        jetCurrent D hu j m
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
              (F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3) x) -
            F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3)
              (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x)) +
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q * jetCurrent D hu j m -
            jetCurrent D hu j m * LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
            (F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3) x)
      else
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
            (F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3)
              (jetCurrent D hu j m x)) -
          F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3)
            (jetCurrent D hu j m
              (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x)) := by
  by_cases hm : m < 0
  · simp only [flatTerm, flatCoefficient, if_pos hm, Module.End.mul_apply,
      LinearMap.sub_apply, map_sub]
    abel
  · simp only [flatTerm, flatCoefficient, if_neg hm, Module.End.mul_apply]


private theorem finsum_finset_exchange
    {ι V : Type*} [AddCommMonoid V]
    (S : Finset ι) (f : ℤ → V) (g : ℤ → ι → V)
    (hf : Function.HasFiniteSupport f)
    (hg : ∀ a ∈ S, Function.HasFiniteSupport (fun m => g m a))
    (heq : ∀ m, f m = ∑ a ∈ S, g m a) :
    (∑ᶠ m : ℤ, f m) = ∑ a ∈ S, ∑ᶠ m : ℤ, g m a := by
  rw [finsum_congr heq]
  exact finsum_sum_comm S g hg


private theorem finsum_finset_exchange_nat
    {ι V : Type*} [AddCommMonoid V]
    (S : Finset ι) (f : ℕ → V) (g : ℕ → ι → V)
    (hf : Function.HasFiniteSupport f)
    (hg : ∀ a ∈ S, Function.HasFiniteSupport (fun n => g n a))
    (heq : ∀ n, f n = ∑ a ∈ S, g n a) :
    (∑ᶠ n : ℕ, f n) = ∑ a ∈ S, ∑ᶠ n : ℕ, g n a := by
  rw [finsum_congr heq]
  exact finsum_sum_comm S g hg


private theorem singleton_coefficient_local (D : LatticeData) (hu : IsUnit D.G.det)
    (F : NativeField D hu) (j : Index D) (e : ℤ) (v : ActualTensor D hu) :
    (singletonLinear D hu j F).coeff e v =
      ∑ᶠ m : ℤ, flatTerm D hu F [j] e v (m, ()) := by
  exact singletonLinear_coefficient D hu F j e v


private theorem singleton_current_ward_of_sum
    (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (j : Index D) (F : NativeField D hu)
    (S : Finset ℕ) (coefficient : ℕ → ℂ) (shift : ℕ → ℤ)
    (fields : ℕ → NativeField D hu) (q e : ℤ) (x : ActualTensor D hu)
    (commutator : ∀ (z : ℤ) (v : ActualTensor D hu),
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q (F.coeff z v) -
        F.coeff z (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q v) =
        ∑ n ∈ S, coefficient n • (fields n).coeff (z + shift n) v) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        ((singletonLinear D hu j F).coeff e x) -
      (singletonLinear D hu j F).coeff e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) =
      (∑ n ∈ S, coefficient n •
        (singletonLinear D hu j (fields n)).coeff (e + shift n) x) +
      ((j.2 + 1 : ℂ) * Ring.choose (LatticeHalfFock.frequency q) (j.2 + 1) *
        (D.G i j.1 : ℂ)) •
        F.coeff (e - (2*q + 1) + 2*(j.2 : ℤ) + 2) x := by
  classical
  let term : ℤ → ActualTensor D hu := fun m =>
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        (flatTerm D hu F [j] e x (m, ())) -
      flatTerm D hu F [j] e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) (m, ())
  let contraction : ℤ → ActualTensor D hu := fun m =>
    if q + m + 1 = 0 then
      (jetScalar j.2 m * LatticeHalfFock.frequency q * (D.G i j.1 : ℂ)) •
        F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3) x
    else 0
  let main : ℤ → ActualTensor D hu := fun m =>
    if m < 0 then
      jetCurrent D hu j m
        (∑ n ∈ S, coefficient n •
          (fields n).coeff (e + 2*m + 2*(j.2 : ℤ) + 3 + shift n) x)
    else
      ∑ n ∈ S, coefficient n •
        (fields n).coeff (e + 2*m + 2*(j.2 : ℤ) + 3 + shift n)
          (jetCurrent D hu j m x)
  let summand : ℤ → ℕ → ActualTensor D hu := fun m n =>
    coefficient n • flatTerm D hu (fields n) [j] (e + shift n) x (m, ())
  have term_eq (m : ℤ) : term m = main m + contraction m := by
    dsimp [term]
    rw [singleton_term_commutator]
    by_cases hm : m < 0
    · simp only [main, contraction, if_pos hm]
      rw [commutator]
      simp only [map_sum, map_smul, Finset.smul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro n hn
        rw [show e + 2 * m + 2 * (j.2 : ℤ) + 3 + shift n =
            (e + shift n) + 2 * m + 2 * (j.2 : ℤ) + 3 by ring]
      · change
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q *
              jetCurrent D hu j m - jetCurrent D hu j m *
                LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
            (F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3) x) = _
        simpa [Module.End.mul_apply] using
          jetCurrent_commutator_apply D hu i j.1 q m j.2
            (F.coeff (e + 2*m + 2*(j.2 : ℤ) + 3) x)
    · simp only [main, contraction, if_neg hm]
      let z : ℤ := e + 2*m + 2*(j.2 : ℤ) + 3
      have hsource := commutator z (jetCurrent D hu j m x)
      have hjetx := jetCurrent_commutator_apply D hu i j.1 q m j.2 x
      have hjetx' : (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q *
          jetCurrent D hu j m - jetCurrent D hu j m *
            LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
          x =
          if q + m + 1 = 0 then
            (jetScalar j.2 m * LatticeHalfFock.frequency q *
              (D.G i j.1 : ℂ)) • x else 0 := by
        simpa [Module.End.mul_apply] using hjetx
      change
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
              (F.coeff z (jetCurrent D hu j m x)) -
            F.coeff z (jetCurrent D hu j m
              (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x)) = _
      calc
        _ = (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
              (F.coeff z (jetCurrent D hu j m x)) -
            F.coeff z (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
              (jetCurrent D hu j m x))) +
            F.coeff z ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q *
              jetCurrent D hu j m - jetCurrent D hu j m *
                LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q) x) := by
                change _ = _ + F.coeff z
                  (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
                    (jetCurrent D hu j m x) -
                    jetCurrent D hu j m
                      (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x))
                rw [map_sub]
                abel
        _ = (∑ n ∈ S, coefficient n •
              (fields n).coeff (z + shift n) (jetCurrent D hu j m x)) +
            F.coeff z ((if q + m + 1 = 0 then
              (jetScalar j.2 m * LatticeHalfFock.frequency q * (D.G i j.1 : ℂ)) • x
              else 0)) := by
                rw [hsource]
                congr 1
                change F.coeff z ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q *
                  jetCurrent D hu j m - jetCurrent D hu j m *
                    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q) x) = _
                rw [hjetx']
        _ = _ := by
          apply congrArg₂ (· + ·)
          · apply Finset.sum_congr rfl
            intro n hn
            rw [show z + shift n = e + 2*m + 2*(j.2 : ℤ) + 3 + shift n by rfl]
          · by_cases hqm : q + m + 1 = 0
            · simp only [if_pos hqm, map_smul, smul_eq_mul]
              dsimp [z]
            · simp [hqm]
  have finiteTerm : Function.HasFiniteSupport term := by
    have tupleFinite {G : ModeTuple D [j] → ActualTensor D hu}
        (hG : Function.HasFiniteSupport G) :
        Function.HasFiniteSupport (fun m : ℤ => G (m, ())) :=
      hG.comp_of_injective (fun _ _ h => congrArg Prod.fst h)
    have hleft : Function.HasFiniteSupport (fun m : ℤ =>
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
          (flatTerm D hu F [j] e x (m, ()))) :=
      (tupleFinite (flatTerm_finite D hu F [j] e x)).fun_comp
        (map_zero (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q))
    have hright : Function.HasFiniteSupport (fun m : ℤ =>
        flatTerm D hu F [j] e
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) (m, ())) :=
      tupleFinite (flatTerm_finite D hu F [j] e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x))
    change Function.HasFiniteSupport ((fun m : ℤ =>
        LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
          (flatTerm D hu F [j] e x (m, ()))) - (fun m : ℤ =>
        flatTerm D hu F [j] e
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) (m, ())))
    exact hleft.sub hright
  have finiteContraction : Function.HasFiniteSupport contraction := by
    apply (Set.finite_singleton (-q-1)).subset
    intro m hm
    change contraction m ≠ 0 at hm
    by_contra outside
    have hneq : q + m + 1 ≠ 0 := by
      intro hzero
      apply outside
      exact Set.mem_singleton_iff.mpr (by omega)
    exact hm (by simp [contraction, hneq])
  have finiteMain : Function.HasFiniteSupport main := by
    have hmain : main = term - contraction := by
      funext m
      exact eq_sub_iff_add_eq.mpr (term_eq m).symm
    rw [hmain]
    exact finiteTerm.sub finiteContraction
  have finiteSummand (n : ℕ) (hn : n ∈ S) :
      Function.HasFiniteSupport (fun m => summand m n) := by
    have tupleFinite {G : ModeTuple D [j] → ActualTensor D hu}
        (hG : Function.HasFiniteSupport G) :
        Function.HasFiniteSupport (fun m : ℤ => G (m, ())) :=
      hG.comp_of_injective (fun _ _ h => congrArg Prod.fst h)
    have hscaled : Function.HasFiniteSupport (fun m : ℤ =>
        coefficient n • flatTerm D hu (fields n) [j] (e + shift n) x (m, ())) :=
      (tupleFinite (flatTerm_finite D hu (fields n) [j] (e + shift n) x)).fun_comp
        (smul_zero (coefficient n))
    simpa [summand] using hscaled
  have main_eq : (∑ᶠ m : ℤ, main m) =
      ∑ n ∈ S, coefficient n •
        (singletonLinear D hu j (fields n)).coeff (e + shift n) x := by
    have exchange := finsum_finset_exchange S main summand finiteMain finiteSummand
      (fun m => by
        by_cases hm : m < 0
        · simp only [main, summand, flatTerm, flatCoefficient, if_pos hm,
            map_sum, map_smul, Module.End.mul_apply]
          apply Finset.sum_congr rfl
          intro n hn
          rw [show e + 2 * m + 2 * (j.2 : ℤ) + 3 + shift n =
              (e + shift n) + 2 * m + 2 * (j.2 : ℤ) + 3 by ring]
        · simp only [main, summand, flatTerm, flatCoefficient, if_neg hm,
            map_sum, map_smul, Module.End.mul_apply]
          apply Finset.sum_congr rfl
          intro n hn
          rw [show e + 2 * m + 2 * (j.2 : ℤ) + 3 + shift n =
              (e + shift n) + 2 * m + 2 * (j.2 : ℤ) + 3 by ring])
    rw [exchange]
    apply Finset.sum_congr rfl
    intro n hn
    change (∑ᶠ m : ℤ, coefficient n •
      flatTerm D hu (fields n) [j] (e + shift n) x (m, ())) = _
    rw [← smul_finsum' (coefficient n)
      (by
        have tupleFinite {G : ModeTuple D [j] → ActualTensor D hu}
            (hG : Function.HasFiniteSupport G) :
            Function.HasFiniteSupport (fun m : ℤ => G (m, ())) :=
          hG.comp_of_injective (fun _ _ h => congrArg Prod.fst h)
        exact tupleFinite (flatTerm_finite D hu (fields n) [j] (e + shift n) x))]
    exact congrArg (fun y => coefficient n • y)
      (singleton_coefficient_local D hu (fields n) j (e + shift n) x).symm
  have contraction_eq : (∑ᶠ m : ℤ, contraction m) =
      ((j.2 + 1 : ℂ) * Ring.choose (LatticeHalfFock.frequency q) (j.2 + 1) *
        (D.G i j.1 : ℂ)) •
        F.coeff (e - (2*q + 1) + 2*(j.2 : ℤ) + 2) x := by
    rw [finsum_eq_single _ (-q-1)]
    · dsimp [contraction]
      rw [if_pos (by omega)]
      have hscalar : jetScalar j.2 (-q - 1) * LatticeHalfFock.frequency q =
          (j.2 + 1 : ℂ) * Ring.choose (LatticeHalfFock.frequency q) (j.2 + 1) := by
        rw [mul_comm]
        exact jetScalar_contraction q j.2
      rw [hscalar]
      have hexp : e + 2 * (-q - 1) + 2 * (j.2 : ℤ) + 3 =
          e - (2*q + 1) + 2*(j.2 : ℤ) + 2 := by ring
      rw [hexp]
    · intro m hm
      simp [contraction, show q + m + 1 ≠ 0 by omega]
  rw [singleton_coefficient_local, singleton_coefficient_local]
  have tupleFinite {G : ModeTuple D [j] → ActualTensor D hu}
      (hG : Function.HasFiniteSupport G) :
      Function.HasFiniteSupport (fun m : ℤ => G (m, ())) :=
    hG.comp_of_injective (fun _ _ h => congrArg Prod.fst h)
  have finiteLeft := tupleFinite (flatTerm_finite D hu F [j] e x)
  have finiteRight := tupleFinite (flatTerm_finite D hu F [j] e
    (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x))
  have finiteLeftCurrent : Function.HasFiniteSupport (fun m : ℤ =>
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        (flatTerm D hu F [j] e x (m, ()))) :=
    finiteLeft.fun_comp
      (map_zero (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q))
  rw [map_finsum _ finiteLeft]
  change (∑ᶠ m : ℤ,
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        (flatTerm D hu F [j] e x (m, ()))) -
      ∑ᶠ m : ℤ, flatTerm D hu F [j] e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) (m, ()) = _
  rw [← finsum_sub_distrib finiteLeftCurrent finiteRight]
  change (∑ᶠ m : ℤ, term m) = _
  rw [finsum_congr term_eq, finsum_add_distrib finiteMain finiteContraction,
    main_eq, contraction_eq]

private theorem polynomialField_one (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) :
    polynomialField D hu charge 1 = chargedField D hu charge := by
  have basis := (MvPolynomial.basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun a => chargedWordField D hu charge (occurrences D a)) 0
  have emptyWord : occurrences D (0 : Index D →₀ ℕ) = [] := by
    simp [occurrences]
  change polynomialField D hu charge (MvPolynomial.monomial 0 1) =
    wordField D hu (chargedField D hu charge) (occurrences D 0) at basis
  rw [MvPolynomial.monomial_zero', MvPolynomial.C_1, emptyWord] at basis
  rw [basis]
  apply HVertexOperator.coeff_inj
  funext exponent
  apply LinearMap.ext
  intro vector
  rw [wordField_coefficient]
  change (∑ᶠ _ : Unit, (chargedField D hu charge).coeff exponent vector) = _
  exact finsum_unique _

private theorem polynomialField_C (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (scalar : ℂ) :
    polynomialField D hu charge (C scalar) = scalar • chargedField D hu charge := by
  rw [C_eq_smul_one, map_smul, polynomialField_one]

private theorem weightedPartial_X_mul_local (D : LatticeData) (i j : Fin D.rank)
    (a b : ℕ) (p : Oscillator D) :
    weightedPartial D i a (X (j,b) * p) =
      (if a = b then (D.G i j : ℂ) • p else 0) +
        X (j,b) * weightedPartial D i a p := by
  classical
  simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]
  simp_rw [pderiv_mul, smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hab : a = b
    · subst b
      simp [pderiv_X, Pi.single_apply, Prod.mk.injEq]
    · simp [pderiv_X, Pi.single_apply, Prod.mk.injEq, hab, Ne.symm hab]
  · simp [Finset.mul_sum, mul_smul_comm]

private def polynomialWardTerm (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (charge : Charge D) (p : Oscillator D) (q e : ℤ)
    (x : ActualTensor D hu) (n : ℕ) : ActualTensor D hu :=
  Ring.choose (LatticeHalfFock.frequency q) n •
    (polynomialField D hu charge
      (neutralPolynomialMode D i charge (n : ℤ) p)).coeff
        (e - (2*q + 1) + 2*(n : ℤ)) x

private theorem polynomialWardTerm_finite (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (charge : Charge D) (p : Oscillator D) (q e : ℤ)
    (x : ActualTensor D hu) :
    Function.HasFiniteSupport (polynomialWardTerm D hu i charge p q e x) := by
  apply (Finset.range (polynomialFrequencyBound D p + 1)).finite_toSet.subset
  intro n hn
  change polynomialWardTerm D hu i charge p q e x n ≠ 0 at hn
  by_contra outside
  have hzero : neutralPolynomialMode D i charge (n : ℤ) p = 0 := by
    apply neutralPolynomialMode_vanish D i charge p (n : ℤ)
    simp only [Finset.mem_coe, Finset.mem_range] at outside
    omega
  exact hn (by simp [polynomialWardTerm, hzero])

private theorem polynomial_current_ward
    (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (charge : Charge D) (p : Oscillator D) (q e : ℤ)
    (x : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        ((polynomialField D hu charge p).coeff e x) -
      (polynomialField D hu charge p).coeff e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) =
      ∑ᶠ n : ℕ, polynomialWardTerm D hu i charge p q e x n := by
  classical
  induction p using MvPolynomial.induction_on generalizing e x with
  | C scalar =>
      rw [polynomialField_C]
      rw [finsum_eq_single _ 0]
      · have hmode0 : neutralPolynomialMode D i charge 0 (C scalar) =
            (bilinear D (unitCharge D i) charge : ℂ) • C scalar := by
          simp [neutralPolynomialMode]
        have hterm0 : polynomialWardTerm D hu i charge (C scalar) q e x 0 =
            (bilinear D (unitCharge D i) charge : ℂ) •
              (scalar • (chargedField D hu charge).coeff (e - (2*q + 1)) x) := by
          simp [polynomialWardTerm, hmode0, polynomialField_C, chargedField,
            HVertexOperator.coeff_of_coeff, smul_eq_mul, sub_eq_add_neg,
            add_comm, add_left_comm, add_assoc]
        rw [hterm0]
        have h := charged_tensor_current_ward D hu i charge q e
        have hx := congrArg (fun T : Module.End ℂ (ActualTensor D hu) => T x) h
        have hcoeff (r : ℤ) :
            (chargedField D hu charge).coeff r = chargedCoefficient D hu charge r := by
          rw [chargedField, HVertexOperator.coeff_of_coeff]
        have hcoeffScalar (r : ℤ) :
            (scalar • HVertexOperator.coeff (chargedField D hu charge)) r =
              scalar • chargedCoefficient D hu charge r := by
          change scalar • (chargedField D hu charge).coeff r = _
          rw [hcoeff]
        simp only [hcoeffScalar, hcoeff, LinearMap.smul_apply, map_smul]
        have hscaled := congrArg (fun y => scalar • y) hx
        simp only [map_smul, LinearMap.smul_apply, Module.End.mul_apply,
          LinearMap.sub_apply] at hscaled ⊢
        change scalar • ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
          ((chargedCoefficient D hu charge e) x) -
          (chargedCoefficient D hu charge e)
            ((LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q) x)) = _ at hscaled
        rw [smul_sub] at hscaled
        rw [smul_comm scalar (bilinear D (unitCharge D i) charge : ℂ)] at hscaled
        exact hscaled
      · intro n hn
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hcast : ¬ (n : ℤ) < 0 := by omega
        have hne : (n : ℤ) ≠ 0 := by omega
        have hp (j : Fin D.rank) :
            pderiv (j, ((n : ℤ) - 1).toNat) (C scalar) = 0 := by
          apply pderiv_eq_zero_of_notMem_vars
          simp
        have hmode : neutralPolynomialMode D i charge (n : ℤ) (C scalar) = 0 := by
          rw [neutralPolynomialMode]
          simp only [hcast, if_false, hne]
          simp only [LinearMap.smul_apply, LinearMap.sum_apply]
          apply smul_eq_zero.mpr
          right
          apply Finset.sum_eq_zero
          intro j hj
          simp [hp]
        simp [polynomialWardTerm, hmode]
  | add first second firstProof secondProof =>
      simp only [map_add, Pi.add_apply, LinearMap.add_apply]
      rw [add_sub_add_comm, firstProof, secondProof,
        ← finsum_add_distrib
          (polynomialWardTerm_finite D hu i charge first q e x)
          (polynomialWardTerm_finite D hu i charge second q e x)]
      apply finsum_congr
      intro n
      simp [polynomialWardTerm, neutralPolynomialMode, map_add, smul_add]
  | mul_X polynomial index previous =>
      let R : ℕ := max (polynomialFrequencyBound D polynomial) (index.2 + 1)
      let S : Finset ℕ := Finset.range (R + 1)
      let coefficient : ℕ → ℂ := fun n => Ring.choose (LatticeHalfFock.frequency q) n
      let shift : ℕ → ℤ := fun n => -(2*q + 1) + 2*(n : ℤ)
      let fields : ℕ → NativeField D hu := fun n =>
        polynomialField D hu charge
          (neutralPolynomialMode D i charge (n : ℤ) polynomial)
      have hbound (z : ℤ) (v : ActualTensor D hu) :
          Function.support (polynomialWardTerm D hu i charge polynomial q z v) ⊆ S := by
        intro n hn
        by_contra hnot
        have hnnot : ¬ n < R + 1 := by
          intro hnlt
          apply hnot
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr hnlt)
        have hnR : (R : ℤ) < (n : ℤ) := by
          change ¬ n < R + 1 at hnnot
          omega
        have hpoly : (polynomialFrequencyBound D polynomial : ℤ) < (n : ℤ) := by
          have hR : polynomialFrequencyBound D polynomial ≤ R := by
            exact Nat.le_max_left _ _
          omega
        have hzero := neutralPolynomialMode_vanish D i charge polynomial
          (n : ℤ) hpoly
        have hfield : polynomialField D hu charge
              (neutralPolynomialMode D i charge (n : ℤ) polynomial) = 0 := by
          rw [hzero, map_zero]
        apply hn
        rw [polynomialWardTerm, hfield]
        simp
      have hcomm (z : ℤ) (v : ActualTensor D hu) :
          LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
              ((polynomialField D hu charge polynomial).coeff z v) -
            (polynomialField D hu charge polynomial).coeff z
              (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q v) =
          ∑ n ∈ S, coefficient n • (fields n).coeff (z + shift n) v := by
        have hp := previous z v
        rw [finsum_eq_sum_of_support_subset _ (hbound z v)] at hp
        rw [hp]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [polynomialWardTerm, coefficient, fields, shift]
        congr 2
        ring_nf
      have hsingle := singleton_current_ward_of_sum D hu i index
        (polynomialField D hu charge polynomial) S coefficient shift fields q e x hcomm
      rw [mul_comm polynomial (X index), polynomialField_X_mul]
      rw [hsingle]
      have hmode_zero :
          neutralPolynomialMode D i charge 0 (X index * polynomial) =
            (bilinear D (unitCharge D i) charge : ℂ) •
              (X index * polynomial) := by
        simp [neutralPolynomialMode]
      have hmode_succ (a : ℕ) :
          neutralPolynomialMode D i charge ((a : ℤ) + 1)
              (X index * polynomial) =
            (a + 1 : ℂ) •
              ((if a = index.2 then (D.G i index.1 : ℂ) • polynomial else 0) +
                X index * weightedPartial D i a polynomial) := by
        rw [neutralPolynomialMode_positive]
        simp only [LinearMap.smul_apply]
        rw [weightedPartial_X_mul_local]
      have hmode_zero_poly :
          neutralPolynomialMode D i charge 0 polynomial =
            (bilinear D (unitCharge D i) charge : ℂ) • polynomial := by
        simp [neutralPolynomialMode]
      have hmode_succ_poly (a : ℕ) :
          neutralPolynomialMode D i charge ((a : ℤ) + 1) polynomial =
            (a + 1 : ℂ) • weightedPartial D i a polynomial := by
        simpa only [LinearMap.smul_apply] using congrArg (fun f => f polynomial)
          (neutralPolynomialMode_positive D i charge a)
      have htarget_bound :
          Function.support (polynomialWardTerm D hu i charge (X index * polynomial) q e x) ⊆ S := by
        intro n hn
        by_contra hnot
        have hnnot : ¬ n < R + 1 := by
          intro hnlt
          apply hnot
          exact Finset.mem_coe.mpr (Finset.mem_range.mpr hnlt)
        have hnR : (R : ℤ) < (n : ℤ) := by
          change ¬ n < R + 1 at hnnot
          omega
        have hmodezero :
            neutralPolynomialMode D i charge (n : ℤ) (X index * polynomial) = 0 := by
          cases n with
          | zero => omega
          | succ a =>
            rw [show (Nat.succ a : ℤ) = (a : ℤ) + 1 by simp,
              hmode_succ]
            have hpoly : (polynomialFrequencyBound D polynomial : ℤ) < (Nat.succ a : ℤ) := by
              have hR : polynomialFrequencyBound D polynomial ≤ R := Nat.le_max_left _ _
              omega
            have hvan := neutralPolynomialMode_vanish D i charge polynomial
              (Nat.succ a : ℤ) hpoly
            rw [show (Nat.succ a : ℤ) = (a : ℤ) + 1 by simp,
              neutralPolynomialMode_positive] at hvan
            have hneq : a ≠ index.2 := by
              have hi : index.2 + 1 ≤ R := Nat.le_max_right _ _
              omega
            have hscalar : (a + 1 : ℂ) ≠ 0 := by
              exact_mod_cast Nat.succ_ne_zero a
            have hwp : weightedPartial D i a polynomial = 0 :=
              (smul_eq_zero.mp hvan).resolve_left hscalar
            simp [hneq, hwp]
        have hfield : polynomialField D hu charge
              (neutralPolynomialMode D i charge (n : ℤ) (X index * polynomial)) = 0 := by
          rw [hmodezero, map_zero]
        apply hn
        rw [polynomialWardTerm, hfield]
        simp
      rw [finsum_eq_sum_of_support_subset _ htarget_bound]
      have hterm (n : ℕ) :
          polynomialWardTerm D hu i charge (X index * polynomial) q e x n =
            coefficient n • (singletonLinear D hu index (fields n)).coeff
                (e + shift n) x +
              (if n = index.2 + 1 then
                ((index.2 + 1 : ℂ) * Ring.choose (LatticeHalfFock.frequency q)
                    (index.2 + 1) * (D.G i index.1 : ℂ)) •
                  (polynomialField D hu charge polynomial).coeff
                    (e - (2*q + 1) + 2*(index.2 : ℤ) + 2) x
               else 0) := by
        cases n with
        | zero =>
            simp only [polynomialWardTerm, coefficient, fields, shift]
            simp only [Nat.cast_zero, Int.cast_zero]
            simp [hmode_zero, hmode_zero_poly, polynomialField_X_mul, map_smul,
              LinearMap.smul_apply, smul_assoc, show (0 : ℕ) ≠ index.2 + 1 by omega]
            ring_nf
        | succ a =>
            simp only [polynomialWardTerm, coefficient, fields, shift]
            rw [show (Nat.succ a : ℤ) = (a : ℤ) + 1 by simp,
              hmode_succ, hmode_succ_poly]
            simp only [map_smul, map_add, LinearMap.smul_apply]
            rw [polynomialField_X_mul]
            by_cases ha : a = index.2
            · subst a
              simp [smul_add, smul_assoc, smul_smul, add_comm, add_left_comm,
                add_assoc]
              congr 2 <;> ring_nf
            · simp [ha, smul_add, smul_assoc, smul_smul, add_comm, add_left_comm,
                add_assoc]
              congr 2 <;> ring_nf
      have hmem : index.2 + 1 ∈ S := by
        simp only [S, Finset.mem_range]
        dsimp [R]
        omega
      symm
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hmem]


private theorem Corr_partial_apply (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : Oscillator D) (shift : ℕ) :
    pderiv index (Corr D charge polynomial shift) =
      Corr D charge (pderiv index polynomial) shift := by
  exact Corr_partial D charge index polynomial shift

private theorem Corr_weightedPartial_apply (D : LatticeData) (charge : Charge D)
    (i : Fin D.rank) (a : ℕ) (polynomial : Oscillator D) (shift : ℕ) :
    weightedPartial D i a (Corr D charge polynomial shift) =
      Corr D charge (weightedPartial D i a polynomial) shift := by
  classical
  simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]
  change _ = (Corr D charge (∑ j : Fin D.rank,
    (D.G i j : ℂ) • pderiv (j, a) polynomial)) shift
  rw [map_sum]
  simp only [map_smul]
  rw [Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro j hj
  rw [Corr_partial_apply]
  rfl

private theorem Corr_neutralPolynomialMode_nat (D : LatticeData) (charge : Charge D)
    (i : Fin D.rank) (polynomial : Oscillator D) (n : ℕ) (shift : ℕ) :
    neutralPolynomialMode D i charge (n : ℤ) (Corr D charge polynomial shift) =
      Corr D charge (neutralPolynomialMode D i charge (n : ℤ) polynomial) shift := by
  cases n with
  | zero =>
      simp [neutralPolynomialMode]
  | succ a =>
      rw [show (Nat.succ a : ℤ) = (a : ℤ) + 1 by simp,
        neutralPolynomialMode_positive]
      simp only [LinearMap.smul_apply]
      rw [Corr_weightedPartial_apply]
      change _ = (Corr D charge ((a + 1 : ℂ) • weightedPartial D i a polynomial)) shift
      rw [map_smul]
      rfl

private theorem correctedPolynomial_current_ward
    (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (charge : Charge D) (polynomial : Oscillator D) (q e : ℤ)
    (x : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        ((correctedPolynomial D hu charge polynomial).coeff e x) -
      (correctedPolynomial D hu charge polynomial).coeff e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) =
      ∑ᶠ n : ℕ,
        Ring.choose (LatticeHalfFock.frequency q) n •
          (correctedPolynomial D hu charge
            (neutralPolynomialMode D i charge (n : ℤ) polynomial)).coeff
              (e - (2*q + 1) + 2*(n : ℤ)) x := by
  classical
  have hshift (s : ℕ) :
      LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
          ((shiftField D hu s
            (polynomialField D hu charge (Corr D charge polynomial s))).coeff e x) -
        (shiftField D hu s
            (polynomialField D hu charge (Corr D charge polynomial s))).coeff e
          (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) =
        ∑ᶠ n : ℕ,
          Ring.choose (LatticeHalfFock.frequency q) n •
            (shiftField D hu s
              (polynomialField D hu charge
                (neutralPolynomialMode D i charge (n : ℤ)
                  (Corr D charge polynomial s)))).coeff
                (e - (2*q + 1) + 2*(n : ℤ)) x := by
    have hp := polynomial_current_ward D hu i charge
      (Corr D charge polynomial s) q (e + 2*(s : ℤ)) x
    simp only [shiftField_coefficient_public]
    simpa [shiftField_coefficient_public, polynomialWardTerm, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hp
  simp only [correctedPolynomial, correctedSum, LinearMap.comp_apply,
    Finsupp.lsum_apply, Finsupp.sum, Finsupp.sum_apply]
  let S : Finset ℕ := (Corr D charge polynomial).support
  have hsupport (n : ℕ) :
      (Corr D charge (neutralPolynomialMode D i charge (n : ℤ) polynomial)).support ⊆ S := by
    intro s hs
    by_contra hnot
    have hzero : Corr D charge polynomial s = 0 := by
      by_contra hz
      apply hnot
      exact Finsupp.mem_support_iff.mpr hz
    have heq := Corr_neutralPolynomialMode_nat D charge i polynomial n s
    rw [hzero] at heq
    have hcorrzero : Corr D charge
          (neutralPolynomialMode D i charge (n : ℤ) polynomial) s = 0 := by
      simpa using heq.symm
    exact (Finsupp.mem_support_iff.mp hs) hcorrzero
  have hcoeff (v : ActualTensor D hu) :
      (HVertexOperator.coeff
          (∑ s ∈ S, (shiftField D hu s)
            ((polynomialField D hu charge) ((Corr D charge polynomial) s))) e) v =
        ∑ s ∈ S,
          ((shiftField D hu s)
            ((polynomialField D hu charge) ((Corr D charge polynomial) s))).coeff e v := by
    rw [map_sum]
    simp only [Finset.sum_apply]
    simp only [LinearMap.coe_sum, Finset.sum_apply]
  rw [hcoeff x, hcoeff]
  rw [map_sum]
  rw [← Finset.sum_sub_distrib]
  let g : ℕ → ℕ → ActualTensor D hu := fun n s =>
    Ring.choose (LatticeHalfFock.frequency q) n •
      (shiftField D hu s
        (polynomialField D hu
          charge
          (neutralPolynomialMode D i charge (n : ℤ)
            (Corr D charge polynomial s)))).coeff
        (e - (2*q + 1) + 2*(n : ℤ)) x
  have hsum :
      (∑ s ∈ S, (
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q)
            ((shiftField D hu s
              (polynomialField D hu charge ((Corr D charge polynomial) s))).coeff e x) -
          (shiftField D hu s
            (polynomialField D hu charge ((Corr D charge polynomial) s))).coeff e
            (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x))) =
        ∑ s ∈ S, ∑ᶠ n : ℕ, g n s := by
    apply Finset.sum_congr rfl
    intro s hs
    simpa [g] using hshift s
  rw [hsum]
  have hterm_finite (s : ℕ) :
      Function.HasFiniteSupport (fun n => g n s) := by
    have heq : (fun n => g n s) =
        polynomialWardTerm D hu i charge (Corr D charge polynomial s)
          q (e + 2*(s : ℤ)) x := by
      funext n
      dsimp only [g, polynomialWardTerm]
      rw [shiftField_coefficient_public,
        show e - (2*q + 1) + 2*(n : ℤ) + 2*(s : ℤ) =
          (e + 2*(s : ℤ)) - (2*q + 1) + 2*(n : ℤ) by ring]
    rw [heq]
    exact polynomialWardTerm_finite D hu i charge (Corr D charge polynomial s)
      q (e + 2*(s : ℤ)) x
  let f : ℕ → ActualTensor D hu := fun n => ∑ s ∈ S, g n s
  have hfinite_f : Function.HasFiniteSupport f :=
    Function.HasFiniteSupport.sum hterm_finite S
  have hcoeff_neutral (n : ℕ) (r : ℤ) (v : ActualTensor D hu) :
      (HVertexOperator.coeff
          (∑ s ∈ (Corr D charge
            (neutralPolynomialMode D i charge (n : ℤ) polynomial)).support,
            shiftField D hu s
              (polynomialField D hu charge
                (Corr D charge
                  (neutralPolynomialMode D i charge (n : ℤ) polynomial) s))) r) v =
        ∑ s ∈ (Corr D charge
            (neutralPolynomialMode D i charge (n : ℤ) polynomial)).support,
          (shiftField D hu s
            (polynomialField D hu charge
              (Corr D charge
                (neutralPolynomialMode D i charge (n : ℤ) polynomial) s))).coeff r v := by
    rw [map_sum]
    simp only [Finset.sum_apply]
    simp only [LinearMap.coe_sum, Finset.sum_apply]
  have hsum_neutral (n : ℕ) :
      (∑ s ∈ (Corr D charge
        (neutralPolynomialMode D i charge (n : ℤ) polynomial)).support, g n s) = f n := by
    dsimp [f]
    apply Finset.sum_subset (hsupport n)
    intro s hs hnot
    have hzero :
        Corr D charge (neutralPolynomialMode D i charge (n : ℤ) polynomial) s = 0 := by
      by_contra hz
      apply hnot
      exact Finsupp.mem_support_iff.mpr hz
    have hzeroMode :
        neutralPolynomialMode D i charge (n : ℤ)
            (Corr D charge polynomial s) = 0 := by
      have heq := Corr_neutralPolynomialMode_nat D charge i polynomial n s
      rw [hzero] at heq
      simpa using heq
    simp [g, hzeroMode]
  have hright :
      (∑ᶠ n : ℕ,
        Ring.choose (LatticeHalfFock.frequency q) n •
          (HVertexOperator.coeff
            (∑ s ∈ (Corr D charge
              (neutralPolynomialMode D i charge (n : ℤ) polynomial)).support,
              shiftField D hu s
                (polynomialField D hu charge
                  (Corr D charge
                    (neutralPolynomialMode D i charge (n : ℤ) polynomial) s)))
            (e - (2*q + 1) + 2*(n : ℤ))) x) =
      ∑ᶠ n : ℕ, f n := by
    apply finsum_congr
    intro n
    rw [hcoeff_neutral]
    have hterm_neutral (s : ℕ) :
        Ring.choose (LatticeHalfFock.frequency q) n •
            (shiftField D hu s
              (polynomialField D hu charge
                (Corr D charge
                  (neutralPolynomialMode D i charge (n : ℤ) polynomial) s))).coeff
                (e - (2*q + 1) + 2*(n : ℤ)) x =
          g n s := by
      dsimp [g]
      rw [Corr_neutralPolynomialMode_nat D charge i polynomial n s]
    rw [Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun s hs => hterm_neutral s)]
    exact hsum_neutral n
  rw [hright]
  have hexchange := finsum_finset_exchange_nat S f g hfinite_f
    (fun s _ => hterm_finite s) (fun n => rfl)
  rw [← hexchange]

private theorem correctedField_neutralMode_sum
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (b : Carrier D) (n : ℕ) :
    correctedField D hu (neutralMode D i (n : ℤ) b) =
      ∑ β ∈ b.support,
        correctedPolynomial D hu β
          (neutralPolynomialMode D i β (n : ℤ) (b β)) := by
  classical
  rw [neutralMode, Finsupp.lsum_apply]
  change correctedField D hu
      (∑ β ∈ b.support,
        Finsupp.single β
          (neutralPolynomialMode D i β (n : ℤ) (b β))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  simp [correctedField]

theorem correctedField_current_ward
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (b : Carrier D) (q e : ℤ) (x : ActualTensor D hu) :
    LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q
        ((correctedField D hu b).coeff e x) -
      (correctedField D hu b).coeff e
        (LatticeHalfFock.tensorCurrent D (ActualGround D hu) i q x) =
      ∑ n ∈ Finset.range (vectorFrequencyBound D b + 1),
        Ring.choose (LatticeHalfFock.frequency q) n •
          (correctedField D hu (neutralMode D i (n : ℤ) b)).coeff
            (e - (2*q + 1) + 2*(n : ℤ)) x := by
  classical
  have hfield_coeff (v : ActualTensor D hu) :
      (correctedField D hu b).coeff e v =
        ∑ β ∈ b.support,
          (correctedPolynomial D hu β (b β)).coeff e v := by
    rw [correctedField, Finsupp.lsum_apply]
    simp only [Finsupp.sum]
    rw [map_sum]
    simp only [LinearMap.coe_sum, Finset.sum_apply]
  rw [hfield_coeff x, hfield_coeff]
  rw [map_sum]
  rw [← Finset.sum_sub_distrib]
  let g : ℕ → Charge D → ActualTensor D hu := fun n β =>
    Ring.choose (LatticeHalfFock.frequency q) n •
      (correctedPolynomial D hu β
        (neutralPolynomialMode D i β (n : ℤ) (b β))).coeff
          (e - (2*q + 1) + 2*(n : ℤ)) x
  simp_rw [correctedPolynomial_current_ward]
  have hterm_finite (β : Charge D) (hβ : β ∈ b.support) :
      Function.HasFiniteSupport (fun n => g n β) := by
    apply (Finset.range (polynomialFrequencyBound D (b β) + 1)).finite_toSet.subset
    intro n hn
    by_contra outside
    have hnnot : ¬ n < polynomialFrequencyBound D (b β) + 1 := by
      intro hnlt
      apply outside
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hnlt)
    have hbound : (polynomialFrequencyBound D (b β) : ℤ) < (n : ℤ) := by
      omega
    have hmode := neutralPolynomialMode_vanish D i β (b β) (n : ℤ) hbound
    apply hn
    simp [g, hmode]
  let f : ℕ → ActualTensor D hu := fun n =>
    Ring.choose (LatticeHalfFock.frequency q) n •
      (correctedField D hu (neutralMode D i (n : ℤ) b)).coeff
        (e - (2*q + 1) + 2*(n : ℤ)) x
  have hf_support :
      Function.support f ⊆ (Finset.range (vectorFrequencyBound D b + 1) : Set ℕ) := by
    intro n hn
    by_contra outside
    have hnnot : ¬ n < vectorFrequencyBound D b + 1 := by
      intro hnlt
      apply outside
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hnlt)
    have hbound : (vectorFrequencyBound D b : ℤ) < (n : ℤ) := by
      omega
    have hmode := neutralMode_vanish D i b (n : ℤ) hbound
    apply hn
    simp [f, hmode]
  have hfinite_f : Function.HasFiniteSupport f :=
    (Finset.range (vectorFrequencyBound D b + 1)).finite_toSet.subset hf_support
  have hneutral_coeff (n : ℕ) (r : ℤ) :
      (correctedField D hu (neutralMode D i (n : ℤ) b)).coeff r x =
        ∑ β ∈ b.support,
          (correctedPolynomial D hu β
            (neutralPolynomialMode D i β (n : ℤ) (b β))).coeff r x := by
    rw [correctedField_neutralMode_sum]
    rw [map_sum]
    simp only [LinearMap.coe_sum, Finset.sum_apply]
  have hdecomp (n : ℕ) : f n = ∑ β ∈ b.support, g n β := by
    dsimp [f, g]
    rw [hneutral_coeff]
    rw [Finset.smul_sum]
  have hexchange := finsum_finset_exchange_nat b.support f g hfinite_f
    (fun β hβ => hterm_finite β hβ) hdecomp
  rw [← hexchange]
  rw [finsum_eq_sum_of_support_subset _ hf_support]

end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
