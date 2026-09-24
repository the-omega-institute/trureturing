/- GID: D5/S3/Combinatorics/Interpolation/ColoredTransversalNewtonSpanning
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/ColoredTransversalNewtonSpanning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Filtered Newton products span evaluations on finite disjoint colored blocks. -/

import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import Mathlib.Combinatorics.Nullstellensatz

/-!
This module supplies the deletion-closed interpolation statement needed for
colored transversals.  Blocks may have unequal sizes, including singletons;
their order is combinatorial and is not required to agree with the order on
the rational values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.ColoredTransversalNewtonSpanning

open scoped BigOperators
open MvPolynomial
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

/-- Nonempty ordered scalar blocks whose values are globally disjoint. -/
structure OrderedDisjointBlocks (n : Nat) where
  excess : Fin n -> Nat
  value : (j : Fin n) -> Fin (excess j + 1) -> Rat
  value_injective :
    Function.Injective (fun z : Sigma fun j => Fin (excess j + 1) => value z.1 z.2)

/-- A choice of one position in every colored block. -/
abbrev Transversal {n : Nat} (B : OrderedDisjointBlocks n) :=
  (j : Fin n) -> Fin (B.excess j + 1)

/-- The sum of the chosen positions in the ordered blocks. -/
def newtonWeight {n : Nat} {B : OrderedDisjointBlocks n}
    (alpha : Transversal B) : Nat :=
  Finset.univ.sum fun j => (alpha j).val

/-- Elementary-symmetric coefficient coordinates of the selected roots. -/
def coefficientPoint {n : Nat} (B : OrderedDisjointBlocks n)
    (alpha : Transversal B) : Fin n -> Rat := fun k =>
  (Finset.univ.val.map fun j => B.value j (alpha j)).esymm (k.val + 1)

/-- Evaluation at `t` of the universal monic polynomial in coefficient coordinates. -/
def characteristicEval {n : Nat} (t : Rat) : MvPolynomial (Fin n) Rat :=
  C (t ^ n) + Finset.univ.sum fun k =>
    C (((-1 : Rat) ^ (k.val + 1)) * t ^ (n - (k.val + 1))) * X k

/-- The colored Newton product indexed by a transversal. -/
def newtonPolynomial {n : Nat} (B : OrderedDisjointBlocks n)
    (alpha : Transversal B) : MvPolynomial (Fin n) Rat :=
  Finset.univ.prod fun j =>
    (Finset.Iio (alpha j)).prod fun a => characteristicEval (B.value j a)

/-- Filtered colored Newton products span every filtered polynomial evaluation
on arbitrary finite nonempty ordered globally disjoint rational blocks. -/
theorem colored_transversal_newton_spans
    {n : Nat} (hn : 0 < n) (B : OrderedDisjointBlocks n) (q : Nat) :
    (forall alpha : Transversal B,
      (newtonPolynomial B alpha).totalDegree <= newtonWeight alpha) /\
    forall Q : MvPolynomial (Fin n) Rat, Q.totalDegree <= q ->
      Exists fun c : {alpha : Transversal B // newtonWeight alpha <= q} -> Rat =>
        forall beta : Transversal B,
          MvPolynomial.eval (coefficientPoint B beta) Q =
            Finset.univ.sum fun alpha =>
              c alpha * MvPolynomial.eval (coefficientPoint B beta)
                (newtonPolynomial B alpha.1) := by
  classical
  have hCharacteristicDegree (t : Rat) :
      (characteristicEval (n := n) t).totalDegree <= 1 := by
    unfold characteristicEval
    apply (totalDegree_add _ _).trans
    apply max_le
    · calc
        (C (t ^ n) : MvPolynomial (Fin n) Rat).totalDegree = 0 := totalDegree_C _
        _ <= 1 := by omega
    · apply totalDegree_finsetSum_le
      intro k _
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, totalDegree_X]
  constructor
  · intro alpha
    unfold newtonPolynomial newtonWeight
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro j _
    apply (totalDegree_finsetProd _ _).trans
    calc
      (∑ a ∈ Finset.Iio (alpha j),
          (characteristicEval (B.value j a)).totalDegree) <=
          ∑ _a ∈ Finset.Iio (alpha j), 1 := by
            apply Finset.sum_le_sum
            intro a _
            exact hCharacteristicDegree _
      _ = (alpha j).val := by simp
  · have hCharacteristic (A : OrderedDisjointBlocks n) (beta : Transversal A) (t : Rat) :
        MvPolynomial.eval (coefficientPoint A beta) (characteristicEval t) =
          Finset.univ.prod fun j => t - A.value j (beta j) := by
      let roots : Multiset Rat := Finset.univ.val.map fun j => A.value j (beta j)
      have hv := Multiset.prod_X_sub_X_eq_sum_esymm roots
      have hev := congrArg (Polynomial.eval t) hv
      have hcard : roots.card = n := by simp [roots]
      rw [hcard] at hev
      rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at hev
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_sub, Multiset.map_map, Function.comp_apply] at hev
      simpa [characteristicEval, roots, coefficientPoint, MvPolynomial.aeval_def,
        MvPolynomial.aeval_esymm_eq_multiset_esymm, ← Fin.sum_univ_eq_sum_range,
        Fin.sum_univ_succ, Fin.prod_ofFn, Multiset.esymm, mul_comm, mul_left_comm,
        mul_assoc] using hev.symm
    let Represents (A : OrderedDisjointBlocks n) (r : Nat)
        (P : MvPolynomial (Fin n) Rat) : Prop :=
      Exists fun c : Transversal A -> Rat =>
        (forall alpha, r < newtonWeight alpha -> c alpha = 0) /\
        forall beta : Transversal A,
          MvPolynomial.eval (coefficientPoint A beta) P =
            Finset.univ.sum fun alpha =>
              c alpha * MvPolynomial.eval (coefficientPoint A beta)
                (newtonPolynomial A alpha)
    have hSpan (M : Nat) : forall A : OrderedDisjointBlocks n,
        Finset.univ.sum A.excess = M -> forall r (P : MvPolynomial (Fin n) Rat),
          P.totalDegree <= r -> Represents A r P := by
      induction M using Nat.strong_induction_on with
      | h M ih =>
          intro A hA r P hP
          by_cases hzero : M = 0
          · have hexcess (j : Fin n) : A.excess j = 0 := by
              have hj := Finset.single_le_sum (f := A.excess)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
              rw [hA, hzero] at hj
              omega
            let alpha0 : Transversal A := fun j => ⟨0, by simp [hexcess]⟩
            have hsub : Subsingleton (Transversal A) := by
              constructor
              intro alpha beta
              funext j
              apply Fin.ext
              have ha : (alpha j).val < 1 := by simpa [hexcess] using (alpha j).isLt
              have hb : (beta j).val < 1 := by simpa [hexcess] using (beta j).isLt
              omega
            have huniv : (Finset.univ : Finset (Transversal A)) = {alpha0} := by
              ext alpha
              simp [Subsingleton.elim alpha alpha0]
            refine ⟨fun _ => MvPolynomial.eval (coefficientPoint A alpha0) P, ?_, ?_⟩
            · intro alpha halpha
              exfalso
              have hw : newtonWeight alpha = 0 := by
                unfold newtonWeight
                apply Finset.sum_eq_zero
                intro j _
                have hj : (alpha j).val < 1 := by simpa [hexcess] using (alpha j).isLt
                omega
              omega
            · intro beta
              have hbeta : beta = alpha0 := Subsingleton.elim _ _
              rw [hbeta, huniv]
              have hiio (j : Fin n) : Finset.Iio (alpha0 j) = ∅ := by
                ext a
                simp [alpha0]
              simp [newtonPolynomial, hiio]
          · have hMpos : 0 < M := Nat.pos_of_ne_zero hzero
            cases r with
            | zero =>
                have hPzero : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hP
                have hPC : P = C (P.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hPzero
                rw [hPC]
                let a := P.coeff 0
                let alpha0 : Transversal A := fun k => 0
                refine ⟨fun alpha => if alpha = alpha0 then a else 0, ?_, ?_⟩
                · intro alpha halpha
                  have hne : alpha ≠ alpha0 := by
                    intro heq
                    subst alpha
                    simpa [newtonWeight, alpha0] using halpha
                  simp [hne]
                · intro beta
                  have hiio (k : Fin n) : Finset.Iio (alpha0 k) = ∅ := by
                    ext x
                    simp [alpha0]
                  have hnewton : newtonPolynomial A alpha0 = 1 := by
                    simp [newtonPolynomial, hiio]
                  rw [Finset.sum_eq_single alpha0]
                  · simp [a, hnewton]
                  · intro alpha _ hne
                    simp [hne]
                  · simp
            | succ r' =>
                let alpha0 : Transversal A := fun k => 0
                let y0 := coefficientPoint A alpha0
                let base : Fin n -> Rat := fun k => A.value k 0
                have hbase : Function.Injective base := by
                  intro k l hkl
                  have hs : (⟨k, (0 : Fin (A.excess k + 1))⟩ :
                      Sigma fun i => Fin (A.excess i + 1)) =
                      ⟨l, (0 : Fin (A.excess l + 1))⟩ := by
                    apply A.value_injective
                    exact hkl
                  exact congrArg Sigma.fst hs
                let V : Matrix (Fin n) (Fin n) Rat := Matrix.vandermonde base
                have hV : Matrix.det V ≠ 0 := by
                  exact vandermonde_det_ne_zero_of_injective hbase
                let centered := P - C (MvPolynomial.eval y0 P)
                let singleton : Fin n -> Finset Rat := fun k => {y0 k}
                have hvanish (x : Fin n -> Rat)
                    (hx : ∀ k, x k ∈ singleton k) : MvPolynomial.eval x centered = 0 := by
                  have hxy : x = y0 := by
                    funext k
                    simpa [singleton] using hx k
                  subst x
                  simp [centered]
                obtain ⟨quotient, hProductDegree, hCentered⟩ :=
                  MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination
                    singleton (by intro k; simp [singleton]) centered hvanish
                let sign : Fin n -> Rat := fun k => (-1 : Rat) ^ (k.val + 1)
                let delta : Fin n -> MvPolynomial (Fin n) Rat := fun k =>
                  C (sign (Fin.rev k)) * (X (Fin.rev k) - C (y0 (Fin.rev k)))
                let g : Fin n -> MvPolynomial (Fin n) Rat := fun k =>
                  characteristicEval (base k)
                have hG (k : Fin n) :
                    g k = ∑ l, C (V k l) * delta l := by
                  have hzEval := hCharacteristic A alpha0 (base k)
                  have hzEvalZero : MvPolynomial.eval (coefficientPoint A alpha0)
                      (characteristicEval (base k)) = 0 := by
                    rw [hzEval]
                    apply Finset.prod_eq_zero (Finset.mem_univ k)
                    simp [base, alpha0]
                  have hz : base k ^ n +
                      ∑ i, sign i * base k ^ (n - (i.val + 1)) * y0 i = 0 := by
                    simpa [characteristicEval, sign, y0] using hzEvalZero
                  have hreindex :
                      (∑ l, C (V k l) * delta l) =
                        ∑ i, C (sign i * base k ^ (n - (i.val + 1))) *
                          (X i - C (y0 i)) := by
                    rw [← Equiv.sum_comp Fin.revPerm]
                    apply Finset.sum_congr rfl
                    intro i _
                    simp only [V, delta, Matrix.vandermonde_apply, Fin.revPerm_apply]
                    rw [Fin.rev_rev]
                    simp only [sign, Fin.val_rev, map_mul]
                    ring
                  rw [hreindex]
                  unfold g characteristicEval
                  simp_rw [mul_sub]
                  rw [Finset.sum_sub_distrib]
                  have hconst : (C (base k ^ n) : MvPolynomial (Fin n) Rat) =
                      -(∑ i, (C (sign i * base k ^ (n - (i.val + 1))) :
                        MvPolynomial (Fin n) Rat) * C (y0 i)) := by
                    simp_rw [← map_mul]
                    rw [← map_sum, ← map_neg]
                    apply congrArg C
                    exact eq_neg_of_add_eq_zero_left hz
                  rw [hconst]
                  ring
                have hInv : V⁻¹ * V = (1 : Matrix (Fin n) (Fin n) Rat) :=
                  Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hV)
                have hDelta (l : Fin n) :
                    delta l = ∑ k, C (V⁻¹ l k) * g k := by
                  symm
                  calc
                    (∑ k, C (V⁻¹ l k) * g k) =
                        ∑ k, ∑ m, C (V⁻¹ l k * V k m) * delta m := by
                          apply Finset.sum_congr rfl
                          intro k _
                          rw [hG, Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro m _
                          simp [mul_assoc]
                    _ = ∑ m, ∑ k, C (V⁻¹ l k * V k m) * delta m :=
                      Finset.sum_comm
                    _ = ∑ m, C ((V⁻¹ * V) l m) * delta m := by
                          apply Finset.sum_congr rfl
                          intro m _
                          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
                    _ = delta l := by
                          rw [hInv]
                          simp [Matrix.one_apply]
                have hSignSq (i : Fin n) : sign i * sign i = 1 := by
                  simp [sign, ← mul_pow]
                have hCoordinate (i : Fin n) :
                    X i - C (y0 i) =
                      ∑ k, C (sign i * V⁻¹ (Fin.rev i) k) * g k := by
                  have hd := hDelta (Fin.rev i)
                  calc
                    X i - C (y0 i) = C (sign i * sign i) * (X i - C (y0 i)) := by
                      rw [hSignSq]
                      simp
                    _ = C (sign i) * delta (Fin.rev i) := by
                      simp [delta, mul_assoc]
                    _ = C (sign i) * (∑ k, C (V⁻¹ (Fin.rev i) k) * g k) := by rw [hd]
                    _ = ∑ k, C (sign i * V⁻¹ (Fin.rev i) k) * g k := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro k _
                      simp [mul_assoc]
                have hFactorDegree (i : Fin n) :
                    (X i - C (y0 i) : MvPolynomial (Fin n) Rat).totalDegree = 1 := by
                  rw [sub_eq_add_neg,
                    totalDegree_add_eq_left_of_totalDegree_lt (by simp :
                      (-C (y0 i) : MvPolynomial (Fin n) Rat).totalDegree <
                        (X i : MvPolynomial (Fin n) Rat).totalDegree)]
                  exact totalDegree_X i
                have hQuotientDegree (i : Fin n) : (quotient i).totalDegree <= r' := by
                  by_cases hqi : quotient i = 0
                  · simp [hqi]
                  · have hfactor :
                        (X i - C (y0 i) : MvPolynomial (Fin n) Rat) ≠ 0 := by
                      intro hz
                      have hd := hFactorDegree i
                      rw [hz, totalDegree_zero] at hd
                      omega
                    have hd := hProductDegree i
                    simp only [singleton, Finset.prod_singleton] at hd
                    rw [totalDegree_mul_of_isDomain hfactor hqi, hFactorDegree] at hd
                    have hc : centered.totalDegree <= P.totalDegree := by
                      exact totalDegree_sub_C_le P _
                    omega
                let Qpart : Fin n -> MvPolynomial (Fin n) Rat := fun k =>
                  ∑ i, C (sign i * V⁻¹ (Fin.rev i) k) * quotient i
                have hQpartDegree (k : Fin n) : (Qpart k).totalDegree <= r' := by
                  unfold Qpart
                  apply totalDegree_finsetSum_le
                  intro i _
                  apply (totalDegree_mul _ _).trans
                  rw [totalDegree_C]
                  simpa using hQuotientDegree i
                have hCenteredSum :
                    centered = ∑ i, (X i - C (y0 i)) * quotient i := by
                  rw [hCentered, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
                  · apply Finset.sum_congr rfl
                    intro i _
                    simp [singleton, smul_eq_mul, mul_comm]
                  · intro i
                    simp
                have hCenteredG : centered = ∑ k, g k * Qpart k := by
                  rw [hCenteredSum]
                  simp_rw [hCoordinate, Finset.sum_mul]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro k _
                  unfold Qpart
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
                have hPDecomp :
                    P = C (MvPolynomial.eval y0 P) + ∑ k, g k * Qpart k := by
                  rw [← hCenteredG]
                  simp [centered]
                have hTerm (k : Fin n) : Represents A (r' + 1) (g k * Qpart k) := by
                  by_cases hkzero : A.excess k = 0
                  · refine ⟨0, by simp, ?_⟩
                    intro beta
                    have hbeta : beta k = 0 := by
                      apply Fin.ext
                      have hb := (beta k).isLt
                      simp [hkzero] at hb
                      omega
                    have hgzero : MvPolynomial.eval (coefficientPoint A beta) (g k) = 0 := by
                      unfold g base
                      rw [hCharacteristic]
                      apply Finset.prod_eq_zero (Finset.mem_univ k)
                      simp [hbeta]
                    simp [map_mul, hgzero]
                  · obtain ⟨d, hkd⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
                    let excess' : Fin n -> Nat := Function.update A.excess k d
                    let embed (l : Fin n) : Fin (excess' l + 1) ->
                        Fin (A.excess l + 1) := fun a => if hl : l = k then
                      ⟨a.val + 1, by
                        subst l
                        have ha := a.isLt
                        simp [excess', hkd] at ha ⊢
                        omega⟩
                    else
                      ⟨a.val, by
                        have ha := a.isLt
                        simpa [excess', hl] using ha⟩
                    have hEmbed (l : Fin n) : Function.Injective (embed l) := by
                      intro a b hab
                      apply Fin.ext
                      by_cases hl : l = k
                      · simpa [embed, hl] using congrArg Fin.val hab
                      · simpa [embed, hl] using congrArg Fin.val hab
                    have hSigmaEmbed : Function.Injective
                        (fun z : Sigma fun l => Fin (excess' l + 1) =>
                          (⟨z.1, embed z.1 z.2⟩ :
                            Sigma fun l => Fin (A.excess l + 1))) := by
                      exact @Function.Injective.sigma_map
                        (Fin n) (Fin n) (fun l => Fin (excess' l + 1))
                        (fun l => Fin (A.excess l + 1)) id embed
                        Function.injective_id hEmbed
                    let tail : OrderedDisjointBlocks n :=
                      { excess := excess'
                        value := fun l a => A.value l (embed l a)
                        value_injective := by
                          intro x y hxy
                          apply hSigmaEmbed
                          apply A.value_injective
                          exact hxy }
                    have htailSum : Finset.univ.sum tail.excess = M - 1 := by
                      dsimp [tail, excess']
                      rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
                      have hs := Finset.sum_erase_add Finset.univ A.excess
                        (Finset.mem_univ k)
                      rw [hA, hkd] at hs
                      simp only [Finset.sdiff_singleton_eq_erase]
                      omega
                    have htailLt : M - 1 < M := by omega
                    let lift (alpha : Transversal tail) : Transversal A :=
                      fun l => embed l (alpha l)
                    have hLiftWeight (alpha : Transversal tail) :
                        newtonWeight (lift alpha) = newtonWeight alpha + 1 := by
                      unfold newtonWeight
                      calc
                        (∑ l, (lift alpha l).val) =
                            ∑ l, ((alpha l).val + if l = k then 1 else 0) := by
                              apply Finset.sum_congr rfl
                              intro l _
                              by_cases hl : l = k
                              · simp [lift, embed, hl]
                              · simp [lift, embed, hl]
                        _ = (∑ l, (alpha l).val) + 1 := by
                              rw [Finset.sum_add_distrib]
                              simp
                    have hCoefficient (alpha : Transversal tail) :
                        coefficientPoint tail alpha = coefficientPoint A (lift alpha) := by
                      rfl
                    have hInnerOther (alpha : Transversal tail) (l : Fin n) (hl : l ≠ k) :
                        (Finset.Iio (lift alpha l)).prod
                            (fun a => characteristicEval (n := n) (A.value l a)) =
                          (Finset.Iio (alpha l)).prod
                            (fun a => characteristicEval (n := n) (tail.value l a)) := by
                      symm
                      apply Finset.prod_bij (fun a _ => embed l a)
                      · intro a ha
                        rw [Finset.mem_Iio]
                        change (embed l a).val < (lift alpha l).val
                        simpa [lift, embed, hl] using ha
                      · intro a₁ _ a₂ _ heq
                        exact hEmbed l heq
                      · intro b hb
                        let a : Fin (excess' l + 1) := ⟨b.val, by
                          have hbl := b.isLt
                          simpa [excess', hl] using hbl⟩
                        refine ⟨a, ?_, ?_⟩
                        · rw [Finset.mem_Iio]
                          change a.val < (alpha l).val
                          rw [Finset.mem_Iio] at hb
                          change b.val < (lift alpha l).val at hb
                          simpa [a, lift, embed, hl] using hb
                        · apply Fin.ext
                          simp [a, embed, hl]
                      · intro a _
                        rfl
                    have hInnerK (alpha : Transversal tail) :
                        (Finset.Iio (lift alpha k)).prod
                            (fun a => characteristicEval (n := n) (A.value k a)) =
                          g k * (Finset.Iio (alpha k)).prod
                            (fun a => characteristicEval (n := n) (tail.value k a)) := by
                      have hIio : Finset.Iio (lift alpha k) =
                          insert 0 ((Finset.Iio (alpha k)).image (embed k)) := by
                        ext x
                        simp only [Finset.mem_Iio, Finset.mem_insert, Finset.mem_image]
                        constructor
                        · intro hx
                          by_cases hx0 : x = 0
                          · exact Or.inl hx0
                          · right
                            have hxpos : 0 < x.val := by
                              apply Nat.pos_of_ne_zero
                              intro hxv
                              apply hx0
                              apply Fin.ext
                              exact hxv
                            let a : Fin (excess' k + 1) := ⟨x.val - 1, by
                              have hxl := x.isLt
                              simp [excess', hkd] at hxl ⊢
                              omega⟩
                            refine ⟨a, ?_, ?_⟩
                            · have hxv : x.val < (lift alpha k).val := hx
                              have hlift : (lift alpha k).val = (alpha k).val + 1 := by
                                simp [lift, embed]
                              rw [hlift] at hxv
                              exact show a.val < (alpha k).val by
                                dsimp [a]
                                omega
                            · apply Fin.ext
                              dsimp [a]
                              simp [embed]
                              omega
                        · intro hx
                          rcases hx with rfl | ⟨a, ha, rfl⟩
                          · change 0 < (lift alpha k).val
                            simp [lift, embed]
                          · change (embed k a).val < (lift alpha k).val
                            simpa [lift, embed] using Nat.succ_lt_succ ha
                      have hnot : (0 : Fin (A.excess k + 1)) ∉
                          (Finset.Iio (alpha k)).image (embed k) := by
                        simp [embed]
                      rw [hIio, Finset.prod_insert hnot]
                      change characteristicEval (A.value k 0) * _ = _
                      rw [show characteristicEval (A.value k 0) = g k by rfl]
                      congr 1
                      rw [Finset.prod_image (hEmbed k).injOn]
                    have hNewtonLift (alpha : Transversal tail) :
                        newtonPolynomial A (lift alpha) =
                          g k * newtonPolynomial tail alpha := by
                      unfold newtonPolynomial
                      calc
                        (∏ l, ∏ a ∈ Finset.Iio (lift alpha l),
                            characteristicEval (A.value l a)) =
                            (∏ a ∈ Finset.Iio (lift alpha k),
                              characteristicEval (n := n) (A.value k a)) *
                            ∏ l ∈ (Finset.univ.erase k),
                              ∏ a ∈ Finset.Iio (lift alpha l),
                                characteristicEval (n := n) (A.value l a) :=
                          (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)).symm
                        _ = (g k * ∏ a ∈ Finset.Iio (alpha k),
                              characteristicEval (n := n) (tail.value k a)) *
                            ∏ l ∈ (Finset.univ.erase k),
                              ∏ a ∈ Finset.Iio (alpha l),
                                characteristicEval (n := n) (tail.value l a) := by
                          rw [hInnerK]
                          congr 1
                          apply Finset.prod_congr rfl
                          intro l hl
                          exact hInnerOther alpha l (Finset.ne_of_mem_erase hl)
                        _ = g k * (∏ l, ∏ a ∈ Finset.Iio (alpha l),
                              characteristicEval (n := n) (tail.value l a)) := by
                          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
                          ring
                    obtain ⟨ctail, hctail, htailEval⟩ :=
                      ih (M - 1) htailLt tail htailSum r' (Qpart k) (hQpartDegree k)
                    let cA : Transversal A -> Rat := fun alpha =>
                      ∑ gamma : Transversal tail,
                        if lift gamma = alpha then ctail gamma else 0
                    refine ⟨cA, ?_, ?_⟩
                    · intro alpha ha
                      unfold cA
                      apply Finset.sum_eq_zero
                      intro gamma _
                      by_cases hga : lift gamma = alpha
                      · rw [if_pos hga]
                        apply hctail
                        have hw := hLiftWeight gamma
                        rw [hga] at hw
                        omega
                      · simp [hga]
                    · intro beta
                      have hsum :
                          (∑ alpha, cA alpha *
                              MvPolynomial.eval (coefficientPoint A beta)
                                (newtonPolynomial A alpha)) =
                            MvPolynomial.eval (coefficientPoint A beta) (g k) *
                              ∑ gamma, ctail gamma *
                                MvPolynomial.eval (coefficientPoint A beta)
                                  (newtonPolynomial tail gamma) := by
                        unfold cA
                        simp_rw [Finset.sum_mul]
                        rw [Finset.sum_comm, Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro gamma _
                        rw [Finset.sum_eq_single (lift gamma)]
                        · rw [if_pos rfl, hNewtonLift, map_mul]
                          ring
                        · intro alpha _ hne
                          simp [hne.symm]
                        · simp
                      by_cases hbeta : (beta k).val = 0
                      · have hbeta0 : beta k = 0 := Fin.ext hbeta
                        have hgzero :
                            MvPolynomial.eval (coefficientPoint A beta) (g k) = 0 := by
                          unfold g base
                          rw [hCharacteristic]
                          apply Finset.prod_eq_zero (Finset.mem_univ k)
                          simp [hbeta0]
                        rw [map_mul, hgzero, zero_mul, hsum, hgzero, zero_mul]
                      · let betaTail : Transversal tail := fun l => if hl : l = k then
                          ⟨(beta l).val - 1, by
                            subst l
                            have hb := (beta k).isLt
                            simp [tail, excess', hkd] at hb ⊢
                            omega⟩
                        else
                          ⟨(beta l).val, by
                            have hb := (beta l).isLt
                            simpa [tail, excess', hl] using hb⟩
                        have hLiftBeta : lift betaTail = beta := by
                          funext l
                          apply Fin.ext
                          by_cases hl : l = k
                          · subst l
                            have hpos : 0 < (beta k).val := Nat.pos_of_ne_zero hbeta
                            simp [lift, betaTail, embed]
                            omega
                          · simp [lift, betaTail, embed, hl]
                        calc
                          MvPolynomial.eval (coefficientPoint A beta) (g k * Qpart k) =
                              MvPolynomial.eval (coefficientPoint A beta) (g k) *
                                MvPolynomial.eval (coefficientPoint A beta) (Qpart k) := by
                                rw [map_mul]
                          _ = MvPolynomial.eval (coefficientPoint A beta) (g k) *
                                ∑ gamma, ctail gamma *
                                  MvPolynomial.eval (coefficientPoint A beta)
                                    (newtonPolynomial tail gamma) := by
                                rw [← hLiftBeta, ← hCoefficient betaTail,
                                  htailEval betaTail]
                          _ = ∑ alpha, cA alpha *
                                MvPolynomial.eval (coefficientPoint A beta)
                                  (newtonPolynomial A alpha) := hsum.symm
                let termCoeff : Fin n -> Transversal A -> Rat := fun k =>
                  Classical.choose (hTerm k)
                have hTermSupport (k : Fin n) (alpha : Transversal A)
                    (ha : r' + 1 < newtonWeight alpha) : termCoeff k alpha = 0 := by
                  exact (Classical.choose_spec (hTerm k)).1 alpha ha
                have hTermEval (k : Fin n) (beta : Transversal A) :
                    MvPolynomial.eval (coefficientPoint A beta) (g k * Qpart k) =
                      ∑ alpha, termCoeff k alpha *
                        MvPolynomial.eval (coefficientPoint A beta)
                          (newtonPolynomial A alpha) := by
                  exact (Classical.choose_spec (hTerm k)).2 beta
                let alpha0Coeff : Transversal A -> Rat := fun alpha =>
                  if alpha = alpha0 then MvPolynomial.eval y0 P else 0
                let c : Transversal A -> Rat := fun alpha =>
                  alpha0Coeff alpha + ∑ k, termCoeff k alpha
                refine ⟨c, ?_, ?_⟩
                · intro alpha ha
                  have hne : alpha ≠ alpha0 := by
                    intro heq
                    subst alpha
                    simp [newtonWeight, alpha0] at ha
                  simp [c, alpha0Coeff, hne, hTermSupport _ alpha ha]
                · intro beta
                  rw [hPDecomp, map_add, map_sum]
                  simp_rw [hTermEval]
                  rw [Finset.sum_comm]
                  have hzeroNewton : newtonPolynomial A alpha0 = 1 := by
                    have hiio (k : Fin n) : Finset.Iio (alpha0 k) = ∅ := by
                      ext x
                      simp [alpha0]
                    simp [newtonPolynomial, hiio]
                  calc
                    MvPolynomial.eval (coefficientPoint A beta) (C (MvPolynomial.eval y0 P)) +
                        ∑ alpha, ∑ k, termCoeff k alpha *
                          MvPolynomial.eval (coefficientPoint A beta)
                            (newtonPolynomial A alpha) =
                        ∑ alpha, (alpha0Coeff alpha + ∑ k, termCoeff k alpha) *
                          MvPolynomial.eval (coefficientPoint A beta)
                            (newtonPolynomial A alpha) := by
                          have hconstant :
                              MvPolynomial.eval (coefficientPoint A beta)
                                  (C (MvPolynomial.eval y0 P)) =
                                ∑ alpha, alpha0Coeff alpha *
                                  MvPolynomial.eval (coefficientPoint A beta)
                                    (newtonPolynomial A alpha) := by
                            rw [Finset.sum_eq_single alpha0]
                            · simp [alpha0Coeff, hzeroNewton]
                            · intro alpha _ hne
                              simp [alpha0Coeff, hne]
                            · simp
                          rw [hconstant, ← Finset.sum_add_distrib]
                          apply Finset.sum_congr rfl
                          intro alpha _
                          rw [add_mul, Finset.sum_mul]
                    _ = ∑ alpha, c alpha *
                          MvPolynomial.eval (coefficientPoint A beta)
                            (newtonPolynomial A alpha) := by rfl
    intro Q hQ
    obtain ⟨c, hc, hEval⟩ := hSpan (Finset.univ.sum B.excess) B rfl q Q hQ
    refine ⟨fun alpha => c alpha.1, ?_⟩
    intro beta
    rw [hEval beta]
    let f : Transversal B -> Rat := fun alpha =>
      c alpha * MvPolynomial.eval (coefficientPoint B beta)
        (newtonPolynomial B alpha)
    change (∑ alpha, f alpha) =
      ∑ alpha : {alpha : Transversal B // newtonWeight alpha <= q}, f alpha.1
    have houtside :
        (∑ alpha : {alpha : Transversal B // ¬newtonWeight alpha <= q}, f alpha.1) = 0 := by
      apply Finset.sum_eq_zero
      intro alpha _
      unfold f
      rw [hc alpha.1 (by omega)]
      simp
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun alpha : Transversal B => newtonWeight alpha <= q) f
    rw [houtside, add_zero] at hsplit
    exact hsplit.symm

#print axioms colored_transversal_newton_spans

end D5.S3.Combinatorics.Interpolation.ColoredTransversalNewtonSpanning
