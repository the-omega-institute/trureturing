/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDivisors]
   utility: none
   digest: The two critical polynomials stay relatively prime in the ordinary trace chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDivisors
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSWeightedDehomogenization

/-! The independent trace weights permit dehomogenization of the two
complexified trace variables separately. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalChart

open MvPolynomial PeriodicMPSFiveSiteCoordinates PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteWeightedMinors PeriodicMPSFiveSiteCriticalDivisors
  PeriodicMPSFiveSiteCriticalCertificate PeriodicMPSFiveSiteProjectiveLine
  PeriodicMPSWeightedDehomogenization
open scoped BigOperators

open private coordinates_weight from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteWeightedMinors
open private amplitudes map_coordinates map_flatten
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineMinors
open private specialized_minor minorOver_weight
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalDivisors

noncomputable section

private def rightWeights (j : Fin 10) : ℕ := if j.val < 5 then 0 else weights j

private theorem weights_right_le (j : Fin 10) : rightWeights j ≤ 2 := by
  fin_cases j <;> decide

private lemma amplitudes_left_weight (i : Fin 8) :
    (amplitudes (R := P) X true i).IsWeightedHomogeneous rightWeights 0 := by
  let f : Fin 10 → P := fun j => if j.val < 5 then X j else 0
  have hw (j : Fin 10) : (f j).IsWeightedHomogeneous rightWeights 0 := by
    by_cases hj : j.val < 5
    · simpa [f, rightWeights, hj] using isWeightedHomogeneous_X ℤ rightWeights j
    · simpa [f, hj] using isWeightedHomogeneous_zero ℤ rightWeights 0
  let F : P →+* P := eval₂Hom C f
  have hs : ((amplitudes (R := P) X true) i).IsWeightedHomogeneous (fun _ => 0) 0 := by
    intro m _
    simp [Finsupp.weight_apply, Finsupp.sum]
  have h := eval₂Hom_homogeneous _ rightWeights f hw hs
  change (F (amplitudes (R := P) X true i)).IsWeightedHomogeneous rightWeights 0 at h
  have e := congrFun (map_coordinates F (X 0) (X 1) (X 2) (X 3) (X 4)) i
  simp only [Function.comp_apply, F, eval₂Hom_X'] at e
  change F (amplitudes (R := P) X true i) = _ at e
  rw [e] at h
  simpa [amplitudes, f] using h

private lemma amplitudes_right_weight (i : Fin 8) :
    (amplitudes (R := P) X false i).IsWeightedHomogeneous rightWeights 5 := by
  let f : Fin 10 → P := fun j => if j.val < 5 then 0 else X j
  have hw (j : Fin 10) : (f j).IsWeightedHomogeneous rightWeights (weights j) := by
    by_cases hj : j.val < 5
    · simpa [f, hj] using isWeightedHomogeneous_zero ℤ rightWeights (weights j)
    · simpa [f, rightWeights, hj] using isWeightedHomogeneous_X ℤ rightWeights j
  let F : P →+* P := eval₂Hom C f
  have hs := coordinates_weight (X 5) (X 6) (X 7) (X 8) (X 9)
    (isWeightedHomogeneous_X ℤ weights 5) (isWeightedHomogeneous_X ℤ weights 6)
    (isWeightedHomogeneous_X ℤ weights 7) (isWeightedHomogeneous_X ℤ weights 8)
    (isWeightedHomogeneous_X ℤ weights 9) i
  have h := eval₂Hom_homogeneous weights rightWeights f hw hs
  change (F (amplitudes (R := P) X false i)).IsWeightedHomogeneous rightWeights 5 at h
  have e := congrFun (map_coordinates F (X 5) (X 6) (X 7) (X 8) (X 9)) i
  simp only [Function.comp_apply, F, eval₂Hom_X'] at e
  change F (amplitudes (R := P) X false i) = _ at e
  rw [e] at h
  simpa [amplitudes, f] using h

private lemma flatten_weight {w : Fin 10 → ℕ} {d : ℕ} (p : Fin 8 → P)
    (hp : ∀ i, (p i).IsWeightedHomogeneous w d) (i : Fin 4) (j : Fin 8) :
    (flatten p i j).IsWeightedHomogeneous w d := by
  fin_cases i <;> fin_cases j <;> exact hp _

private lemma observation_right_weight (i : Fin 10) :
    (observation (R := P) X i).IsWeightedHomogeneous rightWeights 5 := by
  unfold observation
  apply IsWeightedHomogeneous.sum
  intro j _
  exact (flatten_weight _ amplitudes_left_weight _ _).mul
    (flatten_weight _ amplitudes_right_weight _ _)

private lemma right_degree_sum (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    ∑ j : Fin 9, (5 - rightWeights (k.succAbove j)) = 37 := by
  rcases hk with rfl | rfl <;> decide

private theorem minor_right_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (symbolicMinor k).IsWeightedHomogeneous rightWeights 37 := by
  classical
  rw [symbolicMinor, Matrix.det_apply, ← right_degree_sum k hk]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun j : Fin 9 => pderiv (k.succAbove j) (observation (R := P) X (k.succAbove (σ j))))
    (fun j => 5 - rightWeights (k.succAbove j))
    (fun j _ => (observation_right_weight _).pderiv (Nat.sub_add_cancel
      ((weights_right_le _).trans (by decide))))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using h
  · simpa [hs, Units.neg_smul] using h.neg

/-- An ordering in which the two first trace coordinates are the two removed variables. -/
def chartOrder : Fin 10 ≃ Option (Option (Fin 8)) :=
  ((Equiv.swap (1 : Fin 10) 5).trans (finSuccEquiv 9)).trans
    ((finSuccEquiv 8).optionCongr)

private def chartWeights (j : Option (Fin 8)) : ℕ := weights (chartOrder.symm (some j))

private def chartRightWeights (j : Option (Fin 8)) : ℕ :=
  rightWeights (chartOrder.symm (some j))

private lemma weights_chart :
    weights ∘ chartOrder.symm = fun j => j.elim 1 chartWeights := by
  funext j
  cases j with
  | none => decide
  | some j => rfl

private lemma right_weights_chart :
    rightWeights ∘ chartOrder.symm = fun j => j.elim 0 chartRightWeights := by
  funext j
  cases j with
  | none => decide
  | some j => rfl

private lemma right_weights_second :
    chartRightWeights = fun j => j.elim 1 (fun l => chartRightWeights (some l)) := by
  funext j
  cases j with
  | none => decide
  | some j => rfl

variable {K : Type*} [Field K] [CharZero K]

private def orderedMinor (k : Fin 10) : MvPolynomial (Option (Option (Fin 8))) K :=
  renameEquiv K chartOrder (minorOver k)

/-- The critical minor after both affine trace coordinates are set to one. -/
def chartMinor (k : Fin 10) : MvPolynomial (Fin 8) K :=
  dehom (dehom (orderedMinor k))

private theorem minor_ne_zero (k : Fin 10) (hk : k = 0 ∨ k = 1) : minorOver (K := K) k ≠ 0 := by
  intro h
  have he := specialized_minor (K := K) k
  rw [h, map_zero] at he
  have hmap : (linePolynomial k).map (Int.castRingHom K) =
      residualMinor (Polynomial.X : Polynomial K) k := by
    simpa [linePolynomial] using map_minor (Polynomial.mapRingHom (Int.castRingHom K))
      (Polynomial.X : Polynomial ℤ) k
  have hd := Polynomial.natDegree_map_eq_of_injective
    (f := Int.castRingHom K) Int.cast_injective (p := linePolynomial k)
  rw [hmap, ← he, Polynomial.natDegree_zero] at hd
  rcases hk with rfl | rfl
  · rw [integral_certificate.1] at hd
    omega
  · rw [integral_certificate.2.1] at hd
    omega

private theorem ordered_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (orderedMinor (K := K) k).IsWeightedHomogeneous (fun j => j.elim 1 chartWeights) 75 := by
  simpa only [orderedMinor, weights_chart] using rename_homogeneous chartOrder weights
    (minorOver_weight (K := K) k hk)

private theorem dehom_right_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (dehom (orderedMinor (K := K) k)).IsWeightedHomogeneous
      (fun j => j.elim 1 (fun l => chartRightWeights (some l))) 37 := by
  have hm : (minorOver (K := K) k).IsWeightedHomogeneous rightWeights 37 := by
    intro m hn
    exact minor_right_weight k hk (mem_support_iff.mp (support_map_subset _ _
      (mem_support_iff.mpr hn)))
  have h := rename_homogeneous chartOrder rightWeights hm
  rw [right_weights_chart] at h
  have hh := dehom_homogeneous_of_weight_zero chartRightWeights h
  rw [right_weights_second] at hh
  exact hh

/-- The two affine critical equations have no common nonunit divisor. -/
theorem relatively_prime_chartMinors :
    IsRelPrime (chartMinor (K := K) 0) (chartMinor (K := K) 1) := by
  let e := renameEquiv K chartOrder
  have hp (k : Fin 10) (hk : k = 0 ∨ k = 1) : orderedMinor (K := K) k ≠ 0 := by
    intro he
    apply minor_ne_zero (K := K) k hk
    exact e.injective (he.trans (map_zero e).symm)
  have h : IsRelPrime (orderedMinor (K := K) 0) (orderedMinor (K := K) 1) := by
    apply IsRelPrime.of_map e.symm
    simpa only [orderedMinor, AlgEquiv.symm_apply_apply, e] using
      (relatively_prime_minors (K := K))
  have h' := relatively_prime_dehom chartWeights (hp 0 (.inl rfl)) (hp 1 (.inr rfl)) h
    (ordered_weight 0 (.inl rfl)) (ordered_weight 1 (.inr rfl))
  exact relatively_prime_dehom (fun l => chartRightWeights (some l))
    (dehom_ne_zero chartWeights (hp 0 (.inl rfl)) (ordered_weight 0 (.inl rfl)))
    (dehom_ne_zero chartWeights (hp 1 (.inr rfl)) (ordered_weight 1 (.inr rfl))) h'
    (dehom_right_weight 0 (.inl rfl)) (dehom_right_weight 1 (.inr rfl))

theorem first_chartMinor_ne_zero : chartMinor (K := K) 0 ≠ 0 := by
  have h : orderedMinor (K := K) 0 ≠ 0 := by
    intro e
    apply first_minor_ne_zero (K := K)
    exact (renameEquiv K chartOrder).injective (e.trans (map_zero _).symm)
  exact dehom_ne_zero _ (dehom_ne_zero _ h (ordered_weight 0 (.inl rfl)))
    (dehom_right_weight 0 (.inl rfl))

private theorem eval_dehom {ι : Type*} (x : ι → K) (p : MvPolynomial (Option ι) K) :
    eval x (dehom p) = eval (fun i => i.elim 1 x) p := by
  have h : (eval x).comp dehom = eval (fun i => i.elim 1 x) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [dehom]
    · rintro (_ | i) <;> simp [dehom]
  exact RingHom.congr_fun h p

/-- Evaluating the affine minor inserts one in both missing trace coordinates. -/
theorem eval_chartMinor (x : Fin 8 → K) (k : Fin 10) :
    eval x (chartMinor k) =
      eval (fun j => (chartOrder j).elim 1 (fun i => i.elim 1 x)) (minorOver k) := by
  rw [chartMinor, eval_dehom, eval_dehom, orderedMinor, renameEquiv_apply, eval_rename]
  rfl

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalChart
