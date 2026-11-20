/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCriticalCertificate]
   utility: none
   digest: Independent trace weights and a full-degree line certificate give relatively prime affine critical minors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCriticalCertificate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSWeightedDehomogenization

/-! The six-site cofactors have degrees 47 and 46 in the two independent
weighted trace blocks. Full degree on the certified line detects every
common divisor before the two trace coordinates are set to one. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalChart

open MvPolynomial PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteWeightedMinors PeriodicMPSSixSiteProjectiveLine
  PeriodicMPSSixSiteCriticalCertificate PeriodicMPSWeightedDehomogenization
  PeriodicMPSWeightedLineSpecialization
open PeriodicMPSFiveSiteLineMinors (line)
open PeriodicMPSSixSiteMarginal (flatten necklaceTable)
open scoped BigOperators

open private coordinates_weight degree_line
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteWeightedMinors
open private amplitudes map_amplitudes observedRows
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteLineMinors

noncomputable section

/-- Restrict the trace weights to the forward block (`true`) or reverse block (`false`). -/
def blockWeights (left : Bool) (j : Fin 10) : ℕ :=
  if decide (j.val < 5) = left then weights j else 0

private lemma blockWeights_le (left : Bool) (j : Fin 10) : blockWeights left j ≤ 2 := by
  cases left <;> fin_cases j <;> decide

set_option maxHeartbeats 1500000 in
-- Check the two finite blocks of the weight assignment.
private lemma amplitudes_weight (side left : Bool) (i : Fin 14) :
    (amplitudes (R := P) X side i).IsWeightedHomogeneous (blockWeights left)
      (if side = left then 6 else 0) := by
  let f : Fin 10 → P := fun j => if decide (j.val < 5) = side then X j else 0
  let w : Fin 10 → ℕ := fun j => if side = left then weights j else 0
  have hf (j : Fin 10) : (f j).IsWeightedHomogeneous (blockWeights left) (w j) := by
    by_cases hj : decide (j.val < 5) = side
    · by_cases hs : side = left
      · have hj' := hj.trans hs
        simpa [f, w, blockWeights, hj, hs, hj'] using
          isWeightedHomogeneous_X ℤ (blockWeights left) j
      · have hj' : decide (j.val < 5) ≠ left := fun h => hs (hj.symm.trans h)
        simpa [f, w, blockWeights, hj, hs, hj'] using
          isWeightedHomogeneous_X ℤ (blockWeights left) j
    · simpa [f, hj] using isWeightedHomogeneous_zero ℤ (blockWeights left) (w j)
  have htotal : (amplitudes (R := P) X side i).IsWeightedHomogeneous weights 6 := by
    cases side
    · exact coordinates_weight _ _ _ _ _ _
        ((isWeightedHomogeneous_X ℤ weights 5).pow 2)
        ((isWeightedHomogeneous_X ℤ weights 5).mul (isWeightedHomogeneous_X ℤ weights 6))
        ((isWeightedHomogeneous_X ℤ weights 6).pow 2)
        (isWeightedHomogeneous_X ℤ weights 7) (isWeightedHomogeneous_X ℤ weights 8)
        (isWeightedHomogeneous_X ℤ weights 9) i
    · exact coordinates_weight _ _ _ _ _ _
        ((isWeightedHomogeneous_X ℤ weights 0).pow 2)
        ((isWeightedHomogeneous_X ℤ weights 0).mul (isWeightedHomogeneous_X ℤ weights 1))
        ((isWeightedHomogeneous_X ℤ weights 1).pow 2)
        (isWeightedHomogeneous_X ℤ weights 2) (isWeightedHomogeneous_X ℤ weights 3)
        (isWeightedHomogeneous_X ℤ weights 4) i
  have hs : (amplitudes (R := P) X side i).IsWeightedHomogeneous w
      (if side = left then 6 else 0) := by
    by_cases h : side = left
    · simpa [w, h] using htotal
    · intro m _
      simp [w, h, Finsupp.weight_apply, Finsupp.sum]
  let F : P →+* P := eval₂Hom C f
  have hFX : F ∘ (X : Fin 10 → P) = f := by
    funext j
    exact eval₂Hom_X' _ _ _
  have he := congrFun (map_amplitudes F (X : Fin 10 → P) side) i
  rw [hFX] at he
  have hfix : amplitudes f side i = amplitudes (R := P) X side i := by
    cases side
    · have hx (j : Fin 10) (hj : ¬ j.val < 5) : f j = X j := by simp [f, hj]
      simp only [amplitudes, Bool.false_eq_true, if_false, hx 5 (by decide),
        hx 6 (by decide), hx 7 (by decide), hx 8 (by decide), hx 9 (by decide)]
    · have hx (j : Fin 10) (hj : j.val < 5) : f j = X j := by simp [f, hj]
      simp only [amplitudes, if_true, hx 0 (by decide), hx 1 (by decide),
        hx 2 (by decide), hx 3 (by decide), hx 4 (by decide)]
  have h := eval₂Hom_homogeneous w (blockWeights left) f hf hs
  change (F (amplitudes (R := P) X side i)).IsWeightedHomogeneous (blockWeights left) _ at h
  change F (amplitudes (R := P) X side i) = amplitudes f side i at he
  rwa [he, hfix] at h

/-- The raw observation has degree six in each independent weighted trace block. -/
theorem observation_block_weight (left : Bool) (i : Fin 10) :
    (observation (R := P) X i).IsWeightedHomogeneous (blockWeights left) 6 := by
  unfold observation
  apply IsWeightedHomogeneous.sum
  intro j _
  dsimp only [flatten]
  have h := (amplitudes_weight true left (necklaceTable (observedRows i).1 j)).mul
    (amplitudes_weight false left (necklaceTable (observedRows i).2 j))
  cases left <;> exact h

private lemma block_degree_sum (left : Bool) (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    ∑ j : Fin 9, (6 - blockWeights left (k.succAbove j)) = if left then 47 else 46 := by
  rcases hk with rfl | rfl <;> cases left <;> decide

private lemma symbolicMinor_block_weight (left : Bool) (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (symbolicMinor k).IsWeightedHomogeneous (blockWeights left) (if left then 47 else 46) := by
  classical
  rw [symbolicMinor, Matrix.det_apply, ← block_degree_sum left k hk]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun j : Fin 9 => pderiv (k.succAbove j) (observation (R := P) X (k.succAbove (σ j))))
    (fun j => 6 - blockWeights left (k.succAbove j))
    (fun j _ => (observation_block_weight left _).pderiv
      (Nat.sub_add_cancel ((blockWeights_le left _).trans (by decide))))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using h
  · simpa [hs, Units.neg_smul] using h.neg

/-- The two selected minors have forward and reverse weighted degrees 47 and 46. -/
theorem symbolicMinor_bidegree (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (symbolicMinor k).IsWeightedHomogeneous (blockWeights true) 47 ∧
      (symbolicMinor k).IsWeightedHomogeneous (blockWeights false) 46 :=
  ⟨symbolicMinor_block_weight true k hk, symbolicMinor_block_weight false k hk⟩

section Coefficients

variable {R : Type*} [CommRing R]

/-- The integer cofactor with coefficients in the target ring. -/
def minorOver (k : Fin 10) : MvPolynomial (Fin 10) R :=
  MvPolynomial.map (Int.castRingHom R) (symbolicMinor k)

/-- Evaluating the cofactor at any two weighted tuples gives the associated
subdeterminant of the six-site observation Jacobian. -/
theorem evaluated_symbolicMinor_at (a : Fin 10 → R) (k : Fin 10) :
    (symbolicMinor k).eval₂ (Int.castRingHom R) a =
      ((jacobian a).submatrix k.succAbove k.succAbove).det := by
  let F := eval₂Hom (Int.castRingHom R) a
  change F (symbolicMinor k) = _
  rw [symbolicMinor, RingHom.map_det]
  congr 1
  ext i j
  exact evaluated_derivative _ _ _

theorem eval_minorOver (a : Fin 10 → R) (k : Fin 10) :
    eval a (minorOver k) = ((jacobian a).submatrix k.succAbove k.succAbove).det := by
  rw [minorOver, MvPolynomial.eval_map]
  exact evaluated_symbolicMinor_at a k

private lemma minorOver_homogeneous {w : Fin 10 → ℕ} {n : ℕ} {k : Fin 10}
    (h : (symbolicMinor k).IsWeightedHomogeneous w n) :
    (minorOver (R := R) k).IsWeightedHomogeneous w n := by
  intro m hm
  exact h (mem_support_iff.mp (support_map_subset _ _ (mem_support_iff.mpr hm)))

theorem minorOver_bidegree (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (minorOver (R := R) k).IsWeightedHomogeneous (blockWeights true) 47 ∧
      (minorOver (R := R) k).IsWeightedHomogeneous (blockWeights false) 46 :=
  ⟨minorOver_homogeneous (symbolicMinor_bidegree k hk).1,
    minorOver_homogeneous (symbolicMinor_bidegree k hk).2⟩

end Coefficients

variable {K : Type*} [Field K] [CharZero K]

private lemma specialized_minor (k : Fin 10) :
    eval₂Hom Polynomial.C (line (Polynomial.X : Polynomial K)) (minorOver k) =
      residualMinor (Polynomial.X : Polynomial K) k := by
  rw [minorOver, MvPolynomial.eval₂Hom_map_hom]
  have h : (Polynomial.C : K →+* Polynomial K).comp (Int.castRingHom K) =
      Int.castRingHom (Polynomial K) := RingHom.ext_int _ _
  exact h ▸ evaluated_symbolicMinor _ k

private lemma full_degree (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (residualMinor (Polynomial.X : Polynomial K) k).natDegree = 93 := by
  have hmap : (linePolynomial k).map (Int.castRingHom K) =
      residualMinor (Polynomial.X : Polynomial K) k := by
    simpa [linePolynomial] using map_minor (Polynomial.mapRingHom (Int.castRingHom K))
      (Polynomial.X : Polynomial ℤ) k
  rw [← hmap, Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
  rcases hk with rfl | rfl
  · exact integral_certificate.1
  · exact integral_certificate.2.1

private lemma restricted_ne_zero (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    residualMinor (Polynomial.X : Polynomial K) k ≠ 0 := by
  intro h
  have hd := full_degree (K := K) k hk
  rw [h, Polynomial.natDegree_zero] at hd
  omega

private lemma minor_ne_zero (k : Fin 10) (hk : k = 0 ∨ k = 1) : minorOver (R := K) k ≠ 0 := by
  intro h
  have he := specialized_minor (K := K) k
  rw [h, map_zero] at he
  exact restricted_ne_zero k hk he.symm

/-- The full weighted minors have no common nonunit divisor. -/
theorem relatively_prime_minors : IsRelPrime (minorOver (R := K) 0) (minorOver (R := K) 1) := by
  apply isRelPrime_of_full_degree_specialization weights
    (fun i => by fin_cases i <;> decide) (line (Polynomial.X : Polynomial K)) degree_line
    _ _ 93 (minorOver_homogeneous (symbolicMinor_weight 0 (.inl rfl)))
  · rw [specialized_minor]
    exact full_degree 0 (.inl rfl)
  · rw [specialized_minor]
    exact restricted_ne_zero 0 (.inl rfl)
  · rw [specialized_minor, specialized_minor]
    exact coprime_restrictions

/-- The two distinguished traces (at indices 0 and 5) are removed successively. -/
def chartOrder : Fin 10 ≃ Option (Option (Fin 8)) :=
  ((Equiv.swap (1 : Fin 10) 5).trans (finSuccEquiv 9)).trans
    ((finSuccEquiv 8).optionCongr)

private def chartWeights (j : Option (Fin 8)) : ℕ := weights (chartOrder.symm (some j))

private def chartRightWeights (j : Option (Fin 8)) : ℕ :=
  blockWeights false (chartOrder.symm (some j))

private lemma weights_chart :
    weights ∘ chartOrder.symm = fun j => j.elim 1 chartWeights := by
  funext j
  cases j with
  | none => decide
  | some j => rfl

private lemma right_weights_chart :
    blockWeights false ∘ chartOrder.symm = fun j => j.elim 0 chartRightWeights := by
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

private def orderedMinor (k : Fin 10) : MvPolynomial (Option (Option (Fin 8))) K :=
  renameEquiv K chartOrder (minorOver k)

/-- The cofactor in the affine chart with both distinguished traces equal to one. -/
def chartMinor (k : Fin 10) : MvPolynomial (Fin 8) K :=
  dehom (dehom (orderedMinor k))

private theorem ordered_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (orderedMinor (K := K) k).IsWeightedHomogeneous (fun j => j.elim 1 chartWeights) 93 := by
  simpa only [orderedMinor, weights_chart] using rename_homogeneous chartOrder weights
    (minorOver_homogeneous (R := K) (symbolicMinor_weight k hk))

private theorem dehom_right_weight (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    (dehom (orderedMinor (K := K) k)).IsWeightedHomogeneous
      (fun j => j.elim 1 (fun l => chartRightWeights (some l))) 46 := by
  have h := rename_homogeneous chartOrder (blockWeights false) (minorOver_bidegree (R := K) k hk).2
  rw [right_weights_chart] at h
  have hh := dehom_homogeneous_of_weight_zero chartRightWeights h
  rwa [right_weights_second] at hh

private theorem orderedMinor_ne_zero (k : Fin 10) (hk : k = 0 ∨ k = 1) :
    orderedMinor (K := K) k ≠ 0 := by
  intro h
  apply minor_ne_zero (K := K) k hk
  exact (renameEquiv K chartOrder).injective (h.trans (map_zero _).symm)

/-- The two affine critical equations have no common nonunit divisor. -/
theorem relatively_prime_chartMinors :
    IsRelPrime (chartMinor (K := K) 0) (chartMinor (K := K) 1) := by
  let e := renameEquiv K chartOrder
  have h : IsRelPrime (orderedMinor (K := K) 0) (orderedMinor (K := K) 1) := by
    apply IsRelPrime.of_map e.symm
    simpa only [orderedMinor, AlgEquiv.symm_apply_apply, e] using
      (relatively_prime_minors (K := K))
  have h₀ := orderedMinor_ne_zero (K := K) 0 (.inl rfl)
  have h₁ := orderedMinor_ne_zero (K := K) 1 (.inr rfl)
  have hw₀ := ordered_weight (K := K) 0 (.inl rfl)
  have hw₁ := ordered_weight (K := K) 1 (.inr rfl)
  have h' := relatively_prime_dehom chartWeights h₀ h₁ h hw₀ hw₁
  exact relatively_prime_dehom (fun l => chartRightWeights (some l))
    (dehom_ne_zero chartWeights h₀ hw₀) (dehom_ne_zero chartWeights h₁ hw₁) h'
    (dehom_right_weight 0 (.inl rfl)) (dehom_right_weight 1 (.inr rfl))

theorem first_chartMinor_ne_zero : chartMinor (K := K) 0 ≠ 0 :=
  dehom_ne_zero _ (dehom_ne_zero _ (orderedMinor_ne_zero 0 (.inl rfl))
    (ordered_weight 0 (.inl rfl))) (dehom_right_weight 0 (.inl rfl))

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalChart
