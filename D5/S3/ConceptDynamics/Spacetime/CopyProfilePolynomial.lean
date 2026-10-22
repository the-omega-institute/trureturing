/- GID: D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Native time profiles give the full copy polynomial and its finite one-hole slice readout. -/

import D5.S3.ConceptDynamics.Spacetime.RegionFilterQExpressibility
import D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Observation.StrictOneHoleContexts
open ComplementCharge TotalCopyNormalization RegionFilterQExpressibility
open NativeTimeProfile
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Bal := TotalCopyNormalization.B

/-- The diagonal operation that supplies `m` tagged parallel copies of one input. -/
def copies : Nat → Bal → Bal
  | 0, _ => zero
  | n + 1, X => ParallelComposition.parallelBalanced (copies n X) X

/-- The total value of a copy term under an arbitrary independent assignment. -/
def value {r : Nat} (N : CopyTerm r) (v : Fin r → Bal) : Bal :=
  (eval N v).getD zero

/--
The 5B/5C bridge used by the copy argument. It says that a temporal-free
term, evaluated on independently replicated leaves, has an integer polynomial
profile.  The displayed coefficient is the full 5C coefficient and retains the
constant correction `- r * q(N(0))`.
-/
def CopyPolynomialLaw : Prop := ∀ (r : Nat) (N : CopyTerm r), 0 < r → TemporalFree N →
  ∀ X : Bal, ∃ P : Polynomial Int,
    P.natDegree ≤ r ∧
    (∀ n : Nat, P.eval (n : Int) = q (value N (fun _ => copies n X)).val) ∧
    P.coeff 0 = q (zeroValue N).val ∧
    P.coeff 1 = (∑ i : Fin r, q (value N (sliceAssignment i X)).val) -
      (r : Int) * q (zeroValue N).val

private def diagonalPolynomial {r : Nat} {M : Type*} [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) : Polynomial Int :=
  ∑ J : Finset (Fin r), Polynomial.C (f (J.piecewise b a)) * Polynomial.X ^ J.card

private theorem diagonalPolynomial_degree {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) :
    (diagonalPolynomial f a b).natDegree ≤ r := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro J _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by simpa using J.card_le_univ)

private theorem diagonalPolynomial_eval {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) (m : Int) :
    (diagonalPolynomial f a b).eval m = f (fun i => a i + m • b i) := by
  simp only [diagonalPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [show (fun i => a i + m • b i) = (fun i => m • b i) + a from
    funext (fun i => add_comm _ _), f.map_add_univ]
  apply Finset.sum_congr rfl
  intro J _
  have h := f.map_piecewise_smul (fun _ => m) (J.piecewise b a) J
  have hv : J.piecewise (fun i => m • J.piecewise b a i) (J.piecewise b a) =
      J.piecewise (fun i => m • b i) a := by
    funext i
    by_cases hi : i ∈ J <;> simp [Finset.piecewise, hi]
  have hh := (congrArg f hv).symm.trans h
  simpa [smul_eq_mul, mul_comm] using hh.symm

private theorem diagonalPolynomial_zero {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) :
    (diagonalPolynomial f a b).coeff 0 = f a := by
  rw [Polynomial.coeff_zero_eq_eval_zero, diagonalPolynomial_eval]
  simp

private theorem diagonalPolynomial_one {r : Nat} {M : Type*}
    [AddCommGroup M]
    (f : MultilinearMap Int (fun _ : Fin r => M) Int) (a b : Fin r → M) :
    (diagonalPolynomial f a b).coeff 1 =
      (∑ i, f (Function.update a i (a i + b i))) - (r : Int) * f a := by
  have hs : (Finset.univ.filter (fun J : Finset (Fin r) => 1 = J.card)) =
      Finset.univ.image (fun i : Fin r => ({i} : Finset (Fin r))) := by
    ext J
    simp [eq_comm, Finset.card_eq_one]
  have hcoeff : (diagonalPolynomial f a b).coeff 1 =
      ∑ i : Fin r, f (Function.update a i (b i)) := by
    simp only [diagonalPolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [← Finset.sum_filter, hs, Finset.sum_image]
    · simp only [Finset.piecewise_singleton]
    · intro i _ j _ h
      exact Finset.singleton_injective h
  rw [hcoeff]
  simp only [f.map_update_add, Function.update_eq_self, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem gamma_zero : gamma zero.val = 0 := by
  haveI : IsEmpty ↥zero.val.1.current := Finset.isEmpty_coe_sort.mpr zero_empty.2.1
  exact Finset.sum_eq_zero (fun e _ => isEmptyElim e)

private theorem gamma_copies (n : Nat) (X : Bal) :
    gamma (copies n X).val = (n : Int) • gamma X.val := by
  induction n with
  | zero => simp [copies, gamma_zero]
  | succ n ih =>
    rw [copies, gamma_parallel, ih]
    simp [Nat.cast_add, add_smul]

private def basePoint : Augmented := (1, 0)
private def inputPoint (X : Bal) : Augmented := (0, gamma X.val)

private def profileModel {r : Nat} (N : CopyTerm r) :
    MultilinearMap Int (fun _ : Fin r => Augmented) Profile :=
  (LinearMap.snd Int Int Profile).compMultilinearMap (model N)

/-- The coefficient at a set of distinct input occurrences in the complete profile expansion. -/
def profileCoefficients {r : Nat} (N : CopyTerm r) (X : Bal) (J : Finset (Fin r)) : Profile :=
  profileModel N (J.piecewise (fun _ => inputPoint X) (fun _ => basePoint))

/-- Native evaluation on independently many tagged copies has a squarefree profile expansion. -/
theorem profile_multiaffine {r : Nat} (N : CopyTerm r) (hN : TemporalFree N) (X : Bal)
    (v : Fin r → Nat) :
    gamma (value N (fun i => copies (v i) X)).val =
      ∑ J : Finset (Fin r), (∏ i ∈ J, (v i : Int)) • profileCoefficients N X J := by
  let a : Fin r → Augmented := fun _ => basePoint
  let b : Fin r → Augmented := fun _ => inputPoint X
  let f := profileModel N
  have native : gamma (value N (fun i => copies (v i) X)).val =
      f (fun i => a i + (v i : Int) • b i) := by
    obtain ⟨Y, hY⟩ := temporal_free_total N hN (fun i => copies (v i) X)
    have hm := model_eval N hN (fun i => copies (v i) X) Y hY
    have hp : (fun i => pack (copies (v i) X)) =
        (fun i => a i + (v i : Int) • b i) := by
      funext i
      simp [pack, a, b, basePoint, inputPoint, gamma_copies]
    rw [hp] at hm
    simpa only [value, hY, Option.getD_some, pack, f, profileModel,
      LinearMap.compMultilinearMap_apply, LinearMap.snd_apply] using
        (congrArg Prod.snd hm).symm
  rw [native]
  have hab : (fun i => a i + (v i : Int) • b i) =
      (fun i => (v i : Int) • b i) + a := funext (fun i => add_comm _ _)
  rw [hab, f.map_add_univ]
  apply Finset.sum_congr rfl
  intro J _
  have hs := f.map_piecewise_smul (fun i => (v i : Int)) (J.piecewise b a) J
  have hv : J.piecewise (fun i => (v i : Int) • J.piecewise b a i) (J.piecewise b a) =
      J.piecewise (fun i => (v i : Int) • b i) a := by
    funext i
    by_cases hi : i ∈ J <;> simp [Finset.piecewise, hi]
  exact (congrArg f hv).symm.trans hs

/-- Lemma 5B/5C, including the constant correction in the linear coefficient. -/
theorem copy_polynomial_law : CopyPolynomialLaw := by
  intro r N _ hN X
  let a : Fin r → Augmented := fun _ => basePoint
  let b : Fin r → Augmented := fun _ => inputPoint X
  let f := NativeTimeProfile.readout.compMultilinearMap (profileModel N)
  have native (v : Fin r → Bal) :
      f (fun i => pack (v i)) = q (value N v).val := by
    obtain ⟨Y, hY⟩ := temporal_free_total N hN v
    change NativeTimeProfile.readout ((model N (fun i => pack (v i))).2) = _
    rw [model_eval N hN v Y hY]
    simpa [value, hY, pack] using readout_gamma Y.val
  have fzero : f a = q (zeroValue N).val := by
    have hv := native (fun _ => zero)
    simpa [a, pack, basePoint, gamma_zero, value, zeroValue, evalDiagonal] using hv
  have fslice (i : Fin r) : f (Function.update a i (a i + b i)) =
      q (value N (sliceAssignment i X)).val := by
    apply Eq.trans _ (native (sliceAssignment i X))
    apply congrArg f
    funext j
    by_cases hji : j = i <;>
      simp [Function.update_apply, a, b, basePoint, inputPoint, pack,
        sliceAssignment, hji, gamma_zero]
  refine ⟨diagonalPolynomial f a b, diagonalPolynomial_degree f a b, ?_, ?_, ?_⟩
  · intro m
    have hp := congrArg NativeTimeProfile.readout (profile_multiaffine N hN X (fun _ => m))
    rw [readout_gamma] at hp
    rw [hp]
    simp only [diagonalPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro J _
    simp [f, a, b, profileCoefficients, smul_eq_mul, mul_comm]
  · exact (diagonalPolynomial_zero f a b).trans fzero
  · rw [diagonalPolynomial_one, fzero]
    simp only [fslice]

/-- Parallel replication is linear for every fixed region readout. -/
def CopiesRegionLinear : Prop := ∀ (R : Region) (n : Nat) (X : Bal),
  regionReadout R (copies n X) = (n : Int) * regionReadout R X

/-- A readout of a total one-hole word, with failure assigned the neutral integer. -/
def wordReadout (w : Word) (X : Bal) : Int :=
  ((contextDenote nativeSignature w X).map (fun Y => q Y.val)).getD 0

/--
The post-polynomial normalization statement needed by the tail argument.  It
keeps the exact finite family of temporal-free one-hole words and the exact
sum of their readouts.
-/
def CopySliceReadoutLaw : Prop := ∀ (R : Region) (n : Nat) (C : CopyTerm n), 0 < n →
  DiagonalTotal C →
  (∀ X : Bal, ∃ Y : Bal, evalDiagonal C X = some Y ∧ q Y.val = regionReadout R X) →
  ∃ w : Fin n → Word,
    (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) ∧
    ∀ X : Bal, regionReadout R X = ∑ i, wordReadout (w i) X

/-- The finite joint saturation principle used after slice normalization. -/
def CopySaturationLaw : Prop := ∀ {ι : Type} [Fintype ι] (w : ι → Word),
  (∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y) →
  ∃ c : Int, c ≤ 0 ∧ ∀ (p : Fin 3 → Int) (t t' : Int), t < c → t' < c →
    ∃ X Y : Bal, SelectedVariant X Y p t t' ∧
      ∀ i, wordReadout (w i) X = wordReadout (w i) Y

/-- The copy form of Proposition 64. -/
def CopyQExpressible (R : Region) : Prop := ∃ n : Nat, 0 < n ∧ ∃ C : CopyTerm n,
  DiagonalTotal C ∧ ∀ X : Bal, ∃ Y : Bal,
    evalDiagonal C X = some Y ∧ q Y.val = regionReadout R X

/-- Polynomial identification from all natural evaluations. -/
theorem polynomial_identification (P : Polynomial Int) (a : Int)
    (h : ∀ n : Nat, P.eval (n : Int) = (n : Int) * a) :
    P = Polynomial.X * Polynomial.C a := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Int.ofNat_injective).mono
  rintro _ ⟨n, rfl⟩
  simpa using h n

private theorem region_parallel (R : Region) (X Y : Bal) :
    regionReadout R (ParallelComposition.parallelBalanced X Y) =
      regionReadout R X + regionReadout R Y := by
  unfold regionReadout
  simp only [Finset.sum_filter]
  change (∑ e ∈ (X.val.2.val.disjSum Y.val.2.val).map
      (ParallelComposition.equiv X.val.1.archive Y.val.1.archive).toEmbedding,
      if (((ParallelComposition.archive X.val.1.archive Y.val.1.archive).attributes e).time,
          ((ParallelComposition.archive X.val.1.archive Y.val.1.archive).attributes e).position) ∈ R
      then contribution (ParallelComposition.context X.val.1 Y.val.1) e else 0) = _
  rw [Finset.sum_map, Finset.sum_disjSum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _
  · exact congrArg (fun a : Attributes 3 => if (a.time, a.position) ∈ R
        then (if a.positive then (1 : Int) else -1) else 0)
      (ParallelComposition.attributes_left _ _ e)
  · exact congrArg (fun a : Attributes 3 => if (a.time, a.position) ∈ R
        then (if a.positive then (1 : Int) else -1) else 0)
      (ParallelComposition.attributes_right _ _ e)

/-- Every fixed region readout is integer-linear in the number of tagged copies. -/
theorem copies_region_linear : CopiesRegionLinear := by
  intro R n X
  induction n with
  | zero => simp [copies, regionReadout, zero_empty.2.2]
  | succ n ih => rw [copies, region_parallel, ih]; push_cast; ring

/-- Lemma 6: the existing finite predicate construction saturates a whole finite word family. -/
theorem copy_saturation_law : CopySaturationLaw := by
  intro ι _ w hw
  have hn := fun i => normalize_word (w i) (hw i)
  choose w' hf he using hn
  have hr := fun i => reify_temporal_free (w' i) (hf i)
  choose v hv using hr
  obtain ⟨K, hK⟩ := Finite.exists_ge (fun i => timeThreshold (v i))
  let Qs := Finset.univ.toList.flatMap (fun i => requiredPredicates (v i))
  obtain ⟨c, hc, hs⟩ := finite_joint_input Qs (min K 0)
  refine ⟨c, hc.trans (min_le_right K 0), fun p t t' ht ht' => ?_⟩
  obtain ⟨X, Y, pair, h, hx, hy, sat⟩ := hs p t t' ht ht'
  refine ⟨X, Y, pair, fun i => ?_⟩
  unfold wordReadout
  rw [he i X, he i Y, hv i X, hv i Y]
  change q (runSteps (v i) X).val = q (runSteps (v i) Y).val
  apply saturated_runSteps (v i) h
  · rw [hx]
    exact ht.trans_le (hc.trans ((min_le_left K 0).trans (hK i)))
  · rw [hy]
    exact ht'.trans_le (hc.trans ((min_le_left K 0).trans (hK i)))
  · intro Q hQ hnQ
    apply sat Q _ hnQ
    exact List.mem_flatMap.mpr ⟨i, by simp, hQ⟩

/-- The polynomial linear coefficient recovers the fixed finite family of one-hole slices. -/
theorem copy_slice_readout_law : CopySliceReadoutLaw := by
  intro R n C hn ht hC
  obtain ⟨_, _, _, N, _, hN, he, hAll, w, _, hw, hwTotal, _⟩ :=
    total_copy_normalization C hn ht
  refine ⟨w, hwTotal, fun X => ?_⟩
  obtain ⟨P, _, hP, hP0, hP1⟩ := copy_polynomial_law n N hn hN X
  have evals : ∀ m : Nat, P.eval (m : Int) = (m : Int) * regionReadout R X := by
    intro m
    obtain ⟨Y, hY, hq⟩ := hC (copies m X)
    rw [hP m]
    have hNY : eval N (fun _ => copies m X) = some Y := (he _).symm.trans hY
    simp only [value, hNY, Option.getD_some]
    rw [hq, copies_region_linear]
  have pEq := polynomial_identification P (regionReadout R X) evals
  have zeroQ : q (zeroValue N).val = 0 := by
    rw [← hP0, pEq]
    simp
  have coeff1 : P.coeff 1 = regionReadout R X := by rw [pEq]; simp
  rw [coeff1, zeroQ, mul_zero, sub_zero] at hP1
  rw [hP1]
  apply Finset.sum_congr rfl
  intro i _
  unfold wordReadout value
  rw [hw i X]
  obtain ⟨Y, hY⟩ := hAll (sliceAssignment i X)
  rw [hY]
  rfl

/-- A finite sum of total word readouts is a tail readout. -/
theorem sum_word_readouts_implies_tail
    (R : Region) {ι : Type} [Fintype ι]
    (w : ι → Word)
    (hw : ∀ i, ∀ X : Bal, ∃ Y : Bal, contextDenote nativeSignature (w i) X = some Y)
    (hsum : ∀ X : Bal, regionReadout R X = ∑ i, wordReadout (w i) X) : Tail R := by
  obtain ⟨c, _, hc⟩ := copy_saturation_law (ι := ι) w hw
  refine ⟨c, fun p t t' ht ht' => ?_⟩
  obtain ⟨X, Y, pair, same⟩ := hc p t t' ht ht'
  have values : regionReadout R X = regionReadout R Y := by
    rw [hsum X, hsum Y]
    exact Finset.sum_congr rfl (fun i _ => same i)
  obtain ⟨hX, hY⟩ := selected_region_values R X Y p t t' pair
  rw [hX, hY] at values
  split_ifs at values <;> simp_all

/-- Necessity of the copy criterion. -/
theorem copy_q_expressible_implies_tail
    (R : Region) (hR : CopyQExpressible R) : Tail R := by
  obtain ⟨n, hn, C, ht, hC⟩ := hR
  obtain ⟨w, hw, hsum⟩ := copy_slice_readout_law R n C hn ht hC
  exact sum_word_readouts_implies_tail R w hw hsum

/-- Tail regions are copy-expressible by the existing one-hole construction. -/
theorem tail_implies_copy_q_expressible (R : Region) (hR : Tail R) :
    CopyQExpressible R := by
  obtain ⟨w, hw⟩ := (q_expressible_iff_tail R).mpr hR
  refine ⟨1, by decide, wordToCopy w, ?_, ?_⟩
  · intro X
    obtain ⟨Y, hY, _⟩ := hw X
    exact ⟨Y, by simpa only [word_to_copy_denote] using hY⟩
  · intro X
    obtain ⟨Y, hY, hq⟩ := hw X
    exact ⟨Y, by simpa only [word_to_copy_denote] using hY, hq⟩

end
end D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
