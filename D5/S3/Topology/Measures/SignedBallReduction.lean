/- GID: D5/S3/Topology/Measures/SignedBallReduction
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/SignedBallReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed raw splitting yields a normalized disjoint full Stone–Cech embedding. -/

import D5.S3.Topology.Measures.SignedGrothendieckCriterion
import D5.S3.Topology.Measures.WeakStarPerturbation
import D5.S3.Topology.Measures.ClopenDisjointization
import D5.S3.Topology.StoneCech.CountableAvoidance

/-! # The full signed dual-ball analytic reduction -/

open Set Filter Topology Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace D5.S3.Topology.Measures.SignedBallReduction

open NormPreservingLifts SignedRieszRepresentation WeakStarPerturbation
open D5.S3.Topology.StoneCech.CountableAvoidance

universe u

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

private lemma functional_smul (c : ℝ) (s : SignedMeasure K) :
    signedFunctional (c • s) = c • signedFunctional s := by
  ext g
  change (∫ᵛ x, g x ∂•(c • s)) = c • (∫ᵛ x, g x ∂•s)
  exact VectorMeasure.integral_smul_vectorMeasure _ _

private lemma functional_add (s t : SignedMeasure K) :
    signedFunctional (s + t) = signedFunctional s + signedFunctional t := by
  ext g
  change (∫ᵛ x, g x ∂•(s + t)) = (∫ᵛ x, g x ∂•s) + (∫ᵛ x, g x ∂•t)
  apply VectorMeasure.integral_add_vectorMeasure
  all_goals
    rw [VectorMeasure.Integrable, ← SignedMeasure.totalVariation_eq_variation]
    exact g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma functional_sub (s t : SignedMeasure K) :
    signedFunctional (s - t) = signedFunctional s - signedFunctional t := by
  calc
    signedFunctional (s - t) = signedFunctional (s + (-1 : ℝ) • t) := by
      rw [neg_one_smul, sub_eq_add_neg]
    _ = signedFunctional s + (-1 : ℝ) • signedFunctional t := by
      rw [functional_add, functional_smul]
    _ = signedFunctional s - signedFunctional t := by
      rw [neg_one_smul, sub_eq_add_neg]

private lemma map_injective (j : ℕ → ℕ) (hj : Injective j) :
    Injective (Ultrafilter.map j) := by
  intro p q h
  exact Ultrafilter.coe_injective ((Filter.map_injective hj) (congrArg Ultrafilter.toFilter h))

private lemma map_free (j : ℕ → ℕ) (hj : Injective j)
    (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ cofinite) :
    (Ultrafilter.map j p : Filter ℕ) ≤ cofinite :=
  (Filter.map_mono hp).trans hj.tendsto_cofinite

private lemma principal_limit (f : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ))
    (hf : Continuous f) (p : Ultrafilter ℕ) (g : C(K, ℝ)) :
    Tendsto (fun n => f (pure n) g) (p : Filter ℕ) (𝓝 (f p g)) :=
  (((WeakDual.eval_continuous g).comp hf).tendsto p).comp p.tendsto_pure_self

private lemma two_free :
    ∃ p q : Ultrafilter ℕ, (p : Filter ℕ) ≤ cofinite ∧
      (q : Filter ℕ) ≤ cofinite ∧ p ≠ q := by
  let p : Ultrafilter ℕ := hyperfilter ℕ
  obtain ⟨A, hA, hnot⟩ := exists_infinite_notMem (fun _ => p)
    (fun _ => hyperfilter_le_cofinite)
  obtain ⟨j, hj, hjA⟩ :=
    D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation.enumerate_pool hA
  let q := Ultrafilter.map j p
  have hAq : A ∈ q := Ultrafilter.mem_map.mpr
    (mem_of_superset univ_mem (fun n _ => hjA n))
  exact ⟨p, q, hyperfilter_le_cofinite,
    map_free j hj.injective p hyperfilter_le_cofinite, fun h => hnot 0 (h.symm ▸ hAq)⟩

/-- An embedding in the entire real signed dual unit ball produces actual
regular norm-one signed measures with disjoint Borel carriers and an
injective extension on every principal and free ultrafilter. -/
theorem exists_normalized_disjoint_embedding
    (h : StoneCech ℕ → WeakDual ℝ C(K, ℝ))
    (hh : Continuous h) (hhi : Injective h)
    (hball : ∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) :
    ∃ (b : ℕ → SignedMeasure K) (E : ℕ → Set K)
      (f : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ)),
      (∀ n, (b n).totalVariation.Regular) ∧
      (∀ n, (b n).totalVariation.real univ = 1) ∧
      (∀ n, MeasurableSet (E n)) ∧ Pairwise (Disjoint on E) ∧
      (∀ n, (b n).totalVariation (E n)ᶜ = 0) ∧
      Continuous f ∧ Injective f ∧
      (∀ n, f (pure n) = StrongDual.toWeakDual (signedFunctional (b n))) ∧
      ∀ p, ‖WeakDual.toStrongDual (f p)‖ ≤ 1 := by
  classical
  let e : Ultrafilter ℕ ≃ₜ StoneCech ℕ := ultrafilterHomeomorph
  let x : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ) := h ∘ e
  have hx : Continuous x := hh.comp e.continuous
  have hxi : Injective x := hhi.comp e.injective
  have reps (n : ℕ) := signed_riesz_markov_kakutani (K := K) |>.2.2
    (WeakDual.toStrongDual (x (pure n)))
  choose s hs hrep hnorm using reps
  have hb : ∃ B : ℝ, ∀ n, (s n).totalVariation.real univ ≤ B :=
    ⟨1, fun n => by rw [hnorm n]; exact hball _⟩
  obtain ⟨j, E, r, vInf, hj, hE, hdis, hdec, hreg, hmass,
    hr, hlim, hvreg, hv⟩ :=
    SignedGrothendieckCriterion.exists_signed_raw_restriction_splitting s hs hb
  let u (n : ℕ) : SignedMeasure K := (s (j n)).restrict (E n)
  let v (n : ℕ) : SignedMeasure K := (s (j n)).restrict (E n)ᶜ
  let U (n : ℕ) := signedFunctional (u n)
  let V := signedFunctional vInf
  let xj : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ) := x ∘ Ultrafilter.map j
  have hxj : Continuous xj := hx.comp (continuous_map j)
  have hxji : Injective xj := hxi.comp (map_injective j hj.injective)
  have hUnorm (n : ℕ) : ‖U n‖ = (u n).totalVariation.real univ :=
    (signed_riesz_markov_kakutani (K := K)).2.1 _ (hreg n).1 |>.symm
  have hUbound (n : ℕ) : ‖U n‖ ≤ 1 := by
    rw [hUnorm n]
    have ht := hmass n
    have hsone : (s (j n)).totalVariation.real univ ≤ 1 := by
      rw [hnorm]; exact hball _
    have hn : 0 ≤ (v n).totalVariation.real univ := measureReal_nonneg
    dsimp [u, v] at *
    linarith
  have hUlim : Tendsto (fun n => ‖U n‖) atTop (𝓝 r) := by
    simpa only [hUnorm] using hlim
  obtain ⟨uhat, huhat, huext, hubound⟩ := exists_bounded_extension U 1 hUbound
  have hvscalar (g : C(K, ℝ)) :
      Tendsto (fun n => signedFunctional (v n) g) atTop (𝓝 (V g)) :=
    hv (NormedSpace.inclusionInDoubleDual ℝ C(K, ℝ) g)
  have hsplit (n : ℕ) : WeakDual.toStrongDual (xj (pure n)) =
      U n + signedFunctional (v n) := by
    change WeakDual.toStrongDual (x (Ultrafilter.map j (pure n))) = _
    rw [Ultrafilter.map_pure, ← hrep, hdec (n), functional_add]
  have hfree (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ cofinite) :
      WeakDual.toStrongDual (uhat p) = WeakDual.toStrongDual (xj p) - V := by
    ext g
    have hu := principal_limit uhat huhat p g
    simp only [huext] at hu
    change Tendsto (fun n => U n g) (p : Filter ℕ) (𝓝 (uhat p g)) at hu
    have hvp := (hvscalar g).mono_left (hp.trans_eq Nat.cofinite_eq_atTop)
    have hxp := principal_limit xj hxj p g
    have he : ∀ n, U n g + signedFunctional (v n) g = xj (pure n) g := by
      intro n
      exact congrArg (fun F : StrongDual ℝ C(K, ℝ) => F g) (hsplit n).symm
    have hl := tendsto_nhds_unique (by simpa only [he] using hu.add hvp) hxp
    change uhat p g = xj p g - V g
    linarith
  have hrpos : 0 < r := by
    by_contra h
    have hrzero : r = 0 := le_antisymm (le_of_not_gt h) hr
    have hUzero : Tendsto U atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (hrzero ▸ hUlim)
    have hconst (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ cofinite) :
        WeakDual.toStrongDual (xj p) = V := by
      have hu0 : WeakDual.toStrongDual (uhat p) = 0 := by
        ext g
        have ht := ((ContinuousLinearMap.apply ℝ ℝ g).continuous.tendsto 0).comp hUzero
        have ht' := ht.mono_left (hp.trans_eq Nat.cofinite_eq_atTop)
        have hu := principal_limit uhat huhat p g
        simp only [huext] at hu
        apply tendsto_nhds_unique hu
        convert ht' using 1 <;> rfl
      have he := hfree p hp
      rw [hu0] at he
      exact sub_eq_zero.mp he.symm
    obtain ⟨p, q, hp, hq, hpq⟩ := two_free
    exact hpq (hxji (WeakDual.toStrongDual.injective ((hconst p hp).trans (hconst q hq).symm)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hUlim.eventually_const_lt hrpos)
  let k : ℕ → ℕ := fun n => n + N
  have hk : StrictMono k := fun a b hab => Nat.add_lt_add_right hab N
  let b (n : ℕ) : SignedMeasure K := ‖U (k n)‖⁻¹ • u (k n)
  have hpos (n : ℕ) : 0 < ‖U (k n)‖ := hN _ (Nat.le_add_left N n)
  have hbreg (n : ℕ) : (b n).totalVariation.Regular := by
    letI : (u (k n)).totalVariation.Regular := (hreg (k n)).1
    dsimp [b]
    rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
      ← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hbnorm (n : ℕ) : (b n).totalVariation.real univ = 1 := by
    dsimp [b]
    rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
      measureReal_nnreal_smul_apply, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hpos n)), ← SignedMeasure.totalVariation_eq_variation,
      ← hUnorm, inv_mul_cancel₀ (hpos n).ne']
  have hbcarry (n : ℕ) : (b n).totalVariation (E (k n))ᶜ = 0 := by
    dsimp [b, u]
    rw [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
      VectorMeasure.variation_restrict (hE (k n)), Measure.smul_apply,
      Measure.restrict_apply (hE (k n)).compl]
    simp
  have hbf (n : ℕ) : signedFunctional (b n) = ‖U (k n)‖⁻¹ • U (k n) :=
    functional_smul _ _
  have hbfb (n : ℕ) : ‖signedFunctional (b n)‖ ≤ 1 := by
    rw [← (signed_riesz_markov_kakutani (K := K)).2.1 _ (hbreg n), hbnorm]
  obtain ⟨bhat, hbhat, hbext, hbbound⟩ :=
    exists_bounded_extension (fun n => signedFunctional (b n)) 1 hbfb
  let uk : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ) := uhat ∘ Ultrafilter.map k
  let xk : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ) := xj ∘ Ultrafilter.map k
  have huk : Continuous uk := huhat.comp (continuous_map k)
  have hxk : Injective xk := hxji.comp (map_injective k hk.injective)
  have hcorrection := normalize_sub_tendsto_zero (U ∘ k) 1 r
    (fun n => hUbound (k n)) hrpos (hUlim.comp hk.tendsto_atTop)
  have hbfree (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ cofinite) :
      WeakDual.toStrongDual (bhat p) =
        r⁻¹ • (WeakDual.toStrongDual (xk p) - V) := by
    have hufree := hfree (Ultrafilter.map k p) (map_free k hk.injective p hp)
    have hconst : WeakDual.toStrongDual (bhat p) = r⁻¹ • WeakDual.toStrongDual (uk p) := by
      ext g
      have hc := ((ContinuousLinearMap.apply ℝ ℝ g).continuous.tendsto 0).comp hcorrection
      have hcp := hc.mono_left (hp.trans_eq Nat.cofinite_eq_atTop)
      have hu := principal_limit uk huk p g
      have hext (n : ℕ) : uk (pure n) = StrongDual.toWeakDual (U (k n)) := by
        simp only [uk, comp_apply, Ultrafilter.map_pure, huext]
      simp only [hext] at hu
      have ht := hcp.add (hu.const_smul r⁻¹)
      have he (n : ℕ) :
          (‖U (k n)‖⁻¹ • U (k n) - r⁻¹ • U (k n)) g + r⁻¹ * U (k n) g =
            signedFunctional (b n) g := by
        rw [hbf]
        simp
      have ht' : Tendsto (fun n => signedFunctional (b n) g) (p : Filter ℕ)
          (𝓝 (r⁻¹ * uk p g)) := by
        convert ht using 1
        · funext n
          exact (he n).symm
        · simp
      have hb := principal_limit bhat hbhat p g
      simp only [hbext] at hb
      exact tendsto_nhds_unique hb ht'
    rw [hconst]
    exact congrArg (fun z => r⁻¹ • z) hufree
  have hbfi : Set.InjOn bhat {p | (p : Filter ℕ) ≤ cofinite} := by
    intro p hp q hq heq
    apply hxk
    apply WeakDual.toStrongDual.injective
    have he := congrArg (fun z => r • WeakDual.toStrongDual z) heq
    rw [hbfree p hp, hbfree q hq, smul_smul, smul_smul,
      mul_inv_cancel₀ hrpos.ne', one_smul, one_smul] at he
    simpa only [sub_add_cancel] using congrArg (fun z => z + V) he
  have hprincipal : Injective (bhat ∘ (pure : ℕ → Ultrafilter ℕ)) := by
    intro n m heq
    by_contra hnm
    have hbeq : b n = b m :=
      (signed_riesz_markov_kakutani (K := K)).1 _ _ (hbreg n) (hbreg m)
        (StrongDual.toWeakDual.injective (by simpa only [comp_apply, hbext] using heq))
    have hd := hdis (hk.injective.ne hnm)
    have hcover : (univ : Set K) ⊆ (E (k n))ᶜ ∪ (E (k m))ᶜ := by
      intro z _
      by_cases hn : z ∈ E (k n)
      · exact Or.inr (fun hm => Set.disjoint_left.mp hd hn hm)
      · exact Or.inl hn
    have ht : (b n).totalVariation univ = 0 := by
      apply le_antisymm ?_ bot_le
      calc
        _ ≤ (b n).totalVariation ((E (k n))ᶜ ∪ (E (k m))ᶜ) := measure_mono hcover
        _ ≤ (b n).totalVariation (E (k n))ᶜ + (b n).totalVariation (E (k m))ᶜ :=
          measure_union_le _ _
        _ = 0 := by rw [hbcarry n, hbeq, hbcarry m, add_zero]
    have hnormone := hbnorm n
    rw [Measure.real, ht, ENNReal.toReal_zero] at hnormone
    norm_num at hnormone
  obtain ⟨l, hl, hli⟩ := exists_strictMono_injective_reindex bhat hprincipal hbfi
  refine ⟨b ∘ l, E ∘ k ∘ l, bhat ∘ Ultrafilter.map l,
    fun n => hbreg (l n), fun n => hbnorm (l n), fun n => hE (k (l n)),
    ?_, fun n => hbcarry (l n), hbhat.comp (continuous_map l), hli, ?_, ?_⟩
  · intro n m hnm
    exact hdis ((hk.comp hl).injective.ne hnm)
  · intro n
    simp only [comp_apply, Ultrafilter.map_pure, hbext]
  · intro p
    exact hbbound _

/-- The analytic collision premise concerns all regular signed norm-one
sequences carried by disjoint nonempty clopens with positive Jordan mass
at least one half. It requests a collision of distinct free points of
each genuine continuous extension. -/
def SignedClopenCollision : Prop :=
  ∀ (s : ℕ → SignedMeasure K) (W : ℕ → Set K),
    (∀ n, (s n).totalVariation.Regular) →
    (∀ n, (s n).totalVariation.real univ = 1) →
    (∀ n, IsClopen (W n) ∧ (W n).Nonempty) →
    Pairwise (Disjoint on W) →
    (∀ n, (s n).totalVariation (W n)ᶜ = 0) →
    (∀ n, (1 / 2 : ℝ) ≤ (s n).toJordanDecomposition.posPart.real univ) →
    ∀ f : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ), Continuous f →
      (∀ n, f (pure n) = StrongDual.toWeakDual (signedFunctional (s n))) →
      ∃ p q : Ultrafilter ℕ, (p : Filter ℕ) ≤ cofinite ∧
        (q : Filter ℕ) ≤ cofinite ∧ p ≠ q ∧ f p = f q

/-- The full signed clopen collision premise excludes Stone–Čech embeddings
from the entire signed dual unit ball. KPR is proved, not a premise. -/
theorem not_injective_signed_ball_of_collision [ZeroDimensionalSpace K]
    (H : SignedClopenCollision (K := K))
    (h : StoneCech ℕ → WeakDual ℝ C(K, ℝ)) (hh : Continuous h)
    (hball : ∀ p, ‖WeakDual.toStrongDual (h p)‖ ≤ 1) : ¬ Injective h := by
  intro hhi
  obtain ⟨b, E, f, hbreg, hbnorm, hE, hdis, hcarry, hf, hfi, hext, hbound⟩ :=
    exists_normalized_disjoint_embedding h hh hhi hball
  letI : ExtremallyDisconnected (StoneCech ℕ) :=
    CompactT2.Projective.extremallyDisconnected StoneCech.projective
  letI : ExtremallyDisconnected (Ultrafilter ℕ) :=
    extremallyDisconnected_of_homeo (ultrafilterHomeomorph (α := ℕ)).symm
  obtain ⟨c, hc, hgap⟩ :=
    D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation.exists_pos_le_norm_sub
      f hf hfi
  let η : ℝ := min (c / 16) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηone : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηc : 2 * (2 * η) < c := by
    have he : η ≤ c / 16 := min_le_left _ _
    linarith
  obtain ⟨n, W, t, hn, hWdis, ht, s, j, hs, hj, hnj, hsign⟩ :=
    ClopenDisjointization.exists_signed_clopen_disjointization b hbreg hbnorm
      E hE hdis hcarry hη hηone
  let l : ℕ → ℕ := n ∘ j
  let z (k : ℕ) : SignedMeasure K := s • t (j k)
  let f₀ : Ultrafilter ℕ → WeakDual ℝ C(K, ℝ) :=
    fun p => s • f (Ultrafilter.map l p)
  have hf₀ : Continuous f₀ := (hf.comp (continuous_map l)).const_smul s
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsne : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hzg (k : ℕ) : (z k).totalVariation = (t (j k)).totalVariation := (hsign k).1
  have hzreg (k : ℕ) : (z k).totalVariation.Regular := by
    rw [hzg]
    exact (ht (j k)).2.2.2.2.2.2.1
  have hznorm (k : ℕ) : (z k).totalVariation.real univ = 1 := by
    rw [hzg]
    exact (ht (j k)).2.2.2.2.2.2.2.1
  have hzcarry (k : ℕ) : (z k).totalVariation (W (j k))ᶜ = 0 := by
    rw [hzg]
    exact (ht (j k)).2.2.2.2.2.2.2.2.1
  obtain ⟨zhat, hzhat, hzext, hzbound⟩ :=
    exists_bounded_extension (fun k => signedFunctional (z k)) 1 (fun k =>
      (signedFunctional_norm_le _).trans_eq (hznorm k))
  have hgap₀ (p q : Ultrafilter ℕ) (hpq : p ≠ q) :
      c ≤ ‖WeakDual.toStrongDual (f₀ p - f₀ q)‖ := by
    have hne := (map_injective l hnj.injective).ne hpq
    have he := hgap _ _ hne
    simpa only [f₀, ← smul_sub, map_smul, norm_smul, Real.norm_eq_abs,
      hsabs, one_mul] using he
  have hsmall (k : ℕ) :
      ‖WeakDual.toStrongDual (f₀ (pure k) - zhat (pure k))‖ ≤ 2 * η := by
    have herror : (z k - s • b (l k)).totalVariation.real univ < 2 * η := by
      dsimp only [z, l, comp_apply]
      rw [(hsign k).2.2.2]
      have hq := (ht (j k)).2.2.1
      linarith
    have hident : WeakDual.toStrongDual (f₀ (pure k) - zhat (pure k)) =
        -signedFunctional (z k - s • b (l k)) := by
      simp only [f₀, Ultrafilter.map_pure, hext, hzext, map_sub, map_smul,
        StrongDual.toStrongDual_toWeakDual, functional_sub, functional_smul]
      abel
    rw [hident, norm_neg]
    exact (signedFunctional_norm_le _).trans herror.le
  have hzinj : Injective zhat :=
    injective_of_approximation (pure : ℕ → Ultrafilter ℕ) denseRange_pure
      f₀ zhat hf₀ hzhat c (2 * η) hgap₀ hηc hsmall
  obtain ⟨p, q, _, _, hpq, heq⟩ := H z (W ∘ j) hzreg hznorm
    (fun k => ⟨(ht (j k)).1, (ht (j k)).2.1⟩)
    (fun a b hab => hWdis (hj.injective.ne hab)) hzcarry
    (fun k => (hsign k).2.2.1) zhat hzhat hzext
  exact hpq (hzinj heq)

#print axioms exists_normalized_disjoint_embedding
#print axioms not_injective_signed_ball_of_collision

end D5.S3.Topology.Measures.SignedBallReduction
