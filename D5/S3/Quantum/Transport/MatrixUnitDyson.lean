/- GID: D5/S3/Quantum/Transport/MatrixUnitDyson
   generality: G
   mirror-B: D5/B/S3/Quantum/Transport/MatrixUnitDyson
   mirror-E: none(waiver:constructive-matrix-transport)
   anchors: []
   utility: none
   digest: Ordered matrix integrals construct the unique Dyson solution and the unitary transport of the complete moving logical algebra. -/

import D5.S3.Quantum.Transport.MatrixUnitGenerator
import Mathlib

/-!
# Constructive transport of moving logical matrix units

The Dyson series uses the Euclidean operator norm and preserves the order of
matrix multiplication. Its recursive Bochner integrals equal the independent
closed-simplex integrals. Every admissible bound supplies a factorial estimate,
and the resulting series is the unique continuous integral-equation solution.
The computed matrix-unit generator gives a two-sided unitary transport on the
closed positive-length interval. The physical index type may be empty.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Matrix BigOperators Topology Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Transport.MatrixUnitDyson
open D5.S3.Quantum.Recovery.MatrixUnitDecoder
open D5.S3.Quantum.Transport.MatrixUnitGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {d n : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
  [Fintype n] [DecidableEq n]

-- These are actual recursive Bochner integrals. The latest time acts on the
-- left, so multiplication is never commuted.
def orderedTerm (K : ℝ → Matrix n n ℂ) : ℕ → ℝ → Matrix n n ℂ
  | 0, _ => 1
  | m + 1, t => ∫ s in (0 : ℝ)..t, K s * orderedTerm K m s

def dysonSeries (K : ℝ → Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  ∑' m : ℕ, orderedTerm K m t

def orderedSimplex (m : ℕ) (t : ℝ) : Set (Fin m → ℝ) :=
  {τ | (∀ i, 0 ≤ τ i ∧ τ i ≤ t) ∧ ∀ i j, i ≤ j → τ j ≤ τ i}

-- List order fixes K(t₁) ... K(tₘ) independently of orderedTerm.
def simplexTerm (K : ℝ → Matrix n n ℂ) (m : ℕ) (t : ℝ) : Matrix n n ℂ :=
  ∫ τ in orderedSimplex m t, (List.ofFn fun i : Fin m => K (τ i)).prod

-- All ST39.1 clauses, with the actual series fixed before any existential.
def wholeConclusion (F D : ℝ → d → d → Matrix n n ℂ) (T : ℝ) : Prop :=
  let K := fun t => transportGenerator (F t) (D t)
  let P := fun t => unitSupport (F t)
  let Pdot := fun t => supportVelocity (D t)
  let G := dysonSeries K
  (∀ t ∈ Icc 0 T,
    (K t)ᴴ = -K t ∧
    (∀ i j, K t * F t i j - F t i j * K t = D t i j) ∧
    K t * P t - P t * K t = Pdot t) ∧
  (Fintype.card d = 1 → ∀ t ∈ Icc 0 T,
    K t = Pdot t * P t - P t * Pdot t) ∧
  ContinuousOn K (Icc 0 T) ∧
  (∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) ∧
  (∀ m t, t ∈ Icc 0 T →
    IntegrableOn (fun τ : Fin m → ℝ => (List.ofFn fun i : Fin m => K (τ i)).prod)
      (orderedSimplex m t) volume ∧
    orderedTerm K m t = simplexTerm K m t) ∧
  (∀ M : ℝ, 0 ≤ M → (∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) →
    ∀ m t, t ∈ Icc 0 T → ‖orderedTerm K m t‖ ≤ (M * t) ^ m / (m.factorial : ℝ)) ∧
  (∀ t ∈ Icc 0 T,
    Summable (fun m => ‖orderedTerm K m t‖) ∧
    HasSum (fun m => orderedTerm K m t) (G t) ∧
    G t = 1 + ∑' m : ℕ, orderedTerm K (m + 1) t) ∧
  TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, orderedTerm K m t)
    G atTop (Icc 0 T) ∧
  ContinuousOn G (Icc 0 T) ∧
  (∀ t ∈ Icc 0 T, G t = 1 + ∫ s in (0 : ℝ)..t, K s * G s) ∧
  (∀ t ∈ Icc 0 T, HasDerivWithinAt G (K t * G t) (Icc 0 T) t) ∧
  G 0 = 1 ∧
  (∀ t ∈ Icc 0 T, (G t)ᴴ * G t = 1 ∧ G t * (G t)ᴴ = 1) ∧
  (∀ t ∈ Icc 0 T, ∀ i j,
    HasDerivWithinAt (fun s => (G s)ᴴ * F s i j * G s)
      (0 : Matrix n n ℂ) (Icc 0 T) t ∧
    F t i j = G t * F 0 i j * (G t)ᴴ) ∧
  (∀ H : ℝ → Matrix n n ℂ,
    ContinuousOn H (Icc 0 T) →
    (∀ t ∈ Icc 0 T, H t = 1 + ∫ s in (0 : ℝ)..t, K s * H s) →
    ∀ t ∈ Icc 0 T, H t = G t)

/-- The ordered integral construction and the full computed-generator transport. -/
theorem constructive_transport : (∀ (K : ℝ → Matrix n n ℂ) (T : ℝ), 0 ≤ T →
      ContinuousOn K (Icc 0 T) →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) ∧
      (∀ m t, t ∈ Icc 0 T →
        IntegrableOn
          (fun τ : Fin m → ℝ => (List.ofFn fun i : Fin m => K (τ i)).prod)
          (orderedSimplex m t) volume ∧
        orderedTerm K m t = simplexTerm K m t) ∧
      (∀ M : ℝ, 0 ≤ M → (∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) →
        ∀ m t, t ∈ Icc 0 T →
          ‖orderedTerm K m t‖ ≤ (M * t) ^ m / (m.factorial : ℝ)) ∧
      (∀ t ∈ Icc 0 T,
        Summable (fun m => ‖orderedTerm K m t‖) ∧
        HasSum (fun m => orderedTerm K m t) (dysonSeries K t) ∧
        dysonSeries K t = 1 + ∑' m : ℕ, orderedTerm K (m + 1) t) ∧
      TendstoUniformlyOn
        (fun N t => ∑ m ∈ Finset.range N, orderedTerm K m t)
        (dysonSeries K) atTop (Icc 0 T) ∧
      ContinuousOn (dysonSeries K) (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T,
        dysonSeries K t = 1 + ∫ s in (0 : ℝ)..t, K s * dysonSeries K s) ∧
      (∀ t ∈ Icc 0 T,
        HasDerivWithinAt (dysonSeries K) (K t * dysonSeries K t) (Icc 0 T) t) ∧
      dysonSeries K 0 = 1 ∧
      (∀ H : ℝ → Matrix n n ℂ, ContinuousOn H (Icc 0 T) →
        (∀ t ∈ Icc 0 T, H t = 1 + ∫ s in (0 : ℝ)..t, K s * H s) →
        ∀ t ∈ Icc 0 T, H t = dysonSeries K t)) ∧
    (∀ (F D : ℝ → d → d → Matrix n n ℂ) (T : ℝ), 0 < T →
      (∀ i j, ContinuousOn (fun t => F t i j) (Icc 0 T)) →
      (∀ i j, ContinuousOn (fun t => D t i j) (Icc 0 T)) →
      (∀ t ∈ Icc 0 T, ∀ i j a b,
        HasDerivWithinAt (fun u => F u i j a b) (D t i j a b) (Icc 0 T) t) →
      (∀ t ∈ Icc 0 T, ∀ i j k l,
        F t i j * F t k l = if j = k then F t i l else 0) →
      (∀ t ∈ Icc 0 T, ∀ i j, (F t i j)ᴴ = F t j i) →
      wholeConclusion F D T) := by
  classical
  have hactual : ∀ (K : ℝ → Matrix n n ℂ) (T : ℝ), 0 ≤ T →
      ContinuousOn K (Icc 0 T) →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) ∧
      (∀ m t, t ∈ Icc 0 T →
        IntegrableOn
          (fun τ : Fin m → ℝ => (List.ofFn fun i : Fin m => K (τ i)).prod)
          (orderedSimplex m t) volume ∧
        orderedTerm K m t = simplexTerm K m t) ∧
      (∀ M : ℝ, 0 ≤ M → (∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) →
        ∀ m t, t ∈ Icc 0 T →
          ‖orderedTerm K m t‖ ≤ (M * t) ^ m / (m.factorial : ℝ)) ∧
      (∀ t ∈ Icc 0 T,
        Summable (fun m => ‖orderedTerm K m t‖) ∧
        HasSum (fun m => orderedTerm K m t) (dysonSeries K t) ∧
        dysonSeries K t = 1 + ∑' m : ℕ, orderedTerm K (m + 1) t) ∧
      TendstoUniformlyOn
        (fun N t => ∑ m ∈ Finset.range N, orderedTerm K m t)
        (dysonSeries K) atTop (Icc 0 T) ∧
      ContinuousOn (dysonSeries K) (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T,
        dysonSeries K t = 1 + ∫ s in (0 : ℝ)..t, K s * dysonSeries K s) ∧
      (∀ t ∈ Icc 0 T,
        HasDerivWithinAt (dysonSeries K) (K t * dysonSeries K t) (Icc 0 T) t) ∧
      dysonSeries K 0 = 1 ∧
      (∀ H : ℝ → Matrix n n ℂ, ContinuousOn H (Icc 0 T) →
        (∀ t ∈ Icc 0 T, H t = 1 + ∫ s in (0 : ℝ)..t, K s * H s) →
        ∀ t ∈ Icc 0 T, H t = dysonSeries K t) := by
    intro K T hT hK
    have hsimplex : ∀ m t, t ∈ Icc 0 T →
        IntegrableOn
          (fun τ : Fin m → ℝ => (List.ofFn fun i : Fin m => K (τ i)).prod)
          (orderedSimplex m t) volume ∧
        orderedTerm K m t = simplexTerm K m t := by
      -- Closed inequalities, including equality of neighbouring time coordinates.
      have hclosed (m : ℕ) (t : ℝ) : IsClosed (orderedSimplex m t) := by
        unfold orderedSimplex
        simp only [setOf_and, setOf_forall]
        exact (isClosed_iInter fun i =>
          (isClosed_le continuous_const (continuous_apply i)).inter
            (isClosed_le (continuous_apply i) continuous_const)).inter
          (isClosed_iInter fun i => isClosed_iInter fun j =>
            isClosed_iInter fun (_ : i ≤ j) =>
              isClosed_le (continuous_apply j) (continuous_apply i))
      have hcompact (m : ℕ) (t : ℝ) : IsCompact (orderedSimplex m t) := by
        have hbox : IsCompact {τ : Fin m → ℝ | ∀ i, τ i ∈ Icc 0 t} :=
          isCompact_pi_infinite fun _ => isCompact_Icc
        exact hbox.of_isClosed_subset (hclosed m t) (fun τ hτ => hτ.1)
      -- List.prod uses the given monoid order; no commutative product is used.
      have hint (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
          IntegrableOn
            (fun τ : Fin m → ℝ => (List.ofFn fun i : Fin m => K (τ i)).prod)
            (orderedSimplex m t) volume := by
        have hc : ContinuousOn
            (fun τ : Fin m → ℝ => (List.ofFn fun i : Fin m => K (τ i)).prod)
            (orderedSimplex m t) := by
          have hc' := continuousOn_list_prod (List.ofFn (fun i : Fin m => i))
            (f := fun i (τ : Fin m → ℝ) => K (τ i))
            (t := orderedSimplex m t) (fun i _ =>
              hK.comp (continuous_apply i).continuousOn (fun τ hτ =>
                ⟨(hτ.1 i).1, (hτ.1 i).2.trans ht.2⟩))
          simpa only [← List.ofFn_comp'] using hc'
        exact hc.integrableOn_compact (hcompact m t)
      -- Induct simultaneously over all upper times in the original interval.
      have heq : ∀ m t, t ∈ Icc 0 T → orderedTerm K m t = simplexTerm K m t := by
        intro m
        induction m with
        | zero =>
          intro t ht
          have hzero : orderedSimplex 0 t = (univ : Set (Fin 0 → ℝ)) := by
            ext τ
            simp [orderedSimplex]
          rw [orderedTerm, simplexTerm, hzero]
          simp only [List.ofFn_zero, List.prod_nil, Measure.restrict_univ]
          have hv : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (Fin.elim0) :=
            Measure.pi_of_empty _ _
          rw [hv]
          simp [Measure.real]
        | succ m ih =>
          intro t ht
          let e : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin (m + 1) → ℝ) :=
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
          have hmp : MeasurePreserving e
              ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) volume := by
            simpa only [Measure.volume_eq_prod] using
              ((volume_preserving_piFinSuccAbove
                (fun _ : Fin (m + 1) => ℝ) 0).symm
                  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0))
          have he (s : ℝ) (τ : Fin m → ℝ) : e (s, τ) = Fin.cons s τ := by
            simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
              Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero']
          -- This proves the actual section, not a redefinition of the simplex.
          have hsection (s : ℝ) (τ : Fin m → ℝ) :
              Fin.cons s τ ∈ orderedSimplex (m + 1) t ↔
                s ∈ Icc 0 t ∧ τ ∈ orderedSimplex m s := by
            constructor
            · intro h
              refine ⟨?_, ?_⟩
              · change 0 ≤ s ∧ s ≤ t
                simpa only [Fin.cons_zero] using h.1 0
              · refine ⟨?_, ?_⟩
                · intro i
                  refine ⟨?_, ?_⟩
                  · simpa only [Fin.cons_succ] using (h.1 i.succ).1
                  · simpa only [Fin.cons_succ, Fin.cons_zero] using
                      h.2 0 i.succ (Fin.zero_le _)
                · intro i j hij
                  simpa only [Fin.cons_succ] using
                    h.2 i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)
            · rintro ⟨hs, hτ⟩
              refine ⟨?_, ?_⟩
              · intro i
                refine Fin.cases ?_ (fun j => ?_) i
                · change 0 ≤ s ∧ s ≤ t
                  exact hs
                · simpa only [Fin.cons_succ] using
                    (show 0 ≤ τ j ∧ τ j ≤ t from
                      ⟨(hτ.1 j).1, (hτ.1 j).2.trans hs.2⟩)
              · intro i j hij
                cases i using Fin.cases with
                | zero =>
                  cases j using Fin.cases with
                  | zero => exact le_rfl
                  | succ j => simpa only [Fin.cons_succ, Fin.cons_zero] using (hτ.1 j).2
                | succ i =>
                  cases j using Fin.cases with
                  | zero => exact (not_le_of_gt (Fin.succ_pos i) hij).elim
                  | succ j =>
                    simpa only [Fin.cons_succ] using
                      hτ.2 i j (Fin.succ_le_succ_iff.mp hij)
          -- Splitting the first list entry preserves every remaining factor.
          have hproduct (s : ℝ) (τ : Fin m → ℝ) :
              (List.ofFn fun i : Fin (m + 1) => K ((Fin.cons s τ : Fin (m + 1) → ℝ) i)).prod =
                K s * (List.ofFn fun i : Fin m => K (τ i)).prod := by
            simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
          let f : (Fin (m + 1) → ℝ) → Matrix n n ℂ :=
            fun σ => (List.ofFn fun i : Fin (m + 1) => K (σ i)).prod
          let H : (ℝ × (Fin m → ℝ)) → Matrix n n ℂ :=
            fun p => (orderedSimplex (m + 1) t).indicator f (e p)
          have hmeas : MeasurableSet (orderedSimplex (m + 1) t) :=
            (hclosed (m + 1) t).measurableSet
          have hf : Integrable ((orderedSimplex (m + 1) t).indicator f) volume :=
            (hint (m + 1) t ht).integrable_indicator hmeas
          have hH : Integrable H
              ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
            hmp.integrable_comp_of_integrable hf
          have hinner (s : ℝ) :
              (∫ τ : Fin m → ℝ, H (s, τ)) =
                (Icc 0 t).indicator (fun u => K u * simplexTerm K m u) s := by
            by_cases hs : s ∈ Icc 0 t
            · have hfun : (fun τ : Fin m → ℝ => H (s, τ)) =
                  (orderedSimplex m s).indicator
                    (fun τ : Fin m → ℝ => K s *
                      (List.ofFn fun i : Fin m => K (τ i)).prod) := by
                funext τ
                by_cases hτ : τ ∈ orderedSimplex m s
                · have hmem : e (s, τ) ∈ orderedSimplex (m + 1) t := by
                    rw [he]
                    exact (hsection s τ).2 ⟨hs, hτ⟩
                  dsimp [H]
                  have hmem' : Fin.cons s τ ∈ orderedSimplex (m + 1) t := by
                    simpa only [← he] using hmem
                  rw [he]
                  simp only [indicator_of_mem hmem', indicator_of_mem hτ, f]
                  exact hproduct s τ
                · have hnot : e (s, τ) ∉ orderedSimplex (m + 1) t := by
                    rw [he]
                    exact fun h => hτ ((hsection s τ).1 h).2
                  simp only [H, indicator_of_notMem hnot, indicator_of_notMem hτ]
              have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
              rw [hfun, integral_indicator (hclosed m s).measurableSet,
                integral_const_mul_of_integrable (hint m s hsT), indicator_of_mem hs]
              rfl
            · have hfun : (fun τ : Fin m → ℝ => H (s, τ)) = fun _ => 0 := by
                funext τ
                have hnot : e (s, τ) ∉ orderedSimplex (m + 1) t := by
                  rw [he]
                  exact fun h => hs ((hsection s τ).1 h).1
                exact indicator_of_notMem hnot f
              rw [hfun, integral_zero, indicator_of_notMem hs]
          have hrec : simplexTerm K (m + 1) t =
              ∫ s in (0 : ℝ)..t, K s * simplexTerm K m s := by
            calc
              simplexTerm K (m + 1) t =
                  ∫ σ, (orderedSimplex (m + 1) t).indicator f σ :=
                (integral_indicator hmeas).symm
              _ = ∫ p : ℝ × (Fin m → ℝ), H p
                    ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
                (hmp.integral_comp' _).symm
              _ = ∫ s : ℝ, ∫ τ : Fin m → ℝ, H (s, τ) := integral_prod H hH
              _ = ∫ s : ℝ, (Icc 0 t).indicator
                    (fun u => K u * simplexTerm K m u) s := by
                exact integral_congr_ae (Eventually.of_forall hinner)
              _ = ∫ s in Icc (0 : ℝ) t, K s * simplexTerm K m s :=
                integral_indicator measurableSet_Icc
              _ = ∫ s in (0 : ℝ)..t, K s * simplexTerm K m s := by
                rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1]
          rw [hrec, orderedTerm, intervalIntegral.integral_of_le ht.1,
            intervalIntegral.integral_of_le ht.1]
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          change K s * orderedTerm K m s = K s * simplexTerm K m s
          rw [ih s ⟨le_of_lt hs.1, hs.2.trans ht.2⟩]
      intro m t ht
      exact ⟨hint m t ht, heq m t ht⟩
    have hcont : ∀ m, ContinuousOn (orderedTerm K m) (Icc 0 T) := by
      intro m
      induction m with
      | zero => simpa only [orderedTerm] using
          (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : Matrix n n ℂ)) (Icc 0 T))
      | succ m ih =>
        have hint := (hK.mul ih).intervalIntegrable_of_Icc (μ := volume) hT
        have hc := intervalIntegral.continuousOn_primitive_interval' hint
          (show (0 : ℝ) ∈ uIcc 0 T by simpa [uIcc_of_le hT])
        with_reducible_and_instances
          simpa only [orderedTerm, uIcc_of_le hT, Pi.mul_apply] using hc
    have hone : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
      rw [Matrix.cstar_norm_def]
      calc
        ‖((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (1 : Matrix n n ℂ))‖ =
            ‖(1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)‖ := by rw [map_one]
        _ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hfactorial : ∀ M : ℝ, 0 ≤ M →
        (∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) →
        ∀ m t, t ∈ Icc 0 T →
          ‖orderedTerm K m t‖ ≤ (M * t) ^ m / (m.factorial : ℝ) := by
      intro M hM hbound m
      induction m with
      | zero => intro t ht; simpa [orderedTerm] using hone
      | succ m ih =>
        intro t ht
        have hmajor : IntervalIntegrable
            (fun s : ℝ => M * ((M * s) ^ m / (m.factorial : ℝ))) volume 0 t := by
          apply Continuous.intervalIntegrable
          fun_prop
        have hestimate : ‖orderedTerm K (m + 1) t‖ ≤
            ∫ s in (0 : ℝ)..t, M * ((M * s) ^ m / (m.factorial : ℝ)) := by
          apply intervalIntegral.norm_integral_le_of_norm_le ht.1 _ hmajor
          exact Filter.Eventually.of_forall fun s hs => by
            have hsT : s ∈ Icc 0 T := ⟨le_of_lt hs.1, hs.2.trans ht.2⟩
            calc
              ‖K s * orderedTerm K m s‖ ≤ ‖K s‖ * ‖orderedTerm K m s‖ :=
                Matrix.l2_opNorm_mul _ _
              _ ≤ M * ((M * s) ^ m / (m.factorial : ℝ)) :=
                mul_le_mul (hbound s hsT) (ih s hsT) (norm_nonneg _) hM
        have hintegral :
            (∫ s in (0 : ℝ)..t, M * ((M * s) ^ m / (m.factorial : ℝ))) =
              (M * t) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
          have heq : (fun s : ℝ => M * ((M * s) ^ m / (m.factorial : ℝ))) =
              (fun s : ℝ => (M ^ (m + 1) / (m.factorial : ℝ)) * s ^ m) := by
            funext s
            simp only [mul_pow, pow_succ]
            ring
          rw [heq, intervalIntegral.integral_const_mul, integral_pow]
          simp only [zero_pow (Nat.succ_ne_zero m), sub_zero, Nat.factorial_succ,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
          have hfac : (m.factorial : ℝ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero m
          have hm : (m : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hfac, hm]
          <;> ring
        exact hestimate.trans_eq hintegral
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hK
    let M0 : ℝ := max 0 C
    have hM0 : 0 ≤ M0 := le_max_left _ _
    have hbound0 : ∀ t ∈ Icc 0 T, ‖K t‖ ≤ M0 :=
      fun t ht => (hC t ht).trans (le_max_right _ _)
    have hsup : ∀ m t, t ∈ Icc 0 T →
        ‖orderedTerm K m t‖ ≤ (M0 * T) ^ m / (m.factorial : ℝ) := by
      intro m t ht
      exact (hfactorial M0 hM0 hbound0 m t ht).trans <|
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg hM0 ht.1) (mul_le_mul_of_nonneg_left ht.2 hM0) m)
          (by positivity)
    have hsum := Real.summable_pow_div_factorial (M0 * T)
    have habs : ∀ t ∈ Icc 0 T, Summable (fun m => ‖orderedTerm K m t‖) := by
      intro t ht
      exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hsup m t ht) hsum
    have huniform := tendstoUniformlyOn_tsum_nat hsum hsup
    have hGcont := continuousOn_tsum hcont hsum hsup
    have hsplit : ∀ t ∈ Icc 0 T,
        dysonSeries K t = 1 + ∑' m : ℕ, orderedTerm K (m + 1) t := by
      intro t ht
      have hs : Summable (fun m => orderedTerm K m t) := (habs t ht).of_norm
      simpa only [dysonSeries, orderedTerm] using hs.tsum_eq_zero_add
    have heq : ∀ t ∈ Icc 0 T,
        dysonSeries K t = 1 + ∫ s in (0 : ℝ)..t, K s * dysonSeries K s := by
      intro t ht
      have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
      have hint (m : ℕ) : IntervalIntegrable
          (fun s => K s * orderedTerm K m s) volume 0 t :=
        ((hK.mul (hcont m)).mono hsub).intervalIntegrable_of_Icc ht.1
      have hnormbound (m : ℕ) :
          (∫ s in (0 : ℝ)..t, ‖K s * orderedTerm K m s‖) ≤
            (M0 * t) * ((M0 * T) ^ m / (m.factorial : ℝ)) := by
        have hi := intervalIntegral.integral_mono_on ht.1 (hint m).norm
          (continuous_const.intervalIntegrable 0 t)
          (fun s hs => show ‖K s * orderedTerm K m s‖ ≤
            M0 * ((M0 * T) ^ m / (m.factorial : ℝ)) from
            (Matrix.l2_opNorm_mul _ _).trans <|
              mul_le_mul (hbound0 s (hsub hs)) (hsup m s (hsub hs)) (norm_nonneg _) hM0)
        simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
          ← mul_assoc, mul_comm t M0] using hi
      have hnormsum : Summable
          (fun m => ∫ s in (0 : ℝ)..t, ‖K s * orderedTerm K m s‖) :=
        Summable.of_nonneg_of_le
          (fun m => intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => norm_nonneg _))
          hnormbound (hsum.mul_left (M0 * t))
      have hinterchange := MeasureTheory.integral_tsum_of_summable_integral_norm
        (fun m => (hint m).1)
        (show Summable (fun m => ∫ s in Ioc (0 : ℝ) t, ‖K s * orderedTerm K m s‖) by
          simpa only [intervalIntegral.integral_of_le ht.1] using hnormsum)
      have hpointwise :
          (∫ s in Ioc (0 : ℝ) t, ∑' m, K s * orderedTerm K m s) =
            ∫ s in Ioc (0 : ℝ) t, K s * dysonSeries K s := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hsT : s ∈ Icc 0 T := ⟨le_of_lt hs.1, hs.2.trans ht.2⟩
        exact ((habs s hsT).of_norm).tsum_mul_left (K s)
      calc
        dysonSeries K t = 1 + ∑' m : ℕ, orderedTerm K (m + 1) t := hsplit t ht
        _ = 1 + ∑' m : ℕ, ∫ s in Ioc (0 : ℝ) t, K s * orderedTerm K m s := by
          simp only [orderedTerm, intervalIntegral.integral_of_le ht.1]
        _ = 1 + ∫ s in Ioc (0 : ℝ) t, ∑' m, K s * orderedTerm K m s := by
          rw [hinterchange]
        _ = 1 + ∫ s in (0 : ℝ)..t, K s * dysonSeries K s := by
          rw [hpointwise, intervalIntegral.integral_of_le ht.1]
    have hderiv : ∀ t ∈ Icc 0 T,
        HasDerivWithinAt (dysonSeries K) (K t * dysonSeries K t) (Icc 0 T) t := by
      intro t ht
      letI : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
      have hc : ContinuousOn (fun s => K s * dysonSeries K s) (Icc 0 T) := hK.mul hGcont
      have hi : IntervalIntegrable (fun s => K s * dysonSeries K s) volume 0 t :=
        (hc.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1
      have hp : HasDerivWithinAt
          (fun u => ∫ s in (0 : ℝ)..u, K s * dysonSeries K s)
          (K t * dysonSeries K t) (Icc 0 T) t :=
        intervalIntegral.integral_hasDerivWithinAt_right hi
          (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hc t ht)
      have hp' := hp.const_add (1 : Matrix n n ℂ)
      exact hp'.congr_of_mem (fun s hs => heq s hs) ht
    have hzero : dysonSeries K 0 = 1 := by
      unfold dysonSeries
      rw [tsum_eq_single 0]
      · rfl
      · intro m hm
        cases m with
        | zero => exact (hm rfl).elim
        | succ m => simp [orderedTerm]
    have huniqueness : ∀ H : ℝ → Matrix n n ℂ,
        ContinuousOn H (Icc 0 T) →
        (∀ t ∈ Icc 0 T, H t = 1 + ∫ s in (0 : ℝ)..t, K s * H s) →
        ∀ t ∈ Icc 0 T, H t = dysonSeries K t := by
      intro H hH hHeq
      have hHzero : H 0 = 1 := by
        simpa only [intervalIntegral.integral_same, add_zero] using
          hHeq 0 (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
      by_cases hsingleton : T = 0
      · intro t ht
        have htzero : t = 0 := le_antisymm (ht.2.trans_eq hsingleton) ht.1
        simpa only [htzero, hHzero, hzero]
      ·
        have hHderiv : ∀ t ∈ Icc 0 T,
            HasDerivWithinAt H (K t * H t) (Icc 0 T) t := by
          intro t ht
          letI : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
          have hc : ContinuousOn (fun s => K s * H s) (Icc 0 T) := hK.mul hH
          have hi : IntervalIntegrable (fun s => K s * H s) volume 0 t :=
            (hc.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).intervalIntegrable_of_Icc ht.1
          have hp : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, K s * H s)
              (K t * H t) (Icc 0 T) t :=
            intervalIntegral.integral_hasDerivWithinAt_right hi
              (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hc t ht)
          exact (hp.const_add (1 : Matrix n n ℂ)).congr_of_mem
            (fun s hs => hHeq s hs) ht
        have hright : ∀ t ∈ Ico 0 T,
            HasDerivWithinAt (fun s => H s - dysonSeries K s)
              (K t * (H t - dysonSeries K t)) (Ici t) t := by
          intro t ht
          have htcc : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
          have hd := ((hHderiv t htcc).sub (hderiv t htcc)).mono
            (show Icc t T ⊆ Icc 0 T from fun s hs => ⟨ht.1.trans hs.1, hs.2⟩)
          have hlocal : Icc t T =ᶠ[𝓝 t] Ici t := by
            filter_upwards [Iio_mem_nhds ht.2] with s hs
            exact propext ⟨fun h => h.1, fun h => ⟨h, hs.le⟩⟩
          have hmodule :
              (NormedSpace.complexToReal : NormedSpace ℝ (Matrix n n ℂ)).toModule =
                (Matrix.module : Module ℝ (Matrix n n ℂ)) := by
            apply Module.ext'
            intro r A
            change (algebraMap ℝ ℂ r) • A = r • A
            exact algebraMap_smul ℂ r A
          with_reducible_and_instances
            convert! hd.congr_set hlocal using 1
            all_goals first
              | exact hmodule
              | exact hmodule.symm
              | simp only [Pi.sub_apply, mul_sub]
        have hdiffzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
          (f := fun s => H s - dysonSeries K s)
          (f' := fun s => K s * (H s - dysonSeries K s))
          (K := M0) (a := 0) (b := T)
          (hH.sub hGcont) hright
          (show H 0 - dysonSeries K 0 = 0 by rw [hHzero, hzero, sub_self])
          (show ∀ t ∈ Ico 0 T,
            ‖K t * (H t - dysonSeries K t)‖ ≤ M0 * ‖H t - dysonSeries K t‖ from
            fun t ht => (Matrix.l2_opNorm_mul _ _).trans
              (mul_le_mul_of_nonneg_right (hbound0 t ⟨ht.1, ht.2.le⟩) (norm_nonneg _)))
        intro t ht
        exact sub_eq_zero.mp (hdiffzero t ht)
    refine ⟨⟨M0, hM0, hbound0⟩, hsimplex, hfactorial, ?_, huniform,
      hGcont, heq, hderiv, hzero, huniqueness⟩
    intro t ht
    exact ⟨habs t ht, (habs t ht).of_norm.hasSum, hsplit t ht⟩
  refine ⟨hactual, ?_⟩
  intro F D T hT hF hD hentry hmul hstar
  let K : ℝ → Matrix n n ℂ := fun t => transportGenerator (F t) (D t)
  let G : ℝ → Matrix n n ℂ := dysonSeries K
  have hK : ContinuousOn K (Icc 0 T) := by
    change ContinuousOn
      (fun t => (Fintype.card d : ℂ)⁻¹ • (∑ i, ∑ j, D t i j * F t j i) -
        (∑ i, F t i i) * (∑ i, D t i i)) (Icc 0 T)
    have hsumDF : ContinuousOn (fun t => ∑ i, ∑ j, D t i j * F t j i) (Icc 0 T) := by
      exact continuousOn_finsetSum (Finset.univ : Finset d) (fun i _ =>
        continuousOn_finsetSum (Finset.univ : Finset d) (fun j _ => (hD i j).mul (hF j i)))
    have hsumF : ContinuousOn (fun t => ∑ i, F t i i) (Icc 0 T) := by
      exact continuousOn_finsetSum (Finset.univ : Finset d) (fun i _ => hF i i)
    have hsumD : ContinuousOn (fun t => ∑ i, D t i i) (Icc 0 T) := by
      exact continuousOn_finsetSum (Finset.univ : Finset d) (fun i _ => hD i i)
    convert (hsumDF.const_smul (Fintype.card d : ℂ)⁻¹).sub (hsumF.mul hsumD) using 1 <;>
      ext t <;> rfl
  -- Reconstruct the operator-valued derivative from entries, in the same norm.
  have hmatrix : ∀ t ∈ Icc 0 T, ∀ i j,
      HasDerivWithinAt (fun s => F s i j) (D t i j) (Icc 0 T) t := by
    intro t ht i j
    have hp := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ =>
      HasDerivWithinAt.fun_sum (u := Finset.univ) (fun b _ =>
        (hentry t ht i j a b).smul_const (Matrix.single a b (1 : ℂ))))
    have hreconstruct (A : Matrix n n ℂ) :
        (∑ a, ∑ b, A a b • Matrix.single a b (1 : ℂ)) = A := by
      simp only [Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.sum_sum_single A
    simpa only [hreconstruct] using hp
  have hgenerator : ∀ t ∈ Icc 0 T,
      (K t)ᴴ = -K t ∧
      (∀ i j, K t * F t i j - F t i j * K t = D t i j) ∧
      K t * unitSupport (F t) - unitSupport (F t) * K t = supportVelocity (D t) := by
    intro t ht
    have hu : UniqueDiffWithinAt ℝ (Icc 0 T) t := uniqueDiffOn_Icc hT t ht
    have htangent (i j k l : d) :
        D t i j * F t k l + F t i j * D t k l =
          if j = k then D t i l else 0 := by
      have hp := (hmatrix t ht i j).mul (hmatrix t ht k l)
      by_cases hjk : j = k
      · have heq : ∀ s ∈ Icc 0 T, F s i l = F s i j * F s k l := by
          intro s hs
          simpa only [if_pos hjk] using (hmul s hs i j k l).symm
        have hp' := hp.congr_of_mem heq ht
        simpa only [if_pos hjk] using
          (hp'.derivWithin hu).symm.trans ((hmatrix t ht i l).derivWithin hu)
      · have heq : ∀ s ∈ Icc 0 T, (0 : Matrix n n ℂ) = F s i j * F s k l := by
          intro s hs
          simpa only [if_neg hjk] using (hmul s hs i j k l).symm
        have hp' := hp.congr_of_mem heq ht
        simpa only [if_neg hjk] using
          (hp'.derivWithin hu).symm.trans
            ((hasDerivWithinAt_const t (Icc 0 T) (0 : Matrix n n ℂ)).derivWithin hu)
    have hstarTangent (i j : d) : (D t i j)ᴴ = D t j i := by
      have hp := (hmatrix t ht i j).star
      have heq : ∀ s ∈ Icc 0 T, F s j i = (F s i j)ᴴ :=
        fun s hs => (hstar s hs i j).symm
      have hp' := hp.congr_of_mem heq ht
      exact (hp'.derivWithin hu).symm.trans ((hmatrix t ht j i).derivWithin hu)
    exact matrix_unit_transport_generator (F t) (D t)
      (hmul t ht) (hstar t ht) htangent hstarTangent
  have hnormalized : Fintype.card d = 1 → ∀ t ∈ Icc 0 T,
      K t = supportVelocity (D t) * unitSupport (F t) -
        unitSupport (F t) * supportVelocity (D t) := by
    intro hd
    letI : Subsingleton d := Fintype.card_le_one_iff_subsingleton.mp hd.le
    letI : Unique d := uniqueOfSubsingleton (Classical.choice ‹Nonempty d›)
    intro t ht
    simp only [K, transportGenerator, averagedVelocity, unitSupport,
      supportVelocity, Fintype.sum_unique, hd, Nat.cast_one, inv_one, one_smul]
  obtain ⟨hbounded, hsimplex, hfactorial, hseries, huniform, hGcont,
    hGeq, hGderiv, hGzero, huniqueness⟩ := hactual K T hT.le hK
  have hunitary : ∀ t ∈ Icc 0 T, (G t)ᴴ * G t = 1 ∧ G t * (G t)ᴴ = 1 := by
    have hd : ∀ s ∈ Icc 0 T,
        HasDerivWithinAt (fun u => (G u)ᴴ * G u)
          (0 : Matrix n n ℂ) (Icc 0 T) s := by
      intro s hs
      have hp := (hGderiv s hs).star.mul (hGderiv s hs)
      change HasDerivWithinAt (fun u => (G u)ᴴ * G u)
        ((K s * G s)ᴴ * G s + (G s)ᴴ * (K s * G s)) (Icc 0 T) s at hp
      have hz : (K s * G s)ᴴ * G s + (G s)ᴴ * (K s * G s) = 0 := by
        rw [Matrix.conjTranspose_mul, (hgenerator s hs).1]
        noncomm_ring
      simpa only [hz] using hp
    have hf : ∀ s ∈ Icc 0 T,
        fderivWithin ℝ (fun u => (G u)ᴴ * G u) (Icc 0 T) s = 0 := by
      intro s hs
      simpa using (hd s hs).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Icc hT s hs)
    intro t ht
    have hconst := (convex_Icc (0 : ℝ) T).is_const_of_fderivWithin_eq_zero
      (fun s hs => (hd s hs).differentiableWithinAt) hf ht
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
    have hleft : (G t)ᴴ * G t = 1 := by
      simpa only [G, hGzero, Matrix.conjTranspose_one, Matrix.one_mul] using hconst
    exact ⟨hleft, mul_eq_one_comm.mp hleft⟩
  have htransportDeriv : ∀ t ∈ Icc 0 T, ∀ i j,
      HasDerivWithinAt (fun s => (G s)ᴴ * F s i j * G s)
        (0 : Matrix n n ℂ) (Icc 0 T) t := by
    intro t ht i j
    have hp := ((hGderiv t ht).star.mul (hmatrix t ht i j)).mul (hGderiv t ht)
    change HasDerivWithinAt (fun s => (G s)ᴴ * F s i j * G s)
      (((K t * G t)ᴴ * F t i j + (G t)ᴴ * D t i j) * G t +
        ((G t)ᴴ * F t i j) * (K t * G t)) (Icc 0 T) t at hp
    have he :
        ((K t * G t)ᴴ * F t i j + (G t)ᴴ * D t i j) * G t +
          ((G t)ᴴ * F t i j) * (K t * G t) =
        (G t)ᴴ * (D t i j - (K t * F t i j - F t i j * K t)) * G t := by
      rw [Matrix.conjTranspose_mul, (hgenerator t ht).1]
      noncomm_ring
    simpa only [he, (hgenerator t ht).2.1 i j, sub_self,
      Matrix.mul_zero, Matrix.zero_mul] using hp
  have htransport : ∀ t ∈ Icc 0 T, ∀ i j,
      HasDerivWithinAt (fun s => (G s)ᴴ * F s i j * G s)
        (0 : Matrix n n ℂ) (Icc 0 T) t ∧
      F t i j = G t * F 0 i j * (G t)ᴴ := by
    intro t ht i j
    refine ⟨htransportDeriv t ht i j, ?_⟩
    have hf : ∀ s ∈ Icc 0 T,
        fderivWithin ℝ (fun u => (G u)ᴴ * F u i j * G u) (Icc 0 T) s = 0 := by
      intro s hs
      simpa using (htransportDeriv s hs i j).hasFDerivWithinAt.fderivWithin
        (uniqueDiffOn_Icc hT s hs)
    have hconst := (convex_Icc (0 : ℝ) T).is_const_of_fderivWithin_eq_zero
      (fun s hs => (htransportDeriv s hs i j).differentiableWithinAt) hf ht
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
    have hinvariant : (G t)ᴴ * F t i j * G t = F 0 i j := by
      simpa only [G, hGzero, Matrix.conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one] using hconst
    -- Both inverse equations belong to this same G, already constructed above.
    have hright := (hunitary t ht).2
    calc
      F t i j = G t * ((G t)ᴴ * F t i j * G t) * (G t)ᴴ := by
        symm
        calc
          G t * ((G t)ᴴ * F t i j * G t) * (G t)ᴴ =
              (G t * (G t)ᴴ) * F t i j * (G t * (G t)ᴴ) := by
            simp only [Matrix.mul_assoc]
          _ = F t i j := by
            simp only [hright, Matrix.one_mul, Matrix.mul_one]
      _ = G t * F 0 i j * (G t)ᴴ := by rw [hinvariant]
  change
    (∀ t ∈ Icc 0 T,
      (K t)ᴴ = -K t ∧
      (∀ i j, K t * F t i j - F t i j * K t = D t i j) ∧
      K t * unitSupport (F t) - unitSupport (F t) * K t = supportVelocity (D t)) ∧
    (Fintype.card d = 1 → ∀ t ∈ Icc 0 T,
      K t = supportVelocity (D t) * unitSupport (F t) -
        unitSupport (F t) * supportVelocity (D t)) ∧
    ContinuousOn K (Icc 0 T) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) ∧
    (∀ m t, t ∈ Icc 0 T →
      IntegrableOn
        (fun τ : Fin m → ℝ => (List.ofFn fun i : Fin m => K (τ i)).prod)
        (orderedSimplex m t) volume ∧
      orderedTerm K m t = simplexTerm K m t) ∧
    (∀ M : ℝ, 0 ≤ M → (∀ t ∈ Icc 0 T, ‖K t‖ ≤ M) →
      ∀ m t, t ∈ Icc 0 T →
        ‖orderedTerm K m t‖ ≤ (M * t) ^ m / (m.factorial : ℝ)) ∧
    (∀ t ∈ Icc 0 T,
      Summable (fun m => ‖orderedTerm K m t‖) ∧
      HasSum (fun m => orderedTerm K m t) (G t) ∧
      G t = 1 + ∑' m : ℕ, orderedTerm K (m + 1) t) ∧
    TendstoUniformlyOn
      (fun N t => ∑ m ∈ Finset.range N, orderedTerm K m t)
      G atTop (Icc 0 T) ∧
    ContinuousOn G (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, G t = 1 + ∫ s in (0 : ℝ)..t, K s * G s) ∧
    (∀ t ∈ Icc 0 T, HasDerivWithinAt G (K t * G t) (Icc 0 T) t) ∧
    G 0 = 1 ∧
    (∀ t ∈ Icc 0 T, (G t)ᴴ * G t = 1 ∧ G t * (G t)ᴴ = 1) ∧
    (∀ t ∈ Icc 0 T, ∀ i j,
      HasDerivWithinAt (fun s => (G s)ᴴ * F s i j * G s)
        (0 : Matrix n n ℂ) (Icc 0 T) t ∧
      F t i j = G t * F 0 i j * (G t)ᴴ) ∧
    (∀ H : ℝ → Matrix n n ℂ, ContinuousOn H (Icc 0 T) →
      (∀ t ∈ Icc 0 T, H t = 1 + ∫ s in (0 : ℝ)..t, K s * H s) →
      ∀ t ∈ Icc 0 T, H t = G t)
  exact ⟨hgenerator, hnormalized, hK, hbounded, hsimplex, hfactorial,
    hseries, huniform, hGcont, hGeq, hGderiv, hGzero, hunitary,
    htransport, huniqueness⟩

end D5.S3.Quantum.Transport.MatrixUnitDyson
