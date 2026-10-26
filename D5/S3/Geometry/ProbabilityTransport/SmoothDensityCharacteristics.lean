/- GID: D5/S3/Geometry/ProbabilityTransport/SmoothDensityCharacteristics
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/SmoothDensityCharacteristics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual smooth periodic density and characteristic transport -/
import D5.S3.Geometry.ProbabilityTransport.PeriodicDensityCalculus

/-!
# SmoothDensityCharacteristics

Actual smooth periodic density transport on the closed time slab.
-/

set_option maxHeartbeats 2000000

set_option maxHeartbeats 1000000


noncomputable section
open Set Metric
namespace SmoothDensityTransport

/-- Joint C1 regularity of the actual lifted velocity, including slab endpoints.
The representative is used only through the accepted fibre derivative identity.
-/
private theorem characteristicVelocity_contDiffOn {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) :
    ContDiffOn ℝ 1
      (fun p : ℝ × Euclid d => velocity U τ ρ p.1 (quotient d p.2))
      (Icc 0 T ×ˢ univ) := by
  let W : Set (ℝ × Euclid d) := Icc 0 T ×ˢ univ
  let M : ℝ × Euclid d → ℝ :=
    fun p => chemicalPotential U τ ρ p.1 (quotient d p.2)
  have hW : UniqueDiffOn ℝ W := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hM : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) M W := by
    dsimp [M, chemicalPotential]
    exact (h.potential_smooth.comp contDiff_snd).contDiffOn.add
      (contDiffOn_const.mul (h.density_smooth.log
        (fun p hp => (h.positive p.1 hp.1 (quotient d p.2)).ne')))
  have hDM : ContDiffOn ℝ 1 (fderivWithin ℝ M W) W :=
    hM.fderivWithin hW (by simp)
  have hsp (p : ℝ × Euclid d) (hp : p ∈ W) :
      HasFDerivAt
        (fun a : Euclid d => chemicalPotential U τ ρ p.1 (quotient d a))
        ((fderivWithin ℝ M W p).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid d)))
        p.2 := by
    have H := (hM.differentiableOn (by simp) p hp).hasFDerivWithinAt.comp p.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2).hasFDerivWithinAt
      (s := univ) (t := W)
      (fun a (_ : a ∈ (univ : Set (Euclid d))) =>
        show (p.1, a) ∈ W from ⟨hp.1, mem_univ a⟩)
    exact H.hasFDerivAt (by simp)
  have heq (p : ℝ × Euclid d) (hp : p ∈ W) :
      gradient (chemicalPotential U τ ρ p.1) (quotient d p.2) =
        WithLp.toLp 2 (fun i => fderivWithin ℝ M W p (0, basisVector d i)) := by
    rw [gradient_at_quotient (chemicalPotential_smooth h hp.1)]
    unfold liftedGradient
    rw [(hsp p hp).fderiv]
    rfl
  have hright : ContDiffOn ℝ 1
      (fun p : ℝ × Euclid d => WithLp.toLp 2
        (fun i => fderivWithin ℝ M W p (0, basisVector d i))) W := by
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff (n := 1)).comp_contDiffOn (contDiffOn_pi.mpr
        (fun i => hDM.clm_apply contDiffOn_const))
  apply hright.neg.congr
  intro p hp
  change -gradient (chemicalPotential U τ ρ p.1) (quotient d p.2) = _
  rw [heq p hp]

/-- A C1 function on the actual quotient has a globally Lipschitz Euclidean
lift. Compactness bounds the descended derivative, rather than a discontinuous
choice of representatives. This also applies when d = 0. -/
private theorem quotientC1_exists_lipschitz {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Torus d → E}
    (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a))) :
    ∃ K : NNReal, LipschitzWith K (fun a : Euclid d => f (quotient d a)) := by
  let D : Torus d → Euclid d →L[ℝ] E :=
    fun x => fderiv ℝ (fun a : Euclid d => f (quotient d a)) (representative d x)
  have hDq (a : Euclid d) :
      D (quotient d a) = fderiv ℝ (fun a : Euclid d => f (quotient d a)) a := by
    exact fderiv_lift_eq_of_quotient_eq
      (quotient_representative d (quotient d a))
  have hDc : Continuous D := by
    apply continuous_of_lift
    simpa only [hDq] using hf.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hDc.continuousOn
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by simp)) ?_⟩
  intro a
  have H : ‖fderiv ℝ (fun a : Euclid d => f (quotient d a)) a‖ ≤ (K : ℝ) := by
    rw [← hDq a]
    exact (hC (quotient d a) (mem_univ _)).trans (le_max_left _ _)
  exact_mod_cast H

/-- Uniform speed and spatial Lipschitz constants on the closed slab.
Bounds are taken on a compact cell with a continuous quotient map. -/
private theorem characteristicVelocity_uniformBounds {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) :
    ∃ L K : NNReal,
      (∀ t ∈ Icc 0 T, ∀ a : Euclid d,
        ‖velocity U τ ρ t (quotient d a)‖ ≤ (L : ℝ)) ∧
      (∀ t ∈ Icc 0 T,
        LipschitzWith K (fun a : Euclid d => velocity U τ ρ t (quotient d a))) := by
  let W : Set (ℝ × Euclid d) := Icc 0 T ×ˢ univ
  let F : ℝ × Euclid d → Euclid d :=
    fun p => velocity U τ ρ p.1 (quotient d p.2)
  let D : ℝ × Euclid d → Euclid d →L[ℝ] Euclid d := fun p =>
    (fderivWithin ℝ F W p).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid d))
  have hW : UniqueDiffOn ℝ W := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hF : ContDiffOn ℝ 1 F W := characteristicVelocity_contDiffOn h hT
  have hD : ContinuousOn D W :=
    (hF.continuousOn_fderivWithin hW (by simp)).clm_comp continuousOn_const
  have hsp (p : ℝ × Euclid d) (hp : p ∈ W) :
      fderiv ℝ (fun a : Euclid d => velocity U τ ρ p.1 (quotient d a)) p.2 = D p := by
    have H := (hF.differentiableOn (by simp) p hp).hasFDerivWithinAt.comp p.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2).hasFDerivWithinAt
      (s := univ) (t := W)
      (fun a (_ : a ∈ (univ : Set (Euclid d))) =>
        show (p.1, a) ∈ W from ⟨hp.1, mem_univ a⟩)
    exact (H.hasFDerivAt (by simp)).fderiv
  let P : (Fin d → ℝ) ≃L[ℝ] Euclid d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let C : Set (ℝ × (Fin d → ℝ)) := Icc 0 T ×ˢ Icc 0 1
  let J : ℝ × (Fin d → ℝ) → ℝ × Euclid d := fun p => (p.1, P p.2)
  have hC : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hJ : Continuous J := continuous_fst.prodMk (P.continuous.comp continuous_snd)
  have hJC : MapsTo J C W := fun p hp => ⟨hp.1, mem_univ _⟩
  obtain ⟨L₀ : ℝ, hL₀⟩ := hC.exists_bound_of_continuousOn
    (hF.continuousOn.comp hJ.continuousOn hJC)
  obtain ⟨K₀ : ℝ, hK₀⟩ := hC.exists_bound_of_continuousOn
    (hD.comp hJ.continuousOn hJC)
  let L : NNReal := ⟨max L₀ 0, le_max_right _ _⟩
  let K : NNReal := ⟨max K₀ 0, le_max_right _ _⟩
  have hcell (a : Euclid d) :
      (fun i => (AddCircle.equivIoc 1 0 ((quotient d a) i)).1) ∈
        Icc (0 : Fin d → ℝ) 1 := by
    constructor
    · intro i
      exact (AddCircle.equivIoc 1 0 ((quotient d a) i)).2.1.le
    · intro i
      simpa using (AddCircle.equivIoc 1 0 ((quotient d a) i)).2.2
  refine ⟨L, K, ?_, ?_⟩
  · intro t ht a
    let z : Fin d → ℝ := fun i => (AddCircle.equivIoc 1 0 ((quotient d a) i)).1
    have H := hL₀ (t, z) ⟨ht, hcell a⟩
    change ‖velocity U τ ρ t
      (quotient d (representative d (quotient d a)))‖ ≤ L₀ at H
    rw [quotient_representative] at H
    exact H.trans (le_max_left _ _)
  · intro t ht
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact (smooth_gradient_lift (chemicalPotential_smooth h ht)).neg.differentiable (by simp)
    · intro a
      let z : Fin d → ℝ := fun i => (AddCircle.equivIoc 1 0 ((quotient d a) i)).1
      have H := hK₀ (t, z) ⟨ht, hcell a⟩
      change ‖D (t, P z)‖ ≤ K₀ at H
      rw [← hsp (t, P z) ⟨ht, mem_univ _⟩] at H
      have heq := fderiv_lift_eq_of_quotient_eq (f := velocity U τ ρ t)
        (a := P z) (b := a) (quotient_representative d (quotient d a))
      rw [heq] at H
      have H' : ‖fderiv ℝ
          (fun a : Euclid d => velocity U τ ρ t (quotient d a)) a‖ ≤ (K : ℝ) :=
        H.trans (le_max_left _ _)
      exact_mod_cast H'

/-- The actual characteristic has a solution on the entire closed time slab
from any starting time and point. Uniform periodic bounds let the existing
Picard-Lindelof theorem cover the slab in one application.
This theorem does not assert differentiable dependence on the initial data. -/
private theorem characteristic_exists_on_entire_slab {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (r : ℝ) (hr : r ∈ Icc 0 T) (a : Euclid d) :
    ∃ γ : ℝ → Euclid d, γ r = a ∧
      ∀ t ∈ Icc 0 T,
        HasDerivWithinAt γ
          (velocity U τ ρ t (quotient d (γ t))) (Icc 0 T) t := by
  obtain ⟨L, K, hL, hK⟩ := characteristicVelocity_uniformBounds h hT
  let A : NNReal := ⟨(L : ℝ) * T + 1, by positivity⟩
  have htime (x : Euclid d) :
      ContinuousOn (fun t => velocity U τ ρ t (quotient d x)) (Icc 0 T) := by
    exact (characteristicVelocity_contDiffOn h hT).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ x⟩)
  have hPL : IsPicardLindelof
      (fun t x => velocity U τ ρ t (quotient d x))
      (⟨r, hr⟩ : Icc 0 T) a A 0 L K := by
    refine ⟨(fun t ht => (hK t ht).lipschitzOnWith),
      (fun x _ => htime x), (fun t ht x _ => hL t ht x), ?_⟩
    change (L : ℝ) * max (T - r) (r - 0) ≤ (L : ℝ) * T + 1 - 0
    have hm : max (T - r) (r - 0) ≤ T :=
      max_le (by linarith [hr.1]) (by linarith [hr.2])
    have H := mul_le_mul_of_nonneg_left hm L.coe_nonneg
    linarith
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Two solutions of the actual equation agreeing at any slab time agree
through both endpoints. The two one-sided uniqueness applications are needed
when the common starting time is itself an endpoint. -/
private theorem characteristic_unique_on_slab {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    {r : ℝ} (hr : r ∈ Icc 0 T) {f g : ℝ → Euclid d}
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f
      (velocity U τ ρ t (quotient d (f t))) (Icc 0 T) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivWithinAt g
      (velocity U τ ρ t (quotient d (g t))) (Icc 0 T) t)
    (heq : f r = g r) : EqOn f g (Icc 0 T) := by
  obtain ⟨L, K, hL, hK⟩ := characteristicVelocity_uniformBounds h hT
  have hfc : ContinuousOn f (Icc 0 T) := HasDerivWithinAt.continuousOn hf
  have hgc : ContinuousOn g (Icc 0 T) := HasDerivWithinAt.continuousOn hg
  have hright : EqOn f g (Icc r T) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun t x => velocity U τ ρ t (quotient d x))
      (s := fun _ => univ) (K := K)
    · intro t ht
      exact (hK t ⟨hr.1.trans ht.1, ht.2.le⟩).lipschitzOnWith
    · exact hfc.mono (Icc_subset_Icc hr.1 le_rfl)
    · intro t ht
      exact (hf t ⟨hr.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hr.1.trans ht.1, ht.2⟩)
    · exact fun _ _ => mem_univ _
    · exact hgc.mono (Icc_subset_Icc hr.1 le_rfl)
    · intro t ht
      exact (hg t ⟨hr.1.trans ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hr.1.trans ht.1, ht.2⟩)
    · exact fun _ _ => mem_univ _
    · exact heq
  have hleft : EqOn f g (Icc 0 r) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun t x => velocity U τ ρ t (quotient d x))
      (s := fun _ => univ) (K := K)
    · intro t ht
      exact (hK t ⟨ht.1.le, ht.2.trans hr.2⟩).lipschitzOnWith
    · exact hfc.mono (Icc_subset_Icc le_rfl hr.2)
    · intro t ht
      exact (hf t ⟨ht.1.le, ht.2.trans hr.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans hr.2⟩)
    · exact fun _ _ => mem_univ _
    · exact hgc.mono (Icc_subset_Icc le_rfl hr.2)
    · intro t ht
      exact (hg t ⟨ht.1.le, ht.2.trans hr.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2.trans hr.2⟩)
    · exact fun _ _ => mem_univ _
    · exact heq
  intro t ht
  rcases le_total t r with htr | hrt
  · exact hleft ⟨ht.1, htr⟩
  · exact hright ⟨hrt, ht.2⟩

/-- Actual data, selected from the preceding existence proof, not a Prop target.
Outside the closed slab the selected curve has no asserted properties. -/
def characteristic {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (r : Icc 0 T) (a : Euclid d) : ℝ → Euclid d :=
  Classical.choose (characteristic_exists_on_entire_slab h hT r r.2 a)

theorem characteristic_initial {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (r : Icc 0 T) (a : Euclid d) : characteristic h hT r a r = a :=
  (Classical.choose_spec (characteristic_exists_on_entire_slab h hT r r.2 a)).1

theorem characteristic_ode {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (r : Icc 0 T) (a : Euclid d) (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (characteristic h hT r a)
      (velocity U τ ρ t (quotient d (characteristic h hT r a t))) (Icc 0 T) t :=
  (Classical.choose_spec (characteristic_exists_on_entire_slab h hT r r.2 a)).2 t ht

/-- An ambient two-time function for stating within-slab regularity without
giving the time subtype a fictitious vector-space structure. Its values for
starting times outside the slab are immaterial to ContDiffOn on the slab. -/
def characteristicOperator {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (r s : ℝ) (a : Euclid d) : Euclid d :=
  if hr : r ∈ Icc 0 T then characteristic h hT ⟨r, hr⟩ a s else a

theorem characteristicOperator_of_mem {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (r : ℝ) (hr : r ∈ Icc 0 T) (s : ℝ) (a : Euclid d) :
    characteristicOperator h hT r s a = characteristic h hT ⟨r, hr⟩ a s := by
  simp only [characteristicOperator, dif_pos hr]

/-- Descent on the actual quotient fibres, proved without selecting an integer
representative of a fibre difference. -/
private theorem characteristic_quotient_fibre {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) (r t : Icc 0 T)
    (a b : Euclid d) (hab : quotient d a = quotient d b) :
    quotient d (characteristic h hT r a t) =
      quotient d (characteristic h hT r b t) := by
  have hshift (c : Euclid d) : quotient d (c + (a - b)) = quotient d c := by
    rw [quotient_add, quotient_sub, hab, sub_self, add_zero]
  have hg : ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun s => characteristic h hT r b s + (a - b))
        (velocity U τ ρ s (quotient d (characteristic h hT r b s + (a - b))))
        (Icc 0 T) s := by
    intro s hs
    simpa only [hshift] using (characteristic_ode h hT r b s hs).add_const (a - b)
  have hi : characteristic h hT r a r = characteristic h hT r b r + (a - b) := by
    rw [characteristic_initial, characteristic_initial]
    abel
  have H := characteristic_unique_on_slab h hT r.2
    (characteristic_ode h hT r a) hg hi
  calc
    quotient d (characteristic h hT r a t) =
        quotient d (characteristic h hT r b t + (a - b)) := congrArg (quotient d) (H t.2)
    _ = quotient d (characteristic h hT r b t) := hshift _

theorem characteristicOperator_quotient_representative {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (r s : ℝ) (hr : r ∈ Icc 0 T) (hs : s ∈ Icc 0 T) (a : Euclid d) :
    quotient d (characteristicOperator h hT r s (representative d (quotient d a))) =
      quotient d (characteristicOperator h hT r s a) := by
  rw [characteristicOperator_of_mem h hT r hr,
    characteristicOperator_of_mem h hT r hr]
  exact characteristic_quotient_fibre h hT ⟨r, hr⟩ ⟨s, hs⟩
    (representative d (quotient d a)) a (quotient_representative d (quotient d a))

end SmoothDensityTransport

noncomputable section
open Set Metric
namespace SmoothDensityTransport

/-- A uniform time Lipschitz bound for the actual representative-defined
velocity. Only relative regularity on the closed slab is used. -/
private theorem characteristicVelocity_time_lipschitz {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
      ‖velocity U τ ρ t (quotient d a) - velocity U τ ρ s (quotient d a)‖ ≤
        K * |t - s| := by
  let W : Set (ℝ × Euclid d) := Icc 0 T ×ˢ univ
  let F : ℝ × Euclid d → Euclid d :=
    fun p => velocity U τ ρ p.1 (quotient d p.2)
  let D : ℝ × Euclid d → ℝ →L[ℝ] Euclid d := fun p =>
    (fderivWithin ℝ F W p).comp (ContinuousLinearMap.inl ℝ ℝ (Euclid d))
  have hW : UniqueDiffOn ℝ W := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hF : ContDiffOn ℝ 1 F W := characteristicVelocity_contDiffOn h hT
  have hD : ContinuousOn D W :=
    (hF.continuousOn_fderivWithin hW (by simp)).clm_comp continuousOn_const
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) (a : Euclid d) :
      HasFDerivWithinAt (fun s => F (s, a)) (D (t, a)) (Icc 0 T) t := by
    exact (hF.differentiableOn (by simp) (t,a) ⟨ht, mem_univ _⟩).hasFDerivWithinAt.comp t (s := Icc 0 T) (t := W)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t a).hasFDerivWithinAt
      (fun s hs => ⟨hs, mem_univ _⟩)
  have heq (t : ℝ) (ht : t ∈ Icc 0 T) (a : Euclid d) :
      fderivWithin ℝ (fun s => F (s, a)) (Icc 0 T) t = D (t,a) :=
    (htime t ht a).fderivWithin ((uniqueDiffOn_Icc hT) t ht)
  let P : (Fin d → ℝ) ≃L[ℝ] Euclid d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let C : Set (ℝ × (Fin d → ℝ)) := Icc 0 T ×ˢ Icc 0 1
  let J : ℝ × (Fin d → ℝ) → ℝ × Euclid d := fun p => (p.1, P p.2)
  have hC : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hJ : Continuous J := continuous_fst.prodMk (P.continuous.comp continuous_snd)
  have hJC : MapsTo J C W := fun p hp => ⟨hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hD.comp hJ.continuousOn hJC)
  let K : ℝ := max M 0
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (a : Euclid d) :
      ‖fderivWithin ℝ (fun s => F (s,a)) (Icc 0 T) t‖ ≤ K := by
    let z : Fin d → ℝ := fun i => (AddCircle.equivIoc 1 0 ((quotient d a) i)).1
    have hz : z ∈ Icc (0 : Fin d → ℝ) 1 := by
      constructor
      · intro i; exact (AddCircle.equivIoc 1 0 ((quotient d a) i)).2.1.le
      · intro i; simpa using (AddCircle.equivIoc 1 0 ((quotient d a) i)).2.2
    have H := hM (t,z) ⟨ht,hz⟩
    change ‖D (t, representative d (quotient d a))‖ ≤ M at H
    rw [← heq t ht] at H
    have hfibre : (fun s => F (s, representative d (quotient d a))) =
        fun s => F (s,a) := by
      funext s
      simp only [F, quotient_representative]
    rw [hfibre] at H
    exact H.trans (le_max_left _ _)
  refine ⟨K, le_max_right _ _, ?_⟩
  intro s hs t ht a
  have H := Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (fun v hv => (htime v hv a).differentiableWithinAt)
    (hbound · · a) (convex_Icc 0 T) hs ht
  simpa only [Real.norm_eq_abs] using H

/-- All constants used by the finite Euler argument are derived before any
mesh is chosen. No flow or density transport assumption occurs here. -/
private theorem actual_smooth_slab_constants {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ) (hT : 0 < T)
    (f : Torus d → ℝ)
    (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a))) :
    ∃ B L K C : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ 0 ≤ K ∧ 0 ≤ C ∧
      (∀ t ∈ Icc 0 T, ∀ a : Euclid d, ‖velocity U τ ρ t (quotient d a)‖ ≤ B) ∧
      (∀ t ∈ Icc 0 T, ∀ a : Euclid d,
        ‖fderiv ℝ (fun z => velocity U τ ρ t (quotient d z)) a‖ ≤ L) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
        ‖velocity U τ ρ t (quotient d a) - velocity U τ ρ s (quotient d a)‖ ≤ K * |t-s|) ∧
      (∀ a : Euclid d, ‖fderiv ℝ (fun z => f (quotient d z)) a‖ ≤ C) := by
  obtain ⟨B,L,hB,hL⟩ := characteristicVelocity_uniformBounds h hT
  obtain ⟨K,hK,hKt⟩ := characteristicVelocity_time_lipschitz h hT
  obtain ⟨C,hC⟩ := quotientC1_exists_lipschitz hf
  refine ⟨B,L,K,C,B.coe_nonneg,L.coe_nonneg,hK,C.coe_nonneg,hB,?_,hKt,?_⟩
  · intro t ht a
    exact norm_fderiv_le_of_lipschitz ℝ (hL t ht)
  · intro a
    exact norm_fderiv_le_of_lipschitz ℝ hC

/-- The same constants exist on every nonnegative slab, including T = 0.
The degenerate time interval needs no uniqueness of relative time derivatives. -/
theorem actual_smooth_slab_constants_including_zero {d : ℕ} {T τ : ℝ}
    {U : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : SmoothFP d T τ U ρ)
    (f : Torus d → ℝ)
    (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a))) :
    ∃ B L K C : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ 0 ≤ K ∧ 0 ≤ C ∧
      (∀ t ∈ Icc 0 T, ∀ a : Euclid d, ‖velocity U τ ρ t (quotient d a)‖ ≤ B) ∧
      (∀ t ∈ Icc 0 T, ∀ a : Euclid d,
        ‖fderiv ℝ (fun z => velocity U τ ρ t (quotient d z)) a‖ ≤ L) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ a : Euclid d,
        ‖velocity U τ ρ t (quotient d a) - velocity U τ ρ s (quotient d a)‖ ≤ K * |t-s|) ∧
      (∀ a : Euclid d, ‖fderiv ℝ (fun z => f (quotient d z)) a‖ ≤ C) := by
  by_cases hT : 0 < T
  · exact actual_smooth_slab_constants h hT f hf
  have hT0 : T = 0 := le_antisymm (le_of_not_gt hT) h.time_nonnegative
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl,h.time_nonnegative⟩
  have ht0 (t : ℝ) (ht : t ∈ Icc 0 T) : t = 0 := by
    rw [hT0] at ht
    exact le_antisymm ht.2 ht.1
  have hb : ContDiff ℝ 1 (fun a : Euclid d => velocity U τ ρ 0 (quotient d a)) :=
    ((smooth_gradient_lift (chemicalPotential_smooth h h0)).neg).of_le (by simp)
  have hbc : Continuous (velocity U τ ρ 0) := continuous_of_lift hb.continuous
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hbc.continuousOn
  obtain ⟨L,hL⟩ := quotientC1_exists_lipschitz hb
  obtain ⟨C,hC⟩ := quotientC1_exists_lipschitz hf
  refine ⟨max B 0,L,0,C,le_max_right _ _,L.coe_nonneg,le_rfl,C.coe_nonneg,?_,?_,?_,?_⟩
  · intro t ht a
    rw [ht0 t ht]
    exact (hB (quotient d a) (mem_univ _)).trans (le_max_left _ _)
  · intro t ht a
    rw [ht0 t ht]
    exact norm_fderiv_le_of_lipschitz ℝ hL
  · intro s hs t ht a
    rw [ht0 s hs,ht0 t ht]
    simp
  · intro a
    exact norm_fderiv_le_of_lipschitz ℝ hC

end SmoothDensityTransport
