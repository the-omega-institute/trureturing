/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteBoundaryCover
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteBoundaryCover
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactExceptional]
   utility: none
   digest: A differentiable six-real-dimensional cover of compact boundary observations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteBoundaryCover
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactExceptional

/-! The compact six-site boundary observations have a finite cover by real-differentiable
images of open subsets of six-dimensional real space. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteBoundaryCover

open Set PeriodicMPSProjectiveCoordinates PeriodicMPSSixSiteCompactSource
  PeriodicMPSSixSiteCoordinates PeriodicMPSSixSiteTraceChart
open PeriodicMPSSixSiteCompactExceptional (exceptional_amplitude)
open PeriodicMPSSixSiteMarginal (gram necklaceTable)
open scoped ComplexConjugate

open private patch projective_patch differentiable_patch twoTail complexCoordinates
  complexCoordinates_surjective differentiable_complexCoordinates
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteBoundaryCover
open private amplitude_zero from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactSource
open private shear_ne_zero swappedIndex_involutive
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCompactExceptional

noncomputable section

/-- Compact lifts whose invariant ray has vanishing first trace-square or vanishing cubic. -/
def boundary : Set Ambient :=
  {x | x ∈ source ∧
    ∃ q : Fin 6 → ℂ, x.1 = projector q ∧ (q 0 = 0 ∨ amplitude q = 0)}

/-- The vacuum roots indexing the exceptional charts in either orientation. -/
abbrev VacuumRoot := {d : ℂ // vacuum d = 0}

private def vacuumPolynomial : Polynomial ℂ :=
  Polynomial.C 1 - Polynomial.C 6 * Polynomial.X + Polynomial.C 9 * Polynomial.X ^ 2 -
    Polynomial.C 2 * Polynomial.X ^ 3

private theorem vacuumPolynomial_eval (d : ℂ) : vacuumPolynomial.eval d = vacuum d := by
  simp [vacuumPolynomial, vacuum]

private theorem vacuumPolynomial_ne_zero : vacuumPolynomial ≠ 0 := by
  intro h
  have he := vacuumPolynomial_eval 0
  rw [h] at he
  norm_num [vacuum] at he

instance : Finite VacuumRoot := by
  have he : {d : ℂ | vacuum d = 0} = {d : ℂ | Polynomial.IsRoot vacuumPolynomial d} := by
    ext d
    change vacuum d = 0 ↔ vacuumPolynomial.eval d = 0
    rw [vacuumPolynomial_eval]
  have h : Set.Finite {d : ℂ | vacuum d = 0} := by
    rw [he]
    exact Polynomial.finite_setOfPred_isRoot vacuumPolynomial_ne_zero
  exact h.to_subtype

/-- Four ordinary projective patches and three normal patches per vacuum root and orientation. -/
abbrev BoundaryFamily := Fin 4 ⊕ (Bool × VacuumRoot × Fin 3)

private def traceZeroCoordinates (v : Fin 4 → ℂ) : Fin 6 → ℂ :=
  ![0, 0, v 0, v 1, v 2, v 3]

private theorem traceZeroCoordinates_smul (c : ℂ) (v : Fin 4 → ℂ) :
    traceZeroCoordinates (c • v) = c • traceZeroCoordinates v := by
  funext i
  fin_cases i <;> simp [traceZeroCoordinates, Pi.smul_apply, smul_eq_mul]

private def exceptionalAmplitude (flipped : Bool) (d s : ℂ) (z : Fin 3 → ℂ) :
    Fin 14 → ℂ :=
  let a := shear s (lift d 0 0 z)
  if flipped then a ∘ swappedIndex else a

private theorem exceptionalAmplitude_smul (flipped : Bool) (d s c : ℂ) (z : Fin 3 → ℂ) :
    exceptionalAmplitude flipped d s (c • z) = c • exceptionalAmplitude flipped d s z := by
  cases flipped
  · exact (congrArg (shear s) (lift_smul d 0 0 c z)).trans (shear_smul s c _)
  · funext i
    change shear s (lift d 0 0 (c • z)) (swappedIndex i) =
      (c • shear s (lift d 0 0 z)) (swappedIndex i)
    rw [lift_smul, shear_smul]

private theorem exceptionalAmplitude_ne_zero (flipped : Bool) {d : ℂ} (hd : vacuum d = 0)
    (s : ℂ) {z : Fin 3 → ℂ} (hz : z ≠ 0) : exceptionalAmplitude flipped d s z ≠ 0 := by
  have ha := shear_ne_zero s (lift_ne_zero_of_vacuum hd hz)
  cases flipped
  · exact ha
  · intro h
    apply ha
    funext i
    have hi := congrFun h (swappedIndex i)
    change shear s (lift d 0 0 z) (swappedIndex (swappedIndex i)) = 0 at hi
    change shear s (lift d 0 0 z) i = 0
    simpa only [swappedIndex_involutive i] using hi

/-- Amplitude representatives on the three-complex-dimensional boundary charts. -/
def boundaryAmplitude : BoundaryFamily → (Fin 3 → ℂ) → Fin 14 → ℂ
  | .inl j, u => amplitude (traceZeroCoordinates (patch j u))
  | .inr (flipped, d, j), u => exceptionalAmplitude flipped d.val (u 0) (patch j (twoTail u))

private theorem exceptional_patch_ne_zero (flipped : Bool) (d : VacuumRoot)
    (j : Fin 3) (u : Fin 3 → ℂ) : boundaryAmplitude (.inr (flipped, d, j)) u ≠ 0 := by
  apply exceptionalAmplitude_ne_zero flipped d.property
  intro h
  have hzero : patch j (twoTail u) j = 0 := congrFun h j
  have hone : patch j (twoTail u) j = 1 := by simp [patch]
  exact one_ne_zero (hone.symm.trans hzero)

private theorem second_coordinate_zero {x : Ambient} (hx : x ∈ source) {q : Fin 6 → ℂ}
    (hq : x.1 = projector q) (hn : q ≠ 0) (h0 : q 0 = 0) : q 1 = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 6, q c ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  have hcol : x.1 0 c = 0 := by
    rw [hq]
    simp [projector, outer, h0, Matrix.smul_apply]
  have hsq := source_quadric_column hx c
  rw [hcol, zero_mul] at hsq
  have h1 := sq_eq_zero_iff.mp hsq
  have hr := projector_ratio q 1 c hc
  rw [← hq, h1, zero_div] at hr
  exact (div_eq_zero_iff.mp hr.symm).resolve_right hc

private theorem ordinary_amplitude_cover {x : Ambient} (hx : x ∈ source) {q : Fin 6 → ℂ}
    (hq : x.1 = projector q) (h0 : q 0 = 0) (ha : amplitude q ≠ 0) :
    ∃ (j : Fin 4) (u : Fin 3 → ℂ),
      boundaryAmplitude (.inl j) u ≠ 0 ∧ x.2 = projector (boundaryAmplitude (.inl j) u) := by
  have hn : q ≠ 0 := fun h => ha ((congrArg amplitude h).trans amplitude_zero)
  have h1 := second_coordinate_zero hx hq hn h0
  let v : Fin 4 → ℂ := ![q 2, q 3, q 4, q 5]
  have hrep : q = traceZeroCoordinates v := by
    funext i
    fin_cases i <;> first | exact h0 | exact h1 | rfl
  have hv : v ≠ 0 := by
    intro h
    apply hn
    rw [hrep, h]
    funext i
    fin_cases i <;> rfl
  obtain ⟨j, u, c, hc, hpatch⟩ := projective_patch hv
  have hscale : amplitude q = c ^ 3 • boundaryAmplitude (.inl j) u := by
    change amplitude q = c ^ 3 • amplitude (traceZeroCoordinates (patch j u))
    rw [hrep, hpatch, traceZeroCoordinates_smul, amplitude_scale]
  have hnonzero : boundaryAmplitude (.inl j) u ≠ 0 := by
    intro h
    exact ha (by rw [hscale, h, smul_zero])
  refine ⟨j, u, hnonzero, ?_⟩
  calc
    x.2 = projector (amplitude q) :=
      congrArg Prod.snd (eq_graphPoint_of_amplitude_ne_zero hx hq ha)
    _ = _ := by rw [hscale, projector_scale _ (pow_ne_zero 3 hc)]

/-- Each boundary lift has the amplitude projector of a nonvanishing chart representative. -/
theorem boundary_amplitude_cover {x : Ambient} (hx : x ∈ boundary) :
    ∃ (i : BoundaryFamily) (u : Fin 3 → ℂ),
      boundaryAmplitude i u ≠ 0 ∧ x.2 = projector (boundaryAmplitude i u) := by
  obtain ⟨hsource, q, hq, hb⟩ := hx
  by_cases ha : amplitude q = 0
  · obtain ⟨s, d, z, hd, hz, hproj⟩ := exceptional_amplitude hsource hq ha
    have horiented : ∃ flipped : Bool, x.2 = projector (exceptionalAmplitude flipped d s z) := by
      rcases hproj with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨flipped, hproj⟩ := horiented
    obtain ⟨j, w, c, hc, hpatch⟩ := projective_patch hz
    let r : VacuumRoot := ⟨d, hd⟩
    let u : Fin 3 → ℂ := ![s, w 0, w 1]
    have hs : u 0 = s := rfl
    have hu : twoTail u = w := by
      funext k
      fin_cases k <;> rfl
    have hscale : exceptionalAmplitude flipped d s z =
        c • boundaryAmplitude (.inr (flipped, r, j)) u := by
      change exceptionalAmplitude flipped d s z =
        c • exceptionalAmplitude flipped d (u 0) (patch j (twoTail u))
      rw [hs, hu, hpatch, exceptionalAmplitude_smul]
    refine ⟨.inr (flipped, r, j), u, exceptional_patch_ne_zero flipped r j u, ?_⟩
    rw [hproj, hscale, projector_scale _ hc]
  · obtain ⟨j, u, hu, hproj⟩ := ordinary_amplitude_cover hsource hq (hb.resolve_right ha) ha
    exact ⟨.inl j, u, hu, hproj⟩

set_option maxHeartbeats 800000 in
-- Check differentiability of each of the fourteen cubic coordinates.
set_option linter.flexible false in
private theorem differentiable_amplitude : Differentiable ℝ amplitude := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i <;> simp [amplitude, coordinates] <;> fun_prop

set_option linter.flexible false in
private theorem differentiable_traceZeroCoordinates : Differentiable ℝ traceZeroCoordinates := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i <;> simp [traceZeroCoordinates] <;> fun_prop

set_option maxHeartbeats 1200000 in
-- Elaborate the finite-coordinate polynomial parametrizations of both charts.
set_option linter.flexible false in
private theorem differentiable_boundaryAmplitude (i : BoundaryFamily) :
    Differentiable ℝ (boundaryAmplitude i) := by
  rcases i with j | ⟨flipped, d, j⟩
  · exact differentiable_amplitude.comp (differentiable_traceZeroCoordinates.comp
      (differentiable_patch j (fun u : Fin 3 → ℂ => u) differentiable_id))
  · have hv := differentiable_patch j twoTail (by
      apply differentiable_pi.mpr
      intro k
      exact (ContinuousLinearMap.proj k.succ : (Fin 3 → ℂ) →L[ℝ] ℂ).differentiable)
    have h (k : Fin 3) : Differentiable ℝ (fun u : Fin 3 → ℂ => patch j (twoTail u) k) :=
      differentiable_pi.mp hv k
    have ha : Differentiable ℝ (fun u : Fin 3 → ℂ =>
        shear (u 0) (lift d.val 0 0 (patch j (twoTail u)))) := by
      apply differentiable_pi.mpr
      intro k
      fin_cases k <;> simp [shear, lift] <;> fun_prop
    cases flipped
    · exact ha
    · exact differentiable_pi.mpr fun k => differentiable_pi.mp ha (swappedIndex k)

private theorem differentiable_normalizedGram {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → Fin 14 → ℂ) (hf : Differentiable ℝ f) :
    DifferentiableOn ℝ (fun u => normalizedGram (f u)) {u | f u ≠ 0} := by
  have heval (k : Fin 14) : Differentiable ℝ (fun u => f u k) := differentiable_pi.mp hf k
  have hg (i j : Fin 4) : Differentiable ℝ (fun u => gram (f u) i j) := by
    let entry (k : Fin 16) (u : E) :=
      f u (necklaceTable i k) * conj (f u (necklaceTable j k))
    have hd : Differentiable ℝ (∑ k, entry k) := Differentiable.sum fun k _ =>
      (heval (necklaceTable i k)).mul (Complex.differentiable_conj.comp (heval (necklaceTable j k)))
    have he : (∑ k, entry k) = fun u => gram (f u) i j := by
      funext u
      simp only [← cut_outer, entry, Finset.sum_apply, cut, outer]
    exact he ▸ hd
  have hm : Differentiable ℝ (fun u => (gram (f u)).trace.re) := by
    let diag (i : Fin 4) (u : E) := gram (f u) i i
    have hd : Differentiable ℝ (∑ i, diag i) := Differentiable.sum fun i _ => hg i i
    have he : Complex.reCLM ∘ (∑ i, diag i) = fun u => (gram (f u)).trace.re := by
      funext u
      simp only [Function.comp_apply, Finset.sum_apply, Matrix.trace, Matrix.diag, diag]
      rfl
    exact he ▸ Complex.reCLM.differentiable.comp hd
  intro u hu
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun v =>
    ((gram (f v)).trace.re)⁻¹ • gram (f v) i j) u
  exact (hm.differentiableAt.inv (gram_mass_pos (f u) hu).ne').smul (hg i j).differentiableAt

/-- A finite family of differentiable images of open sets in six real coordinates covers
the observations of all compact lifts outside the first ordinary trace chart. -/
theorem real_boundary_observation_cover :
    ∃ (D : BoundaryFamily → Set (Fin 6 → ℝ))
      (g : BoundaryFamily → (Fin 6 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ),
      (∀ i, IsOpen (D i) ∧ DifferentiableOn ℝ (g i) (D i)) ∧
      observation '' boundary ⊆ ⋃ i, g i '' D i := by
  refine ⟨fun i => {u | boundaryAmplitude i (complexCoordinates u) ≠ 0},
    fun i u => normalizedGram (boundaryAmplitude i (complexCoordinates u)), ?_, ?_⟩
  · intro i
    have hf := (differentiable_boundaryAmplitude i).comp differentiable_complexCoordinates
    exact ⟨isOpen_ne.preimage hf.continuous, differentiable_normalizedGram _ hf⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, u, hu, hproj⟩ := boundary_amplitude_cover hx
    obtain ⟨v, rfl⟩ := complexCoordinates_surjective u
    exact mem_iUnion.mpr ⟨i, v, hu, (observation_of_projector hu hproj).symm⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteBoundaryCover
