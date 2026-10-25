import CFMPOriginalDiagonalFlux235Transient
import CFMPPhysicalStatic237Transient
import CFMPOriginalSixEdgeLengths435Transient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalExteriorMomentArea435Transient
open CFMPPlaneDualConormal435Transient
open CFMPOriginalTriangleBoundary435Transient CFMPOriginalExteriorNativeMoment435Transient
open CFMPOriginalBoundaryEdge229Transient CFMPOriginalDiagonalFlux235Transient
open CFMPOriginalAdjacentConormal233Transient CFMPPairedSupportConormal230Transient
open CFMPPhysicalStatic237Transient

namespace CFMPOriginalPhysicalEdge237Transient

abbrev Space := Fin 4 → ℝ

def sourceCosine (l : Fin 6 → ℝ) (q : Fin 6) : ℝ :=
  rawCos (fun k => Real.cosh (l k)) q

def sourceAngle (l : Fin 6 → ℝ) (q : Fin 6) : ℝ := Real.arccos (sourceCosine l q)

def vertexPerm (q : Fin 6) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective
    (![![0,1,2,3],![0,2,3,1],![0,3,2,1],![2,3,0,1],![1,3,2,0],![1,2,3,0]] q)
    (by fin_cases q <;> decide)

theorem original_relabel_cosine (x : Fin 6 → ℝ) (q : Fin 6) :
    D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
      (relabel x (vertexPerm q) 0) (relabel x (vertexPerm q) 1)
      (relabel x (vertexPerm q) 2) (relabel x (vertexPerm q) 3)
      (relabel x (vertexPerm q) 4) (relabel x (vertexPerm q) 5) = rawCos x q := by
  fin_cases q <;> rfl

theorem physical_normal_labels (M : Matrix (Fin 4) (Fin 4) ℝ) (q : Fin 6) :
    lorentz (unitNormal M false (sideLabels q).1) (unitNormal M false (sideLabels q).2) =
      lorentz (unitNormal M false (vertexPerm q 2)) (unitNormal M false (vertexPerm q 3)) := by
  fin_cases q <;> first | rfl | exact lorentz_symm _ _

theorem actual_physical_cosine (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (q : Fin 6) :
    -lorentz
      (CFMPOriginalExteriorNativeNormal435Transient.unit l M (pairs (physical q)).1.1)
      (CFMPOriginalExteriorNativeNormal435Transient.unit l M (pairs (physical q)).2.1) =
        sourceCosine l q := by
  rw [unit_eq_physical l hl M hM hG, unit_eq_physical l hl M hM hG,
    (physical_supports q).1, (physical_supports q).2]
  change -lorentz (unitNormal M false (sideLabels q).1)
    (unitNormal M false (sideLabels q).2) = _
  rw [physical_normal_labels]
  have h := original_all_unit_side_cosines l hl M hM hG (vertexPerm q)
  simpa only [original_relabel_cosine, sourceCosine] using h

theorem actual_physical_length (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Space, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (q : Fin 6) :
    edgeLength l hl f (pairs (physical q)).1.1 (pairs (physical q)).1.2 = l q := by
  obtain ⟨p,r,hp,hr,hd⟩ :=
    CFMPOriginalSixEdgeLengths435Transient.all_six_original_lengths l hl M hG f hf q
  have hlabels :
      (lengthLabels q).1 = CFMPOriginalSixEdgeLengths435Transient.edgeStart q ∧
      (lengthLabels q).2 = CFMPOriginalSixEdgeLengths435Transient.edgeEnd q := by
    fin_cases q <;> exact ⟨rfl,rfl⟩
  have he := physical_endpoints l q
  rw [hlabels.1, hlabels.2] at he
  cases hs : physicalReversed q with
  | false =>
    simp [hs] at he
    have ha : edgeStart (facePoints l hl (pairs (physical q)).1.1)
        (pairs (physical q)).1.2 = p := by
      apply Subtype.ext
      exact (edgeStart_val l hl _ _).trans (he.1.trans hp.symm)
    have hb : edgeEnd (facePoints l hl (pairs (physical q)).1.1)
        (pairs (physical q)).1.2 = r := by
      apply Subtype.ext
      exact (edgeEnd_val l hl _ _).trans (he.2.trans hr.symm)
    simpa only [edgeLength, ha, hb] using hd
  | true =>
    simp [hs] at he
    have ha : edgeStart (facePoints l hl (pairs (physical q)).1.1)
        (pairs (physical q)).1.2 = r := by
      apply Subtype.ext
      exact (edgeStart_val l hl _ _).trans (he.1.trans hr.symm)
    have hb : edgeEnd (facePoints l hl (pairs (physical q)).1.1)
        (pairs (physical q)).1.2 = p := by
      apply Subtype.ext
      exact (edgeEnd_val l hl _ _).trans (he.2.trans hp.symm)
    simpa only [edgeLength, ha, hb, dist_comm] using hd

-- Positive normalization has squared Lorentz norm one; the remaining cases give zero.
theorem normalized_norm_zero_or_one (X : Space) :
    let N := CFMPConormalIdentification231Transient.normalize X
    lorentz N N = 0 ∨ lorentz N N = 1 := by
  dsimp only
  by_cases hx : 0 < lorentz X X
  · right
    unfold CFMPConormalIdentification231Transient.normalize
    rw [pairing_smul, ← pow_two, inv_pow, Real.sq_sqrt hx.le]
    exact inv_mul_cancel₀ hx.ne'
  · left
    have hs := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hx)
    simpa only [CFMPConormalIdentification231Transient.normalize, hs,
      inv_zero, zero_smul] using
      (show lorentz (0 : Space) 0 = 0 by simp [lorentz])

theorem actual_unit_derivative_orthogonal
    (l : ℝ → Fin 6 → ℝ) (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (dN : Space) (t : ℝ) (n : Fin 20)
    (hN : ∀ i, HasDerivAt
      (fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n i)
      (dN i) t)
    (hu : lorentz
      (CFMPOriginalExteriorNativeNormal435Transient.unit (l t) (M t) n)
      (CFMPOriginalExteriorNativeNormal435Transient.unit (l t) (M t) n) = 1) :
    lorentz dN (CFMPOriginalExteriorNativeNormal435Transient.unit (l t) (M t) n) = 0 := by
  let N := fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n
  have hd := lorentz_hasDerivAt N N dN dN t hN hN
  have hpositive : ∀ᶠ s in 𝓝 t, 0 < lorentz (N s) (N s) :=
    hd.continuousAt.eventually (Ioi_mem_nhds (by simpa only [N, hu] using (zero_lt_one : (0:ℝ)<1)))
  have hunit : (fun s => lorentz (N s) (N s)) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [hpositive] with s hs
    have hz := normalized_norm_zero_or_one
      (CFMPOriginalExteriorNativeNormal435Transient.raw (l s) (M s) n)
    change lorentz (N s) (N s) = 0 ∨ lorentz (N s) (N s) = 1 at hz
    exact hz.resolve_left hs.ne'
  exact unit_derivative_orthogonal N dN t hN hunit

section PhysicalReadout

variable (l : ℝ → Fin 6 → ℝ) (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (dN : Fin 20 → Space) (t : ℝ)
    (hpos : ∀ᶠ s in 𝓝 t, ∀ k, 0 < l s k)
    (hinv : ∀ᶠ s in 𝓝 t, (M s).det ≠ 0)
    (hG : ∀ᶠ s in 𝓝 t, ∀ i j, lorentz (M s i) (M s j) = lengthGram (l s) i j)
    (hN : ∀ n i, HasDerivAt
      (fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) n i)
      (dN n i) t)
    (f : cutBody (l t) → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Space, y = (radial (l t) w.val) ᵥ* M t ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
include hpos hinv hG hN hf

theorem actual_physical_angle_readout (q : Fin 6)
    (hc : -1 < sourceCosine (l t) q ∧ sourceCosine (l t) q < 1) :
    let N := CFMPOriginalExteriorNativeNormal435Transient.unit (l t) (M t) (pairs (physical q)).1.1
    let P := CFMPOriginalExteriorNativeNormal435Transient.unit (l t) (M t) (pairs (physical q)).2.1
    lorentz (dN (pairs (physical q)).1.1) (conormal N P) +
      lorentz (dN (pairs (physical q)).2.1) (conormal P N) =
        deriv (fun s => sourceAngle (l s) q) t := by
  let N := fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) (pairs (physical q)).1.1
  let P := fun s => CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (M s) (pairs (physical q)).2.1
  have hd := lorentz_hasDerivAt N P (dN (pairs (physical q)).1.1)
    (dN (pairs (physical q)).2.1) t (hN _) (hN _)
  have hcos : (fun s => sourceCosine (l s) q) =ᶠ[𝓝 t]
      fun s => -lorentz (N s) (P s) := by
    filter_upwards [hpos, hinv, hG] with s hp hi hg
    exact (actual_physical_cosine (l s) hp (M s) hi hg q).symm
  have hdiff := hd.neg.differentiableAt.congr_of_eventuallyEq hcos
  have hangle : DifferentiableAt ℝ (fun s => sourceAngle (l s) q) t :=
    (Real.differentiableAt_arccos.mpr ⟨hc.1.ne', hc.2.ne⟩).comp t hdiff
  have hstrict : ∀ᶠ s in 𝓝 t,
      -1 < sourceCosine (l s) q ∧ sourceCosine (l s) q < 1 :=
    hdiff.continuousAt.eventually (isOpen_Ioo.mem_nhds hc)
  have hpair : (fun s => lorentz (N s) (P s)) =ᶠ[𝓝 t]
      fun s => -Real.cos (sourceAngle (l s) q) := by
    filter_upwards [hcos, hstrict] with s he hs
    rw [sourceAngle, Real.cos_arccos hs.1.le hs.2.le]
    linarith
  have hunit (n : Fin 20) := CFMPOriginalExteriorNativeNormal435Transient.pair_unit
    (l t) hpos.self_of_nhds (M t) hinv.self_of_nhds hG.self_of_nhds f hf n
  exact paired_angle_readout (N t) (P t) (dN (pairs (physical q)).1.1)
    (dN (pairs (physical q)).2.1) (sourceAngle (l t) q)
    (deriv (fun s => sourceAngle (l s) q) t)
    (actual_unit_derivative_orthogonal l M _ t _ (hN _) (hunit _))
    (actual_unit_derivative_orthogonal l M _ t _ (hN _) (hunit _))
    (Real.arccos_pos.mpr hc.2) (Real.arccos_lt_pi.mpr hc.1) hpair.eq_of_nhds
    (angle_pairing_derivative N P _ _ (fun s => sourceAngle (l s) q) _ t
      (hN _) (hN _) hangle.hasDerivAt hpair)

theorem actual_physical_flux (q : Fin 6)
    (hc : -1 < sourceCosine (l t) q ∧ sourceCosine (l t) q < 1) :
    boundaryFlux (l t) hpos.self_of_nhds (M t) f dN
        (pairs (physical q)).1.1 (pairs (physical q)).1.2 +
      boundaryFlux (l t) hpos.self_of_nhds (M t) f dN
        (pairs (physical q)).2.1 (pairs (physical q)).2.2 =
      l t q * deriv (fun s => sourceAngle (l s) q) t := by
  have hne : facet (pairs (physical q)).1.1 ≠ facet (pairs (physical q)).2.1 := by
    fin_cases q <;> decide
  have hn := original_adjacent_conormals (l t) hpos.self_of_nhds (M t)
    hinv.self_of_nhds hG.self_of_nhds f hf (physical q) hne
  have hd := actual_physical_angle_readout l M dN t hpos hinv hG hN f hf q hc
  have hlen := actual_physical_length (l t) hpos.self_of_nhds (M t)
    hG.self_of_nhds f hf q
  unfold boundaryFlux
  rw [hn.1, hn.2, ← paired_edgeLength (l t) hpos.self_of_nhds f (physical q),
    hlen, ← add_mul, hd, mul_comm]

theorem original_boundary_length_angle_sum
    (hc : ∀ q, -1 < sourceCosine (l t) q ∧ sourceCosine (l t) q < 1) :
    (∑ n : Fin 20, ∑ e : Fin 3,
      boundaryFlux (l t) hpos.self_of_nhds (M t) f dN n e) =
      ∑ q : Fin 6, l t q * deriv (fun s => sourceAngle (l s) q) t := by
  rw [original_boundary_flux_reduce l M dN t hpos hinv hG hN f hf]
  apply Finset.sum_congr rfl
  intro q _
  exact actual_physical_flux l M dN t hpos hinv hG hN f hf q (hc q)

end PhysicalReadout

end CFMPOriginalPhysicalEdge237Transient

run_cmd do
  let name := ``CFMPOriginalPhysicalEdge237Transient.original_boundary_length_angle_sum
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP237 actual original length-angle boundary sum absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP237 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP237 CHECKED {name} axioms={axioms}"
